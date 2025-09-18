import isString from 'iter-tools-es/methods/is-string';
import { effectsFor, reifyExpression, shouldBranch } from '@bablr/agast-vm-helpers';
import {
  buildInitializerTag,
  referenceFlags,
  buildGapTag,
  buildNullTag,
  buildOpenNodeTag,
  buildCloseNodeTag,
} from '@bablr/agast-vm-helpers/internal-builders';
import {
  buildPattern,
  buildAlternatives,
  buildRegexGap,
  buildNodeFlags,
  buildPropertyMatcher,
  buildBasicNodeMatcher,
  buildFragmentMatcher,
  buildReferenceMatcher,
  buildReferenceFlags,
} from '@bablr/helpers/builders';
import { resolveLanguage } from '@bablr/helpers/grammar';
import { isEmpty, StreamGenerator } from '@bablr/agast-helpers/stream';
import {
  buildAttributeDefinition,
  buildBindingTag,
  buildChild,
  buildReference,
  buildShiftTag,
  fragmentFlags,
  get,
  getCooked,
  getFlagsWithGap,
  isGapNode,
  isNull,
  mergeReferences,
} from '@bablr/agast-helpers/tree';
import * as Tags from '@bablr/agast-helpers/tags';
import {
  CloseNodeTag,
  NullTag,
  GapTag,
  Regex,
  Matcher,
  OpenNodeTag,
  Node,
  ReferenceTag,
} from '@bablr/agast-vm-helpers/symbols';
import { allTagsFor } from '@bablr/agast-helpers/path-facade';
import { getEmbeddedMatcher, getEmbeddedObject } from '@bablr/agast-vm-helpers/deembed';
import { buildCoroutine, coroutines } from './match.js';
import { isArray } from '@bablr/helpers/object';
import {
  buildCall,
  buildEmbeddedMatcher,
  buildEmbeddedObject,
  buildEmbeddedRegex,
  buildEmbeddedTag,
} from '@bablr/agast-vm-helpers/builders';

const { hasOwn } = Object;

const defer = Symbol('defer');

export const createParseStrategy = (rootLanguage, rootMatcher, rootProps) => {
  return (ctx) => {
    return new StreamGenerator(parseStrategy(ctx, rootLanguage, rootMatcher, rootProps));
  };
};

const refEqualsMatcher = (ref, matcher) => {
  return (
    matcher &&
    ref.name === matcher.name &&
    ref.isArray === matcher.isArray &&
    ref.flags.hasGap === matcher.flags.hasGap &&
    ref.flags.expression === matcher.flags.expression
  );
};

function* parseStrategy(ctx, rootURL, rootMatcher, rootValue) {
  const gapsAllowed = !isNull(
    get(['nodeMatcher', 'open', 'flags', 'hasGapToken'], getEmbeddedMatcher(rootMatcher)),
  );

  let matchReturnValue = undefined;
  let processingReturn = false;
  let alreadyAdvanced = false;
  let zombie = false;
  let throwing = false;
  let m;
  let s;
  let co;

  {
    const matcher = reifyExpression(getEmbeddedMatcher(rootMatcher));
    const canonicalURL = rootURL;

    s = yield buildCall('init', canonicalURL);

    if (!matcher.nodeMatcher.flags.token) {
      m = yield buildCall(
        'startFrame',
        Symbol.for('eat'),
        buildEmbeddedMatcher(
          buildPropertyMatcher(
            null,
            null,
            buildBasicNodeMatcher(
              buildFragmentMatcher(
                buildNodeFlags({ ...matcher.nodeMatcher.flags, fragment: true, cover: true }),
              ),
            ),
          ),
        ),
        buildEmbeddedObject({}),
      );

      yield buildCall(
        'advance',
        buildEmbeddedTag(
          buildOpenNodeTag(
            matcher.nodeMatcher.flags.fragment
              ? matcher.nodeMatcher.flags
              : { ...matcher.nodeMatcher.flags, fragment: true, cover: true },
          ),
        ),
      );
      co = buildCoroutine(
        ctx,
        s,
        m,
        buildEmbeddedObject({
          rootMatcher,
        }),
      );
    } else {
      m = yield buildCall('startFrame', Symbol.for('eat'), rootMatcher, buildEmbeddedObject({}));
      yield buildCall('advance', buildEmbeddedTag(buildOpenNodeTag(matcher.nodeMatcher.flags)));

      co = buildCoroutine(ctx, s, m, rootValue);
    }
  }

  while (co) {
    if (!co.done && !alreadyAdvanced && !throwing) {
      co.advance(matchReturnValue);
    }

    alreadyAdvanced = false;
    matchReturnValue = undefined;

    instrLoop: for (;;) {
      if (co.current instanceof Promise) {
        co.current = yield co.current;
      }

      if (co.done && !processingReturn) break;

      processingReturn = false;

      // if (sourceInstr.type !== null) throw new Error();

      const instr = co.value;
      const { verb, arguments: args } = instr;

      let returnValue = undefined;

      if (zombie && verb !== 'write') {
        throw new Error(`zombie production cannot act on {verb: ${verb}}`);
      }

      if (!zombie && (s.status === 'rejected' || throwing)) {
        break;
      }

      switch (verb) {
        case 'eat':
        case 'eatMatch':
        case 'match':
        case 'guard':
        case 'shift':
        case 'shiftMatch': {
          let effects = effectsFor(verb);
          let isShift = verb === 'shift' || verb === 'shiftMatch';
          let didShift = isShift || (m.didShift && !m.isNode);

          let { 0: embeddedMatcher, 1: props, 2: embeddedOptions } = args;
          let start;
          let options = getEmbeddedObject(embeddedOptions) || {};

          if (isShift) {
            if (!co.done) throw new Error('shift instructions must be returned from productions');

            if (
              !embeddedMatcher ||
              (embeddedMatcher.type === Matcher &&
                !getCooked(
                  get(['nodeMatcher', 'open', 'type', 'content'], embeddedMatcher.value),
                )) ||
              embeddedMatcher.type === Regex
            ) {
              throw new Error('shift needs a node matcher');
            }
          }

          if (
            isString(embeddedMatcher) ||
            (embeddedMatcher.type === Node && embeddedMatcher.value.flags.token) ||
            (embeddedMatcher.type === Matcher && isGapNode(embeddedMatcher.value)) ||
            embeddedMatcher.type === Regex
          ) {
            let result;

            result = yield buildCall(
              'match',
              embeddedMatcher === undefined
                ? buildEmbeddedRegex(
                    buildPattern(buildAlternatives([buildRegexGap()]), buildNodeFlags()),
                  )
                : embeddedMatcher,
            );

            if (result) {
              result = result.value;
            }

            if ((!result && effects.failure === 'fail') || (result && effects.success === 'fail')) {
              throwing = true;
              break instrLoop;
            }

            if (result && effects.success === 'eat') {
              let depth = 0;
              for (let tag of Tags.traverse(result.tags)) {
                if (
                  (tag.type === CloseNodeTag && --depth === 0) ||
                  (tag.type === OpenNodeTag && depth++ === 0)
                ) {
                  continue;
                }
                yield buildCall('advance', buildEmbeddedTag(tag));
              }
            }

            returnValue = result;
            break;
          } else if (embeddedMatcher.type === Matcher) {
            const matcher = reifyExpression(embeddedMatcher.value);
            const { refMatcher, nodeMatcher, bindingMatcher } = matcher;
            const parsedPath = refMatcher;
            const parsedResolvedPath =
              !parsedPath || parsedPath.type === '.'
                ? parsedPath || {
                    type: '.',
                    name: null,
                    isArray: false,
                    index: null,
                    flags: referenceFlags,
                  }
                : parsedPath;

            let ownReference = buildReference(
              parsedResolvedPath.type,
              parsedResolvedPath.name,
              parsedResolvedPath.isArray,
              parsedResolvedPath.flags,
            );

            let embeddedNodeMatcher = get('nodeMatcher', embeddedMatcher.value);

            if (embeddedNodeMatcher.type === Symbol.for('ArrayNodeMatcher')) {
              let ref = m.isNode ? ownReference : mergeReferences(m.mergedReference, ownReference);

              let { name, type, isArray, flags } = ref;

              if (flags.hasGap && !s.node.flags.hasGap) {
                flags = getFlagsWithGap(flags, false);
                ref = buildReference(type, name, isArray, flags);
              }

              if (nodeMatcher.length) throw new Error();

              if (!isArray && type !== '.') throw new Error();

              if (name && !s.node.has(name)) {
                yield buildCall('advance', buildEmbeddedTag(buildChild(ReferenceTag, ref)));
                if (effects.success !== 'none') {
                  start = yield buildCall('advance', buildEmbeddedTag(buildInitializerTag(true)));
                }
              }

              returnValue = start;
              break;
            } else if (embeddedNodeMatcher.type === Symbol.for('NullNodeMatcher')) {
              if (parsedResolvedPath && effects.success === 'eat') {
                let { type, name, isArray, flags } = parsedResolvedPath;
                if (flags.hasGap && !s.node.flags.hasGap) {
                  flags = getFlagsWithGap(flags, false);
                }

                if (!s.node.has(name)) {
                  let ownReference = buildReference(type, name, isArray, {
                    ...flags,
                    hasGap: gapsAllowed && flags.hasGap,
                  });
                  yield buildCall(
                    'advance',
                    buildEmbeddedTag(
                      buildChild(
                        ReferenceTag,
                        m.isNode ? ownReference : mergeReferences(m.mergedReference, ownReference),
                      ),
                    ),
                  );
                  if ((effects.success === 'eat' && effects.failure === 'fail') || options.bind) {
                    yield buildCall('advance', buildEmbeddedTag(buildNullTag()));
                  } else {
                    yield buildCall(
                      'advance',
                      buildEmbeddedTag(buildInitializerTag(ownReference.isArray)),
                    );
                  }
                }
              }

              returnValue = null;
              break;
            } else if (embeddedNodeMatcher.type === Symbol.for('GapNodeMatcher')) {
              if (parsedResolvedPath && effects.success === 'eat') {
                let { type, name, isArray, flags } = parsedResolvedPath;

                if (flags.hasGap && !s.node.flags.hasGap) {
                  flags = getFlagsWithGap(flags, false);
                }

                if (
                  yield buildCall(
                    'match',
                    buildEmbeddedRegex(
                      buildPattern(buildAlternatives([buildRegexGap()]), buildNodeFlags()),
                    ),
                  )
                ) {
                  if (!s.node.has(name)) {
                    let ownReference = buildReference(type, name, isArray, {
                      hasGap: gapsAllowed && flags.hasGap,
                    });
                    yield buildCall(
                      'advance',
                      buildEmbeddedTag(
                        buildChild(
                          ReferenceTag,
                          m.isNode
                            ? ownReference
                            : mergeReferences(m.mergedReference, ownReference),
                        ),
                      ),
                    );
                    start = yield buildCall('advance', buildEmbeddedTag(buildGapTag()));
                  }
                }
              } else {
                start = buildGapTag();
              }

              returnValue = start;
              break;
            }

            let { flags, literalValue, type, attributes } = nodeMatcher;
            let { languagePath } = bindingMatcher || { languagePath: [] };

            const previousPath = s.resultPath;

            const language = resolveLanguage(ctx, m.language, languagePath);

            if (languagePath && !language) {
              throw new Error(`Unresolvable language ${languagePath.join('.')}`);
            }

            const grammar = ctx.grammars.get(language);
            const isNode = !flags.fragment;
            const isCover = flags.cover;
            const isLiteral = !type || grammar.literals?.has(type) || options?.literal;
            const isCoverBoundary =
              (isNode || isCover) && (isShift ? true : m.parent ? m.isNode || !m.cover : true);
            const atGap = (s.source.atGap && refMatcher?.type !== '#') || isShift;

            let mergedMatcher = ['#', '@'].includes(ownReference.type)
              ? ownReference
              : m.cover && !m.isNode
              ? isNode
                ? m.cover.mergedReference
                : buildReference('.')
              : m.isNode
              ? ownReference
              : mergeReferences(m.mergedReference, ownReference);

            let mergedReference = buildReference(
              mergedMatcher.type,
              mergedMatcher.name,
              mergedMatcher.isArray,
              {
                ...mergedMatcher.flags,
                hasGap: gapsAllowed && mergedMatcher.flags.hasGap,
              },
            );

            const shouldInterpolate =
              atGap &&
              !isShift &&
              (!m.cover?.didShift || m?.isNode) &&
              (isNode || isCover) &&
              (parsedResolvedPath.flags.hasGap || mergedMatcher.flags.hasGap) &&
              !options?.suppressGap;

            if (flags.fragment && !flags.cover && m.cover && m.path.depth && !isShift)
              throw new Error();

            if (isShift && !(m.isNode || m.isCover)) {
              throw new Error('shift must be returned from an @Node or @Cover production');
            }

            let literalResult;

            if (literalValue && !shouldInterpolate) {
              literalResult = yield buildCall('match', embeddedMatcher);

              if (literalResult) {
                literalResult = literalResult.value;
              }

              if (
                (!literalResult && effects.failure === 'fail') ||
                (literalResult && effects.success === 'fail')
              ) {
                throwing = true;
              }

              if (mergedReference && mergedReference.name !== '.') {
                if (!parsedResolvedPath) {
                  throw new Error(`language failed to specify a path for node of type ${type}`);
                }

                const { type: refType, name, isArray } = mergedReference;

                if (
                  !literalResult &&
                  !isShift &&
                  isCoverBoundary &&
                  effects.success === 'eat' &&
                  !s.referenceTagPath &&
                  ((name && !s.node.has(name)) || (refType === '.' && !s.node.hasRoot()))
                ) {
                  if (name) {
                    yield buildCall(
                      'advance',
                      buildEmbeddedTag(buildChild(ReferenceTag, mergedReference)),
                    );

                    yield buildCall(
                      'advance',
                      buildEmbeddedTag(
                        options.bind ? buildNullTag() : buildInitializerTag(isArray),
                      ),
                    );
                  }
                }
              }

              returnValue = throwing ? null : literalResult;
              if (throwing || !literalResult) {
                break;
              }
            }

            if (isShift && m.cover && !m.cover.mergedReference.flags.expression) {
              throw new Error('Merged reference must have + for hold');
            }

            if (co.done) {
              yield buildCall('endFrame');

              if (shouldBranch(m.effects)) {
                s = yield buildCall('accept');
              }
            }

            // let isCoverBoundary = m.cover

            if (shouldBranch(effects) && (!literalValue || verb === 'match')) {
              s = yield buildCall('branch');
            }

            if (s.referenceTagPath?.tag.value.name) {
              let { type: mType, name: mName } = mergedReference;
              let { type: oType, name: oName } = ownReference;
              if (
                mType !== '.' &&
                oType !== '.' &&
                ((oType && oType !== mType) || (oName && oName !== mName))
              ) {
                throw new Error('ref name mismatch');
              }
            }

            // advance reference?
            if (isCoverBoundary && !s.referenceTagPath && !(m.node.flags.token && !s.depths.path)) {
              let { type, name, isArray, flags } = mergedReference;

              if (flags.hasGap && !s.node.flags.hasGap) {
                flags = getFlagsWithGap(flags, false);
                mergedReference = buildReference(type, name, isArray, flags);
              }

              if (didShift) {
                // let index = s.depths.nodeShift + 1;
                // let height = s.depths.shift === 0 ? 3 : s.depths.shift + 1;

                let shift = buildShiftTag();
                yield buildCall('advance', buildEmbeddedTag(shift));
              } else {
                if (
                  isArray &&
                  ((name && !s.node.has(name)) || (type === '.' && !s.node.hasRoot()))
                ) {
                  yield buildCall(
                    'advance',
                    buildEmbeddedTag(buildChild(ReferenceTag, mergedReference)),
                  );
                  yield buildCall('advance', buildEmbeddedTag(buildInitializerTag(true)));
                }

                yield buildCall(
                  'advance',
                  buildEmbeddedTag(buildChild(ReferenceTag, mergedReference)),
                );
              }
            }

            // advance gap or start tag
            if (shouldInterpolate) {
              if (
                s.held &&
                (isCover
                  ? !grammar.covers.get(type).has(s.held.type.description)
                  : type !== s.held.type.description)
              ) {
                returnValue = null;
                throwing = true;
                break;
              } else {
                start = buildGapTag();
              }
            } else if (isNode) {
              let staticAttributes = hasOwn(grammar, 'attributes')
                ? grammar.attributes.get(type) || {}
                : {};

              if (parsedResolvedPath.type === '@') {
                staticAttributes = { ...staticAttributes, cooked: undefined };
              }

              let cookedLiteral = isLiteral && literalResult ? getCooked(literalResult) : null;

              start = buildOpenNodeTag(
                {
                  ...flags,
                  hasGap:
                    gapsAllowed &&
                    (flags.token
                      ? false
                      : !mergedReference
                      ? true
                      : s.node.flags.hasGap || s.node.flags.token),
                },
                type && Symbol.for(type),
                {
                  ...staticAttributes,
                  ...attributes,
                },
                cookedLiteral,
                !!cookedLiteral,
              );
            } else if (isCoverBoundary) {
              start = buildOpenNodeTag(fragmentFlags);
            }

            const outerOptions = options;
            {
              if (matcher.nodeMatcher.type === '?') throw new Error();

              const options = {
                bind: !!outerOptions.bind,
                allowEmpty: outerOptions.allowEmpty ?? grammar.emptyables?.has(type),
              };

              if (co.done) {
                m = m.parent;
              }

              let reuseMatcher =
                !matcher.refMatcher || refEqualsMatcher(mergedReference, matcher.refMatcher);

              if (!(isLiteral || shouldInterpolate)) {
                m = yield buildCall(
                  'startFrame',
                  literalValue && verb !== 'match'
                    ? isShift
                      ? Symbol.for('shift')
                      : Symbol.for('eat')
                    : Symbol.for(verb),
                  reuseMatcher
                    ? embeddedMatcher
                    : buildEmbeddedMatcher(
                        buildPropertyMatcher(
                          buildReferenceMatcher(
                            mergedMatcher.type,
                            mergedMatcher.name,
                            mergedMatcher.isArray,
                            buildReferenceFlags(mergedMatcher.flags),
                          ),
                          get('bindingMatcher', embeddedMatcher.value),
                          get('nodeMatcher', embeddedMatcher.value),
                        ),
                      ),
                  buildEmbeddedObject(options),
                );
                s = m.state;
              }

              if (start) {
                yield buildCall(
                  'advance',
                  buildEmbeddedTag(buildBindingTag(type ? m.mergedLanguagePath : undefined)),
                );

                yield buildCall('advance', buildEmbeddedTag(start));

                if (isLiteral && !start.value.selfClosing) {
                  for (let tag of Tags.traverse(literalResult.children)) {
                    yield buildCall('advance', buildEmbeddedTag(tag));
                  }
                  yield buildCall('advance', buildEmbeddedTag(buildCloseNodeTag()));
                }
              }
            }

            // how should we continue?
            if (isLiteral || shouldInterpolate) {
              const finishedMatch = m;

              if (
                shouldBranch(effects) &&
                (!matcher.nodeMatcher.literalValue || verb === 'match')
              ) {
                if (verb === 'match') {
                  yield buildCall(
                    'reject',
                    buildEmbeddedObject({ bind: finishedMatch.options.bind }),
                  );
                } else {
                  yield buildCall('accept');
                }
              }

              if (!isLiteral) {
                returnValue = finishedMatch.fragment;
              } else {
                returnValue = s.resultFragment;
              }
            } else if (!shouldInterpolate) {
              co = buildCoroutine(ctx, s, m, props, literalResult);

              let prevTagPath = s.referenceTagPath || previousPath;

              if ([CloseNodeTag, NullTag, GapTag].includes(prevTagPath?.tag.type)) {
                prevTagPath = m.path.parent ? m.path.parent.tagAt(-1) : m.path.tagAt(0);
              }

              co.advance();

              returnValue = defer;
            } else {
              throw new Error('not implemented');
            }
          } else {
            throw new Error();
          }
          break;
        }

        case 'fail': {
          throwing = true;
          break instrLoop;
        }

        case 'write': {
          let { 0: text, 1: options } = args;
          yield buildCall('write', text, options);
          break;
        }

        case 'openSpan':
        case 'closeSpan': {
          let { 0: name } = args;
          yield buildCall(verb, name);
          break;
        }

        case 'defineAttribute': {
          let { 0: path, 1: value } = args;

          if (typeof path === 'string') {
            path = [path];
          }

          if (!isArray(path)) throw new Error();

          yield buildCall('advance', buildEmbeddedTag(buildAttributeDefinition(path, value)));
          break;
        }

        default: {
          throw new Error(`Unknown instruction {type: ${verb}}`);
        }
      }

      if (throwing) break;

      if (returnValue === defer) {
        // execution is suspeneded until the state stack unwinds
      } else if (!co.done) {
        co.advance(returnValue);
      }
    } // end instrLoop

    {
      // resume suspended execution
      const { isNode, effects, allowEmpty, isCoverBoundary } = m;
      const isThrowing = throwing;
      const finishedMatch = m;

      zombie = !co.done;

      if (zombie) {
        co.finalize();
        alreadyAdvanced = true;
        continue;
      }

      if ((isNode || isCoverBoundary || finishedMatch.depth === 0) && !isThrowing) {
        yield buildCall('advance', buildEmbeddedTag(buildCloseNodeTag()));
      }

      if (co.value && coroutines.has(finishedMatch)) {
        // there is a return value to process
        processingReturn = true;
        alreadyAdvanced = true;

        coroutines.delete(finishedMatch);
        continue;
      }

      if (m.captured) throw new Error();

      let isEmpty_ = isEmpty(allTagsFor(isNode ? [m.path.tagPathAt(0), null] : m.range));

      let emptyCover = isCoverBoundary && m.rangeCurrentIndex === m.rangePreviousIndex;

      let failing = isThrowing || emptyCover || (!allowEmpty && isEmpty_);
      throwing = failing && !shouldBranch(effects);

      if (failing) {
        m = yield buildCall('throw');

        if (m && finishedMatch.s.status !== 'rejected' && finishedMatch.s !== m.s) {
          yield buildCall('reject', buildEmbeddedObject({ bind: finishedMatch.options.bind }));
        }
      } else {
        m = yield buildCall('endFrame');

        if (m && finishedMatch.s !== m.s) {
          if (effects.success !== 'none') {
            yield buildCall('accept');
          } else {
            yield buildCall('reject', buildEmbeddedObject({ bind: finishedMatch.options.bind }));
          }
        }
      }

      if (m) {
        s =
          finishedMatch.shiftMatch && (failing || effects.success === 'none')
            ? finishedMatch.shiftMatch.s
            : m.s;
      }

      let { range } = finishedMatch;

      if (finishedMatch.depth === 0) {
        if (!throwing && range) {
          const m = finishedMatch;

          return m.fragment;
        } else {
          throw new Error(`parse failed after ${finishedMatch.state.source.index} characters`);
        }
      }

      co = coroutines.get(m);

      matchReturnValue = failing
        ? finishedMatch.isCoverBoundary
          ? // something is wrong with this line
            // used when we already captured something but just failed to expand on it
            finishedMatch.shiftMatch?.fragment || null
          : null
        : finishedMatch.fragment;
      continue;
    }
  }
}
