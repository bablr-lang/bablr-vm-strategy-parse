import isString from 'iter-tools-es/methods/is-string';
import { effectsFor, reifyExpression, shouldBranch } from '@bablr/agast-vm-helpers';
import {
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
  buildRegexFlags,
} from '@bablr/helpers/builders';
import { isEmpty, printIdentifierPath, StreamGenerator } from '@bablr/agast-helpers/stream';
import {
  buildAttributeDefinition,
  buildBindingTag,
  buildChild,
  buildShiftTag,
  fragmentFlags,
  gapReferenceFlags,
  get,
  getCooked,
  isGapNode,
  isNull,
  mergeReferences,
  referenceFromMatcher,
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
import { freeze } from '@bablr/agast-helpers/object';
import { buildFullPathSegment, getComputedFlags } from '@bablr/agast-helpers/path';
import {
  getProduction,
  normalizeProps,
  resolveLanguage,
  wrapGenerator,
} from '@bablr/helpers/grammar';

const { hasOwn } = Object;

const defer = Symbol('defer');

export const createParseStrategy = (rootLanguage, rootMatcher, rootProps) => {
  return (ctx, getState) => {
    return new StreamGenerator(parseStrategy(ctx, getState, rootLanguage, rootMatcher, rootProps));
  };
};

const refEqualsMatcher = (ref, matcher) => {
  return (
    matcher &&
    ref.name === matcher.name &&
    ref.isArray === matcher.isArray &&
    ref.flags.intrinsic === matcher.flags.intrinsic &&
    ref.flags.expression === matcher.flags.expression
  );
};

function* parseStrategy(ctx, getState, rootURL, rootMatcher, rootValue) {
  const gapsAllowed = !isNull(
    get(['nodeMatcher', 'open', 'flags', 'hasGapToken'], getEmbeddedMatcher(rootMatcher)),
  );

  let matchReturnValue = undefined;
  let processingReturn = false;
  let alreadyAdvanced = false;
  let finishedMatch = null;
  let zombie = false;
  let throwing = false;
  let m;
  let s;
  let co;

  {
    const matcher = reifyExpression(getEmbeddedMatcher(rootMatcher));
    const canonicalURL = rootURL;

    yield buildCall('init', canonicalURL);

    s = getState();

    if (!matcher.nodeMatcher.flags.token) {
      let flags = matcher.nodeMatcher.flags.fragment
        ? matcher.nodeMatcher.flags
        : { ...matcher.nodeMatcher.flags, fragment: true, cover: true };
      m = yield buildCall(
        'startFrame',
        Symbol.for('eat'),
        buildEmbeddedMatcher(
          buildPropertyMatcher(
            null,
            null,
            buildBasicNodeMatcher(buildFragmentMatcher(buildNodeFlags(flags))),
          ),
        ),
        buildEmbeddedObject({}),
      );

      if (!flags.fragment || flags.cover) {
        yield buildCall('advance', buildEmbeddedTag(buildOpenNodeTag(flags)));
      }
      co = buildCoroutine(
        ctx,
        getState,
        m,
        buildEmbeddedObject({
          rootMatcher,
        }),
      );
    } else {
      m = yield buildCall('startFrame', Symbol.for('eat'), rootMatcher, buildEmbeddedObject({}));
      yield buildCall('advance', buildEmbeddedTag(buildOpenNodeTag(matcher.nodeMatcher.flags)));

      co = buildCoroutine(ctx, getState, m, rootValue);
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

      const instr = co.done ? co.value.shift : co.value;
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

          let { 0: embeddedMatcher, 1: props, 2: embeddedOptions } = args;
          let start;
          let options = getEmbeddedObject(embeddedOptions) || {};

          s = getState();

          if (isShift) {
            // if (!co.done) throw new Error('shift instructions must be returned from productions');

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
            const parsedResolvedMatcher = !parsedPath
              ? parsedPath || {
                  type: '.',
                  name: null,
                  isArray: false,
                  index: null,
                  flags: gapReferenceFlags,
                }
              : parsedPath;

            let ownReference = referenceFromMatcher(parsedResolvedMatcher);

            let embeddedNodeMatcher = get('nodeMatcher', embeddedMatcher.value);

            if (embeddedNodeMatcher.type === Symbol.for('NullNodeMatcher')) {
              if (parsedResolvedMatcher && effects.success === 'eat') {
                let { name } = parsedResolvedMatcher;

                if (!s.node.has(name)) {
                  let ownReference = parsedResolvedMatcher;
                  if ((effects.success === 'eat' && effects.failure === 'fail') || options.bind) {
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
                    yield buildCall('advance', buildEmbeddedTag(buildNullTag()));
                  }
                }
              }

              returnValue = null;
              break;
            } else if (embeddedNodeMatcher.type === Symbol.for('GapNodeMatcher')) {
              if (parsedResolvedMatcher && effects.success === 'eat') {
                let { name } = parsedResolvedMatcher;

                let result;
                if (
                  (result = yield buildCall(
                    'match',
                    buildEmbeddedRegex(
                      buildPattern(buildAlternatives([buildRegexGap()]), buildRegexFlags()),
                    ),
                  ))
                ) {
                  if (!s.node.has(name)) {
                    let ownReference = parsedResolvedMatcher;
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

                if (
                  (!result && effects.failure === 'fail') ||
                  (result && effects.success === 'fail')
                ) {
                  throwing = true;
                }
              } else {
                throw new Error('not implemented');
                start = buildGapTag();
              }

              returnValue = start;
              break;
            }

            let { flags, literalValue, type, attributes } = nodeMatcher;
            let { languagePath } = bindingMatcher || { languagePath: [] };

            const previousPath = s.resultPath;

            const language = resolveLanguage(s, languagePath);

            if (languagePath && !language) {
              throw new Error(`Unresolvable language ${printIdentifierPath(languagePath)}`);
            }

            const grammar = ctx.grammars.get(language);
            const isNode = !flags.fragment;
            const isCover = flags.cover;
            const isLiteral = !type || grammar.literals?.has(type) || options?.literal;
            const isCoverBoundary =
              (isNode || isCover) && (isShift ? true : m.parent ? m.isNode || !m.cover : true);
            const atGap = (s.atGap && refMatcher?.type !== '#') || isShift;

            let mergedMatcher = parsedResolvedMatcher;

            let mergedReference = referenceFromMatcher(mergedMatcher);

            const shouldInterpolate =
              (atGap || s.held) &&
              !isShift &&
              (!m.cover?.didShift || m?.isNode) &&
              (isNode || isCover) &&
              !(
                getComputedFlags(mergedReference).intrinsic ||
                getComputedFlags(m.coveredBoundary.mergedReference).intrinsic
              ) &&
              !options?.suppressGap;

            if (isShift && !(m.isNode || m.isCover)) {
              throw new Error('shift must be returned from an @Node or @Cover production');
            }

            let literalResult;

            if (isShift && finishedMatch.s.status === 'rejected') {
              if (
                (!literalResult && effects.failure === 'fail') ||
                (literalResult && effects.success === 'fail')
              ) {
                throwing = true;
              }

              returnValue = null;
              break;
            }

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
                if (!parsedResolvedMatcher) {
                  throw new Error(`language failed to specify a path for node of type ${type}`);
                }

                const { type: refType, name } = mergedReference;

                if (
                  !literalResult &&
                  !isShift &&
                  isCoverBoundary &&
                  effects.success === 'eat' &&
                  !s.referenceTagPath &&
                  ((name && !s.node.has(name)) ||
                    (refType === '.' && !s.node.has(buildFullPathSegment('.'))))
                ) {
                  if (name) {
                    if (options.bind) {
                      yield buildCall(
                        'advance',
                        buildEmbeddedTag(buildChild(ReferenceTag, mergedReference)),
                      );
                      yield buildCall('advance', buildEmbeddedTag(buildNullTag()));
                    }
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
              m = yield buildCall('endFrame');
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

            const outerOptions = options;
            {
              if (matcher.nodeMatcher.type === '?') throw new Error();

              const options = {
                shift: outerOptions.shift ?? true,
                bind: !!outerOptions.bind,
                allowEmpty: outerOptions.allowEmpty ?? grammar.emptyables?.has(type),
                internal: co.done,
              };

              let reuseMatcher =
                !matcher.refMatcher || refEqualsMatcher(mergedReference, matcher.refMatcher);

              if (!(isLiteral || shouldInterpolate)) {
                m = yield buildCall(
                  isShift ? 'shiftFrame' : 'startFrame',
                  Symbol.for(verb),
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
                s = getState();
              }

              // advance reference?
              if (
                (isNode || isCover) &&
                !s.referenceTagPath &&
                !(!s.depths.path && m.parent.nodeMatch.node.flags.token)
              ) {
                if (isShift) {
                  let shift = buildShiftTag();
                  yield buildCall('advance', buildEmbeddedTag(shift));
                } else {
                  yield buildCall(
                    'advance',
                    buildEmbeddedTag(buildChild(ReferenceTag, mergedReference)),
                  );
                }
              }

              let { nodeMatch } = m.parent;
              let hasGap =
                gapsAllowed &&
                (flags.token || mergedReference?.type === '@'
                  ? false
                  : !mergedReference
                  ? true
                  : nodeMatch.node.flags.hasGap || nodeMatch.node.flags.token);

              // advance gap or start tag
              if (shouldInterpolate) {
                start = buildGapTag();
              } else if (isNode) {
                let staticAttributes = hasOwn(grammar, 'attributes')
                  ? grammar.attributes.get(type) || {}
                  : {};

                if (parsedResolvedMatcher.type === '@') {
                  staticAttributes = { ...staticAttributes, cooked: undefined };
                }

                let cookedLiteral = isLiteral && literalResult ? getCooked(literalResult) : null;

                start = buildOpenNodeTag(
                  freeze({ ...flags, hasGap }),
                  type && Symbol.for(type),
                  freeze({ ...staticAttributes, ...attributes }),
                  cookedLiteral,
                  !!cookedLiteral,
                );
              } else if (isCover) {
                start = buildOpenNodeTag(freeze({ ...fragmentFlags, hasGap }));
              }

              if (start) {
                yield buildCall(
                  'advance',
                  buildEmbeddedTag(buildBindingTag(bindingMatcher?.languagePath)),
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
              let returnNode = m.node.tags.at(-1, -1).value.node;
              returnValue = returnNode && freeze({ node: returnNode.node, value: undefined });
            } else if (!shouldInterpolate) {
              co = buildCoroutine(ctx, getState, m, props, literalResult);

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

        case 'exec': {
          let { 0: embeddedMatcher, 1: props } = args;
          let matcher = reifyExpression(embeddedMatcher.value);
          let { nodeMatcher, bindingMatcher } = matcher;
          let { type, flags } = nodeMatcher;
          let resolvedLanguage = resolveLanguage(s, bindingMatcher.languagePath);

          let grammar = ctx.grammars.get(resolvedLanguage);

          let genArgs = freeze({
            type,
            props: normalizeProps(props),
            getState,
            s: getState,
            flags,
            isCover: false,
            isCoverBoundary: false,
            allowEmpty: true,
            grammar,
            matcher: embeddedMatcher.value,
            literalValue: null,
          });

          let production = getProduction(grammar, type);

          let generator = production.call(grammar, genArgs);

          returnValue = wrapGenerator(generator, embeddedMatcher);
          break;
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
      const { isNode, effects, allowEmpty, isCover } = m;
      const isThrowing = throwing;
      finishedMatch = m;
      let finishedCo = co;

      zombie = !co.done;

      if (zombie) {
        finishedCo.finalize();
        alreadyAdvanced = true;
        continue;
      }

      if (
        coroutines.has(m) &&
        (isNode ||
          isCover ||
          (m.depth === 0 && (!m.matcher.flags.fragment || m.matcher.flags.cover))) &&
        !isThrowing
      ) {
        yield buildCall('advance', buildEmbeddedTag(buildCloseNodeTag()));
      }

      if (finishedMatch.options.shift && finishedCo.value?.shift && coroutines.has(m)) {
        // there is a return value to process
        processingReturn = true;
        alreadyAdvanced = true;

        coroutines.delete(m);
        continue;
      }

      let isEmpty_ = m.previousTagPath.nextSibling
        ? isEmpty(allTagsFor([m.previousTagPath.nextSibling, m.path.tagPathAt(-1)]))
        : true;

      // let emptyCover = isCoverBoundary && m.rangeCurrentIndex === m.rangePreviousIndex;
      let emptyCover = false;

      let failing = isThrowing || emptyCover || (!allowEmpty && isEmpty_);
      throwing = failing && !shouldBranch(effects);

      if (failing) {
        m = yield buildCall('throw');
      } else {
        m = yield buildCall('endFrame');
      }

      if (m) {
        s = getState();
      }

      let { node } = finishedMatch;

      if (finishedMatch.depth === 0) {
        if (!throwing && node) {
          return node;
        } else {
          throw new Error(`parse failed after ${finishedMatch.state.source.index} characters`);
        }
      }

      co = coroutines.get(m);

      let returnNode = !failing
        ? finishedMatch.node
        : finishedMatch.options.internal &&
          finishedMatch.shiftMatch &&
          finishedMatch.isCoverBoundary &&
          finishedMatch.effects.failure === 'none'
        ? finishedMatch.shiftMatch.node
        : null;

      matchReturnValue =
        returnNode &&
        freeze({
          node: returnNode.node,
          value: finishedMatch.options.shift ? finishedCo.value?.value : finishedCo.value,
        });
      continue;
    }
  }
}
