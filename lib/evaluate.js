import isString from 'iter-tools-es/methods/is-string';
import { effectsFor, reifyExpression, shouldBranch } from '@bablr/agast-vm-helpers';
import {
  buildInitializerTag,
  buildDoctypeTag,
  referenceFlags,
  nodeFlags,
  getFlagsWithGap,
  buildGapTag,
  buildNullTag,
  buildReferenceTag,
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
import { resolveLanguage, unresolveLanguage } from '@bablr/helpers/grammar';
import { isEmpty, StreamGenerator } from '@bablr/agast-helpers/stream';
import {
  getCooked,
  isGapNode,
  isNull,
  isNullNode,
  mergeReferences,
} from '@bablr/agast-helpers/tree';
import * as sumtree from '@bablr/agast-helpers/sumtree';
import {
  ReferenceTag,
  CloseNodeTag,
  NullTag,
  GapTag,
  EmbeddedRegex,
  EmbeddedMatcher,
  OpenNodeTag,
} from '@bablr/agast-vm-helpers/symbols';
import { allTagsFor, TagPath } from '@bablr/agast-helpers/path';
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

const nodeTopType = Symbol.for('@bablr/node');
const defer = Symbol('defer');

export const createParseStrategy = (rootMatcher, rootProps) => {
  return (ctx) => {
    return new StreamGenerator(parseStrategy(ctx, rootMatcher, rootProps));
  };
};

const fragmentMatcher = buildPropertyMatcher(null, buildBasicNodeMatcher(buildFragmentMatcher()));

function* parseStrategy(ctx, rootMatcher, rootValue) {
  const gapsAllowed = !isNull(
    getEmbeddedMatcher(rootMatcher).properties.nodeMatcher.node.properties.open.node.properties
      .flags?.node.properties.hasGapToken,
  );

  let matchReturnValue = undefined;
  let processingReturn = false;
  let processedReturn = false;
  let alreadyAdvanced = false;
  let zombie = false;
  let throwing = false;
  let m;
  let s;
  let co;

  {
    const matcher = reifyExpression(getEmbeddedMatcher(rootMatcher));
    const canonicalURL = matcher.nodeMatcher.language;

    s = yield buildCall('init', canonicalURL);

    m = yield buildCall(
      'startFrame',
      Symbol.for('eat'),
      buildEmbeddedMatcher(fragmentMatcher),
      buildEmbeddedObject({}),
    );

    yield buildCall('advance', buildEmbeddedTag(buildDoctypeTag({ bablrLanguage: canonicalURL })));

    yield buildCall('advance', buildEmbeddedTag(buildOpenNodeTag(getFlagsWithGap(nodeFlags))));

    co = buildCoroutine(ctx, s, m, {
      productionName: reifyExpression(getEmbeddedMatcher(rootMatcher)).nodeMatcher.type,
    });
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

      if (!zombie && s.status === 'rejected') {
        break;
      }

      switch (verb) {
        case 'eat':
        case 'eatMatch':
        case 'match':
        case 'guard':
        case 'holdFor':
        case 'holdForMatch': {
          const effects = effectsFor(verb);
          const isHold = verb === 'holdFor' || verb === 'holdForMatch';

          let { 0: embeddedMatcher, 1: props, 2: embeddedOptions } = args;
          let start;
          let options = getEmbeddedObject(embeddedOptions) || {};

          if (isHold) {
            if (!co.done) throw new Error('hold instructions must be returned from productions');

            if (
              !embeddedMatcher ||
              (embeddedMatcher.type === EmbeddedMatcher &&
                !getCooked(
                  embeddedMatcher.value.properties.nodeMatcher.node.properties.open.node.properties
                    .type.node,
                )) ||
              embeddedMatcher.type === EmbeddedRegex
            ) {
              throw new Error('hold needs a node matcher');
            }
          }

          if (
            isString(embeddedMatcher) ||
            (embeddedMatcher.type === EmbeddedMatcher && isGapNode(embeddedMatcher.value)) ||
            embeddedMatcher.type === EmbeddedRegex
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

            if ((!result && effects.failure === 'fail') || (result && effects.success === 'fail')) {
              throwing = true;
              break instrLoop;
            }

            if (result && effects.success === 'eat') {
              // if (matcher.type === sym.gap) {
              //   const { name, isArray, hasGap } = parsedResolvedPath;

              //   if (isArray) {
              //     yield buildCall(
              //       'advance',
              //       buildEmbeddedTag(
              //         buildReferenceTag(name, true, freeze({ expression: false, hasGap })),
              //       ),
              //     );

              //     yield buildCall('advance', buildEmbeddedTag(buildInitializerTag(true)));
              //   }

              //   yield buildCall(
              //     'advance',
              //     buildEmbeddedTag(buildReferenceTag(name, isArray, hasGap)),
              //   );
              // }

              let depth = 0;
              for (let tag of result.children) {
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
          } else if (embeddedMatcher.type === EmbeddedMatcher) {
            const matcher = reifyExpression(embeddedMatcher.value);
            const { refMatcher, nodeMatcher } = matcher;
            const parsedPath = refMatcher;
            const parsedResolvedPath =
              !parsedPath || parsedPath.name === '.'
                ? parsedPath || { name: '.', isArray: false, index: null, flags: referenceFlags }
                : parsedPath;

            if (isArray(nodeMatcher)) {
              // initializer
              const { name, isArray, flags } = parsedResolvedPath;

              if (nodeMatcher.length) throw new Error();

              if (!isArray && name !== '.') throw new Error();

              if (!s.node.has(name)) {
                let ownReference = buildReferenceTag(name, true, {
                  hasGap: gapsAllowed && flags.hasGap,
                  expression: false,
                });
                yield buildCall(
                  'advance',
                  buildEmbeddedTag(
                    m.isNode ? ownReference : mergeReferences(m.mergedReference, ownReference),
                  ),
                );
                if (effects.success !== 'none') {
                  start = yield buildCall('advance', buildEmbeddedTag(buildInitializerTag(true)));
                }
              }

              returnValue = start;
              break;
            } else if (isNullNode(nodeMatcher)) {
              if (parsedResolvedPath && effects.success === 'eat') {
                const { name, isArray, flags } = parsedResolvedPath;

                if (!s.node.has(name)) {
                  let ownReference = buildReferenceTag(name, isArray, {
                    hasGap: gapsAllowed && flags.hasGap,
                  });
                  yield buildCall(
                    'advance',
                    buildEmbeddedTag(
                      m.isNode ? ownReference : mergeReferences(m.mergedReference, ownReference),
                    ),
                  );
                  if ((effects.success === 'eat' && effects.failure === 'fail') || options.bind) {
                    start = yield buildCall('advance', buildEmbeddedTag(buildNullTag()));
                  } else {
                    start = yield buildCall(
                      'advance',
                      buildEmbeddedTag(buildInitializerTag(ownReference.value.isArray)),
                    );
                  }
                }
              } else {
                start = buildNullTag();
              }

              returnValue = start;
              break;
            } else if (isGapNode(nodeMatcher)) {
              if (parsedResolvedPath && effects.success === 'eat') {
                const { name, isArray, flags } = parsedResolvedPath;

                if (
                  yield buildCall(
                    'match',
                    buildEmbeddedRegex(
                      buildPattern(buildAlternatives([buildRegexGap()]), buildNodeFlags()),
                    ),
                  )
                ) {
                  if (!s.node.has(name)) {
                    let ownReference = buildReferenceTag(name, isArray, {
                      hasGap: gapsAllowed && flags.hasGap,
                    });
                    yield buildCall(
                      'advance',
                      buildEmbeddedTag(
                        m.isNode ? ownReference : mergeReferences(m.mergedReference, ownReference),
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

            let { flags, language: tagLanguage, intrinsicValue, type, attributes } = nodeMatcher;

            const previousPath = s.resultPath;

            // const resolvedLanguage = resolveLanguage(ctx, m.language, tagLanguage);
            const language = resolveLanguage(ctx, m.language, tagLanguage);

            if (tagLanguage && !language) {
              throw new Error(`Unresolvable language ${tagLanguage}`);
            }

            const grammar = ctx.grammars.get(language);
            const isNode = grammar.covers?.get(nodeTopType).has(type) && !options?.suppressNode;
            const isCover = grammar.covers?.has(type);
            const isCoverBoundary = (isNode || isCover) && !m.cover;
            const atGap = (s.source.atGap && refMatcher?.name !== '#') || isHold;
            const shouldInterpolate =
              atGap &&
              (isNode || isCover) &&
              parsedResolvedPath?.flags.hasGap &&
              !options?.suppressGap;

            // if (isHold && !(isNode || isCover)) {
            //   throw new Error('hold must be returned from an @Node or @Cover production');
            // }

            const selfClosing = !!(intrinsicValue && flags.token) || shouldInterpolate;

            let intrinsicResult;

            let shift = null;

            let ownReference = buildReferenceTag(
              parsedResolvedPath.name,
              parsedResolvedPath.isArray,
              parsedResolvedPath.flags,
            );
            let mergedReference = ['#', '@'].includes(ownReference.value.name)
              ? ownReference
              : m.cover
              ? isNode
                ? m.cover.mergedReference
                : buildReferenceTag('.')
              : m.isNode
              ? ownReference
              : mergeReferences(m.mergedReference, ownReference);

            if (intrinsicValue && !shouldInterpolate) {
              intrinsicResult = yield buildCall('match', embeddedMatcher);

              if (
                (!intrinsicResult && effects.failure === 'fail') ||
                (intrinsicResult && effects.success === 'fail')
              ) {
                throwing = true;
              }

              if (mergedReference && mergedReference.value.name !== '.') {
                if (!parsedResolvedPath) {
                  throw new Error(`language failed to specify a path for node of type ${type}`);
                }

                const { name, isArray, flags: innerFlags } = mergedReference.value;

                // this is copy pasta
                if (
                  !intrinsicResult &&
                  effects.success !== 'none' &&
                  s.node &&
                  !m.cover &&
                  !s.node.has(name) &&
                  !(s.resultPath.tag.type === ReferenceTag && s.resultPath.tag.value.name === name)
                ) {
                  if (name !== '#' && name !== '@') {
                    yield buildCall('advance', buildEmbeddedTag(mergedReference));

                    yield buildCall(
                      'advance',
                      buildEmbeddedTag(
                        options.bind ? buildNullTag() : buildInitializerTag(isArray),
                      ),
                    );
                  }
                }
              }

              returnValue = intrinsicResult;
              if (!intrinsicResult) {
                break;
              }
            }

            if (isHold && !m.cover.mergedReference.value.flags.expression) {
              throw new Error('Merged reference must have + for hold');
            }

            // let isCoverBoundary = m.cover

            // advance reference?
            if (
              !isHold &&
              isCoverBoundary &&
              !options?.suppressNode &&
              effects.success === 'eat' &&
              !s.referencePath
            ) {
              const { name, isArray, flags } = mergedReference.value;

              if (isArray && !s.node.has(name)) {
                yield buildCall(
                  'advance',
                  buildEmbeddedTag(
                    buildReferenceTag(name, isArray, { ...flags, expression: false }),
                  ),
                );
                yield buildCall('advance', buildEmbeddedTag(buildInitializerTag(true)));
              }

              yield buildCall('advance', buildEmbeddedTag(mergedReference));
            }

            let heldValue = s.held;

            // advance gap or start tag
            if (shouldInterpolate) {
              if (
                s.held &&
                (isCover
                  ? !grammar.covers.get(type).has(s.held.type.description)
                  : type !== s.held.type.description)
              ) {
                returnValue = null;
                break;
              } else {
                start = buildGapTag();
              }
            } else if (isNode) {
              const language = resolveLanguage(ctx, m.language, tagLanguage);
              const absoluteLanguage = language.canonicalURL;

              // unresolveLanguage(ctx, m.language, resolvedLanguage.canonicalURL);

              const staticAttributes = hasOwn(grammar, 'attributes')
                ? grammar.attributes.get(type) || {}
                : {};

              start = buildOpenNodeTag(
                {
                  ...flags,
                  hasGap: flags.token
                    ? false
                    : !mergedReference
                    ? gapsAllowed
                    : mergedReference.value.name === '@'
                    ? false
                    : mergedReference.value.flags.hasGap || gapsAllowed,
                },
                absoluteLanguage,
                Symbol.for(type),
                // intrinsicValue && flags.intrinsic
                //   ? ctx.agast.sourceTextFor(intrinsicResult)
                //   : undefined,
                { ...staticAttributes, ...attributes },
              );
            }

            const outerOptions = options;
            {
              if (matcher.nodeMatcher.type === '?') throw new Error();

              const unboundAttributes = isNode
                ? hasOwn(grammar, 'unboundAttributes')
                  ? grammar.unboundAttributes.get(type) || []
                  : []
                : null;

              if (parsedResolvedPath.name === '@') {
                unboundAttributes.push('cooked');
              }
              const options = {
                bind: !!outerOptions.bind,
                unboundAttributes,
                suppressNode: !!outerOptions?.suppressNode,
              };

              if (co.done) {
                yield buildCall('endFrame', true);

                m = m.parent;
              }

              m = yield buildCall(
                'startFrame',
                intrinsicValue ? Symbol.for('eat') : Symbol.for(verb),
                buildEmbeddedMatcher(
                  buildPropertyMatcher(
                    buildReferenceMatcher(
                      mergedReference.value.name,
                      mergedReference.value.isArray,
                      buildReferenceFlags(mergedReference.value.flags),
                    ),
                    embeddedMatcher.value.properties.nodeMatcher.node,
                  ),
                ),
                buildEmbeddedObject(options),
              );
              s = m.state;

              if (start) {
                yield buildCall('advance', buildEmbeddedTag(start));
              }
            }

            // how should we continue?
            if (selfClosing) {
              if (!shouldInterpolate) {
                let depth = 0;
                for (const tag of intrinsicResult.children) {
                  if (
                    (tag.type === CloseNodeTag && --depth === 0) ||
                    (tag.type === OpenNodeTag && depth++ === 0)
                  ) {
                    continue;
                  }
                  yield buildCall('advance', buildEmbeddedTag(tag));
                }

                yield buildCall('advance', buildEmbeddedTag(buildCloseNodeTag()));
              }

              const finishedMatch = m;

              yield buildCall('endFrame');

              m = m.parent;

              returnValue = heldValue || finishedMatch.fragment;
            } else if (!shouldInterpolate) {
              co = buildCoroutine(ctx, s, m, props, intrinsicResult);

              let prevTagPath = s.referencePath || previousPath;

              if ([CloseNodeTag, NullTag, GapTag].includes(prevTagPath.tag.type)) {
                prevTagPath = m.path.parent
                  ? TagPath.from(m.path.parent, -1)
                  : TagPath.from(m.path, 0);
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
          const { 0: text, 1: options } = args;
          yield buildCall('write', text, options);
          break;
        }

        case 'openSpan':
        case 'closeSpan': {
          const { 0: name } = args;
          yield buildCall(verb, name);
          break;
        }

        case 'bindAttribute': {
          const { 0: key, 1: value } = args;
          yield buildCall('bindAttribute', key, value);
          break;
        }

        default: {
          throw new Error(`Unknown instruction {type: ${verb}}`);
        }
      }

      if (returnValue === defer) {
        // execution is suspeneded until the state stack unwinds
      } else if (!co.done) {
        co.advance(returnValue);
      }
    } // end instrLoop

    {
      // resume suspended execution
      const { type, isNode, grammar, matcher, captured, effects } = m;
      const allowEmpty = !!grammar.emptyables?.has(type);
      const isThrowing = throwing;
      const finishedMatch = m;

      zombie = !co.done;

      if (zombie) {
        co.finalize();
        alreadyAdvanced = true;
        continue;
      }

      if (co.value) {
        // there is a return value to process
        processingReturn = true;
        alreadyAdvanced = true;

        coroutines.delete(finishedMatch);
        continue;
      }

      if (captured) throw new Error();

      let isEmpty_ = isEmpty(
        allTagsFor(
          isNode
            ? [
                sumtree.getSize(m.innerPath.node.children) ? TagPath.from(m.innerPath, 0) : null,
                null,
              ]
            : m.range,
        ),
      );

      let failing = isThrowing || (!allowEmpty && isEmpty_);
      throwing = !shouldBranch(effects) && failing;

      if ((isNode || finishedMatch.depth === 0) && !failing) {
        yield buildCall('advance', buildEmbeddedTag(buildCloseNodeTag()));
      }

      if (failing || effects.success === 'none') {
        m = yield buildCall('throw', buildEmbeddedObject({ bind: finishedMatch.options.bind }));
      } else {
        m = yield buildCall('endFrame');
      }

      let { range } = finishedMatch;

      if (m) {
        s = m.state;
      }

      if (finishedMatch.depth === 0) {
        if (!throwing && range) {
          const m = finishedMatch;

          if (!m.state.source.done) {
            throw new Error(
              `parse ate ${m.state.source.index} characters but the input was not consumed`,
            );
          }

          return m.fragment;
        } else {
          throw new Error(`parse failed after ${finishedMatch.state.source.index} characters`);
        }
      }

      co = coroutines.get(m);

      // did we attempt to shift
      matchReturnValue = failing
        ? finishedMatch.shiftMatch?.fragment || null
        : finishedMatch.fragment;
      continue;
    }
  }
}
