import { effectsFor, reifyExpression, shouldBranch } from '@bablr/agast-vm-helpers';
import {
  buildGapTag,
  buildNullTag,
  buildOpenNodeTag,
  buildCloseNodeTag,
} from '@bablr/agast-vm-helpers/internal-builders';
import * as BTree from '@bablr/agast-helpers/btree';
import {
  buildPattern,
  buildAlternatives,
  buildRegexGap,
  buildNodeFlags,
  buildPropertyMatcher,
  buildReferenceMatcher,
  buildReferenceFlags,
  buildRegexFlags,
  buildBoundNodeMatcher,
  buildTreeNodeMatcher,
  buildTreeNodeMatcherOpen,
} from '@bablr/helpers/builders';
import { isEmpty, StreamGenerator, wait } from '@bablr/agast-helpers/stream';
import {
  buildAttributeDefinition,
  buildBindingTag,
  buildChild,
  buildFullOpenNodeTag,
  buildShiftTag,
  get,
  getCooked,
  isGapNode,
  isNull,
  mergeReferences,
  referenceFlags,
  referenceFromMatcher,
  streamFromTree,
} from '@bablr/agast-helpers/tree';
import * as Tags from '@bablr/agast-helpers/tags';
import {
  CloseNodeTag,
  Regex,
  Matcher,
  OpenNodeTag,
  ReferenceTag,
  Node,
  GapNode,
  Property,
} from '@bablr/agast-vm-helpers/symbols';
import { getEmbeddedMatcher, getEmbeddedObject } from '@bablr/agast-vm-helpers/deembed';
import { buildCoroutine, coroutines } from './match.js';
import { isArray } from '@bablr/helpers/object';
import {
  buildCall,
  buildEmbeddedMatcher,
  buildEmbeddedObject,
  buildEmbeddedRegex,
  buildEmbeddedTag,
  buildOptions,
} from '@bablr/agast-vm-helpers/builders';
import { freeze } from '@bablr/agast-helpers/object';
import { buildFullPathSegment, getTags, has, list } from '@bablr/agast-helpers/path';
import { printBinding } from '@bablr/agast-helpers/print';
import { resolveLanguage } from '@bablr/helpers/grammar';

const { hasOwn } = Object;

const isString = (val) => typeof val === 'string';

const defer = Symbol('defer');

export const createParseStrategy = (rootMatcher, rootProps) => {
  return (ctx, language, getState) => {
    return new StreamGenerator(parseStrategy(ctx, getState, language, rootMatcher, rootProps));
  };
};

const refEqualsMatcher = (ref, matcher) => {
  return (
    matcher &&
    ref.name === matcher.name &&
    ref.type === matcher.type &&
    ref.flags.array === matcher.flags.array &&
    ref.flags.intrinsic === matcher.flags.intrinsic &&
    ref.flags.hasGap === matcher.flags.hasGap &&
    ref.flags.expression === matcher.flags.expression
  );
};

function* parseStrategy(ctx, getState, rootLanguage, rootMatcher, rootValue) {
  const gapsAllowed = !isNull(
    get(
      ['valueMatcher', 'nodeMatcher', 'open', 'flags', 'hasGapToken'],
      getEmbeddedMatcher(rootMatcher),
    ),
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

    let { flags, type } = matcher.nodeMatcher;

    s = getState();

    if (!flags.token) {
      m = yield buildCall(
        'startFrame',
        Symbol.for('eat'),
        buildEmbeddedMatcher(
          buildPropertyMatcher(
            null,
            buildBoundNodeMatcher(
              [],
              buildTreeNodeMatcher(buildTreeNodeMatcherOpen(buildNodeFlags(flags), type || '_')),
            ),
          ),
        ),
        '    ',
      );

      if (type !== '__') {
        yield buildCall('advance', buildEmbeddedTag(buildFullOpenNodeTag(flags, type || '_')));
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
      m = yield buildCall('startFrame', Symbol.for('eat'), rootMatcher, '    ');
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
        co.current = yield wait(co.current);
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
        case 'shiftMatch':
        case 'eatHeld': {
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
                  get(
                    ['valueMatcher', 'nodeMatcher', 'open', 'name', 'content'],
                    embeddedMatcher.value,
                  ),
                )) ||
              embeddedMatcher.type === Regex
            ) {
              throw new Error('shift needs a node matcher');
            }
          }

          if (
            isString(embeddedMatcher) ||
            (embeddedMatcher.type === Node && embeddedMatcher.value.value.flags.token) ||
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

            if ((!result && effects.failure === 'fail') || (result && effects.success === 'fail')) {
              throwing = true;
              break instrLoop;
            }

            if (result && effects.success === 'eat') {
              let depth = 0;
              for (let tag of Tags.traverse(getTags(result))) {
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
            let embeddedNodeMatcher = get(['valueMatcher', 'nodeMatcher'], embeddedMatcher.value);

            const matcher = reifyExpression(embeddedMatcher.value);
            const { refMatcher, nodeMatcher, bindingMatchers } = matcher;
            const parsedPath = refMatcher;
            const parsedResolvedMatcher = parsedPath || {
              type:
                (m.getCover() || !m.depth) &&
                m.getNode().value.type !== Symbol.for('__') &&
                !m.isNode
                  ? '_'
                  : '.',
              name: null,
              index: null,
              flags: referenceFlags,
            };

            if (embeddedNodeMatcher.value.name === Symbol.for('NullNodeMatcher')) {
              if (parsedResolvedMatcher && effects.success === 'eat') {
                let { name } = parsedResolvedMatcher;

                if (!has(name, s.node)) {
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
            } else if (embeddedNodeMatcher.value.name === Symbol.for('GapNodeMatcher')) {
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

            let { flags, literalValue, type, name, attributes } = nodeMatcher;

            let languages = s.languages;
            let language = BTree.getAt(-1, s.languages);

            for (let bindingMatcher of bindingMatchers) {
              let { segments } = bindingMatcher || { segments: [] };
              language = resolveLanguage(languages, segments);

              if (!language) {
                throw new Error(`Unresolvable language ${printBinding(bindingMatcher)}`);
              }
              languages = BTree.push(languages, language);
            }

            const grammar = ctx.getGrammar(language);
            const isNode = !type;
            const isCover = type === '_';
            const isLiteral = !name || grammar.literals?.has(name) || options?.literal;
            const isCoverBoundary =
              (isNode || isCover) &&
              (isShift ? true : m.getParent() ? m.isNode || !m.getCover() : true);

            let mergedMatcher = parsedResolvedMatcher;

            let mergedReference = referenceFromMatcher(mergedMatcher);

            const shouldInterpolate =
              (s.atGap || (s.held && verb === 'eatHeld')) &&
              !isShift &&
              (!m.getCover()?.didShift || m?.isNode) &&
              (isNode || isCover) &&
              !(
                mergedReference.flags.intrinsic ||
                (!m.isNode && m.getCoveredBoundary().mergedReference.flags.intrinsic)
              ) &&
              (mergedReference.flags.hasGap ||
                (!m.isNode && m.getCoveredBoundary().mergedReference.flags.hasGap)) &&
              !['#', '@'].includes(mergedReference.type) &&
              !options?.suppressGap;

            if (isShift && !(m.isNode || m.isCover)) {
              throw new Error('shift must be returned from a node or cover production');
            }

            let literalResult;

            if (isShift && finishedMatch.getState().status === 'rejected') {
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

              if (
                (!literalResult && effects.failure === 'fail') ||
                (literalResult && effects.success === 'fail')
              ) {
                throwing = true;
              }

              if (mergedReference && mergedReference.name !== '.') {
                if (!parsedResolvedMatcher) {
                  throw new Error(`language failed to specify a path for node of type ${name}`);
                }

                const { type: refType, name } = mergedReference;

                if (
                  !literalResult &&
                  !isShift &&
                  isCoverBoundary &&
                  effects.success === 'eat' &&
                  ((name && !has(name, s.node)) ||
                    (refType === '_' && !has(buildFullPathSegment('_'), s.node)))
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

            if (isShift && m.getCover() && !m.getCover().mergedReference.flags.expression) {
              throw new Error('Merged reference must have + for hold');
            }

            if (co.done) {
              m = yield buildCall('endFrame');
            }

            // if (sreferenceTagPath?.tag.value.name) {
            //   let { type: mType, name: mName } = mergedReference;
            //   let { type: oType, name: oName } = ownReference;
            //   if (
            //     mType !== '.' &&
            //     oType !== '.' &&
            //     ((oType && oType !== mType) || (oName && oName !== mName))
            //   ) {
            //     throw new Error('ref name mismatch');
            //   }
            // }

            const outerOptions = options;
            {
              if (matcher.nodeMatcher.type === '?') throw new Error();

              const options = {
                shift: outerOptions.shift ?? true,
                bind: !!outerOptions.bind,
                allowEmpty: outerOptions.allowEmpty ?? grammar.emptyables?.has(name),
                internal: co.done,
              };

              let reuseMatcher =
                !matcher.refMatcher || refEqualsMatcher(mergedReference, matcher.refMatcher);

              if (!(isLiteral || shouldInterpolate)) {
                m = yield buildCall(
                  isShift ? 'shiftFrame' : 'startFrame',
                  Symbol.for(
                    literalResult && verb !== 'match' ? (isShift ? 'shift' : 'eat') : verb,
                  ),
                  reuseMatcher
                    ? embeddedMatcher
                    : buildEmbeddedMatcher(
                        buildPropertyMatcher(
                          buildReferenceMatcher(
                            mergedMatcher.type,
                            mergedMatcher.name,
                            buildReferenceFlags(mergedMatcher.flags),
                          ),
                          buildBoundNodeMatcher(
                            [...list('bindingMatchers', embeddedMatcher.value)],
                            get(nodeMatcher, embeddedMatcher.value),
                          ),
                        ),
                      ),
                  buildOptions(options),
                );
                s = getState();
              }

              // advance reference?
              if (
                (isNode || isCover) &&
                !(s.depths.path === 0 && m.getParent()?.getNodeMatch().getNode().value.flags.token)
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

              let nodeMatch = m.getParent() ? m.getParent().getNodeMatch() : m;
              let hasGap =
                gapsAllowed &&
                (flags.token || mergedReference?.type === '@'
                  ? false
                  : nodeMatch.getNode().value.flags.hasGap &&
                    !(mergedReference.flags.intrinsic && nodeMatch.getNode().value.flags.token));

              // advance gap or start tag
              if (shouldInterpolate) {
                start = buildGapTag();
              } else if (isNode) {
                let staticAttributes = hasOwn(grammar, 'attributes')
                  ? grammar.attributes.get(name) || {}
                  : {};

                if (parsedResolvedMatcher.type === '@') {
                  staticAttributes = { ...staticAttributes, cooked: undefined };
                }

                let cookedLiteral = isLiteral && literalResult ? getCooked(literalResult) : null;

                start = buildOpenNodeTag(
                  freeze({ token: flags.token, hasGap }),
                  name,
                  cookedLiteral,
                  freeze({ ...staticAttributes, ...attributes }),
                  !!cookedLiteral,
                );
              } else if (isCover) {
                start = buildFullOpenNodeTag(freeze({ token: false, hasGap }), type, name);
              }

              if (start) {
                for (let bindingMatcher of bindingMatchers) {
                  yield buildCall(
                    'advance',
                    buildEmbeddedTag(buildBindingTag(bindingMatcher?.segments)),
                  );
                }

                yield buildCall('advance', buildEmbeddedTag(start));

                if (isLiteral && !start.value?.selfClosing) {
                  if (literalResult) {
                    for (let tag of Tags.traverse(literalResult.value.children)) {
                      if (tag.type === Property) {
                        if (tag.value.node.type === GapNode) {
                          yield buildCall('advance', buildEmbeddedTag(buildGapTag()));
                        } else {
                          throw new Error();
                        }
                      } else {
                        yield buildCall('advance', buildEmbeddedTag(tag));
                      }
                    }
                  }
                  if (start.type === OpenNodeTag) {
                    yield buildCall('advance', buildEmbeddedTag(buildCloseNodeTag()));
                  }
                }
              }
            }

            // how should we continue?
            if (isLiteral || shouldInterpolate) {
              let returnNode = Tags.getAt(-1, m.getNode().value.children).value.node;
              returnValue = returnNode && freeze({ node: returnNode, value: undefined });
            } else if (!shouldInterpolate) {
              co = buildCoroutine(ctx, getState, m, props, literalResult);

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

        case 'startSpan': {
          let { 0: name, 1: guard, 2: props } = args;
          yield buildCall(verb, name, guard, props);
          break;
        }

        case 'endSpan': {
          yield buildCall(verb);
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
        (isNode || isCover || (m.depth === 0 && m.matcher.type !== '__')) &&
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

      let { getGapNode } = ctx;

      let node = m.getNode();

      let isEmpty_ =
        !isThrowing &&
        isEmpty(streamFromTree(finishedMatch.getNode(), { getGapNode, checkBalance: false }));

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

      node = finishedMatch.getNode();

      if (finishedMatch.depth === 0) {
        if (!throwing && node) {
          return node;
        } else {
          throw new Error(`parse failed after ${finishedMatch.state.sourceIndex} characters`);
        }
      }

      co = coroutines.get(m);

      let returnNode = !failing
        ? finishedMatch.getNode()
        : finishedMatch.options.internal &&
          finishedMatch.getShiftMatch() &&
          finishedMatch.isCoverBoundary &&
          finishedMatch.effects.failure === 'none'
        ? finishedMatch.getShiftMatch().getNode()
        : null;

      matchReturnValue =
        returnNode &&
        freeze({
          node: returnNode,
          value: finishedMatch.options.shift ? finishedCo.value?.value : finishedCo.value,
        });
      continue;
    }
  }
}
