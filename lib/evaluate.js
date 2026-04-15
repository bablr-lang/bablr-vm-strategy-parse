import { effectsFor, reifyExpression, shouldBranch } from '@bablr/agast-vm-helpers';
import { buildGapTag, buildOpenNodeTag } from '@bablr/agast-vm-helpers/internal-builders';
import * as BList from '@bablr/agast-helpers/b-list';
import * as BMap from '@bablr/agast-helpers/b-map';
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
  buildAttributeDefinitionTag,
  buildBindingTag,
  buildChild,
  buildFullOpenNodeTag,
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
  Matcher,
  OpenNodeTag,
  ReferenceTag,
  Node,
  GapNode,
  Property,
  TreeNode,
} from '@bablr/agast-vm-helpers/symbols';
import {
  getEmbeddedMatcher,
  getEmbeddedObject,
  isEmbeddedRegexMatcher,
} from '@bablr/agast-vm-helpers/deembed';
import { buildCoroutine, coroutines } from './match.js';
import { isArray } from '@bablr/helpers/object';
import {
  buildCall,
  buildEmbeddedMatcher,
  buildEmbeddedObject,
  buildEmbeddedTag,
  buildOptions,
} from '@bablr/agast-vm-helpers/builders';
import { freeze, isObject } from '@bablr/agast-helpers/object';
import { getRoot, has, list, TagPath } from '@bablr/agast-helpers/path';
import { printBinding, printTag } from '@bablr/agast-helpers/print';
import { resolveLanguage } from '@bablr/helpers/grammar';
import * as BSet from '@bablr/agast-helpers/b-set';
import { parseTagType } from '@bablr/agast-helpers/builders';

const { hasOwn } = Object;

const defer = Symbol('defer');

export const createParseStrategy = (rootMatcher, rootProps) => {
  return (ctx, getState) => {
    return new StreamGenerator(parseStrategy(ctx, getState, rootMatcher, rootProps));
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

function* parseStrategy(ctx, getState, rootMatcher, rootValue) {
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
        'call',
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
        '      ',
      );

      if (type !== '__') {
        yield buildCall(
          'advance',
          buildEmbeddedTag(printTag(buildFullOpenNodeTag(flags, type || '_'))),
        );
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
      m = yield buildCall('call', Symbol.for('eat'), rootMatcher, '      ');
      yield buildCall(
        'advance',
        buildEmbeddedTag(printTag(buildOpenNodeTag(matcher.nodeMatcher.flags))),
      );

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

      if ((zombie || s.status === 'rejected') && verb !== 'write') {
        throw new Error(`zombie production cannot act on {verb: ${verb}}`);
      }

      if (!zombie && throwing) {
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

          if (embeddedMatcher.type !== Matcher) throw new Error();
          if (embeddedMatcher.value.type !== TreeNode) throw new Error();

          if (isShift) {
            // if (!co.done) throw new Error('shift instructions must be returned from productions');

            if (
              !embeddedMatcher ||
              !getCooked(
                get(
                  ['valueMatcher', 'nodeMatcher', 'open', 'name', 'content'],
                  embeddedMatcher.value,
                ),
              ) ||
              isEmbeddedRegexMatcher(embeddedMatcher)
            ) {
              throw new Error('shift needs a node matcher');
            }
          }

          if (
            embeddedMatcher.value.value.flags.token ||
            isGapNode(embeddedMatcher.value) ||
            getRoot(embeddedMatcher.value).value.name === Symbol.for('String') ||
            isEmbeddedRegexMatcher(embeddedMatcher)
          ) {
            let result;

            result = yield buildCall(
              'match',
              embeddedMatcher === undefined
                ? buildEmbeddedMatcher(
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
              for (let tag of Tags.traverse(Tags.getTags(result))) {
                let tagType = parseTagType(tag);
                if (
                  (tagType === CloseNodeTag && --depth === 0) ||
                  (tagType === OpenNodeTag && depth++ === 0)
                ) {
                  continue;
                }
                yield buildCall('advance', buildEmbeddedTag(printTag(tag)));
              }
            }

            returnValue = result;
            break;
          } else if (embeddedMatcher.type === Matcher) {
            let embeddedMatcher_ = getRoot(embeddedMatcher.value);
            let embeddedNodeMatcher = get(['valueMatcher', 'nodeMatcher'], embeddedMatcher_);

            const matcher = reifyExpression(embeddedMatcher_);
            const { refMatcher, nodeMatcher, bindingMatchers } = matcher;

            const resolvedRefMatcher = refMatcher || {
              type:
                (m.getCover() || !m.depth) && m.type !== Symbol.for('__') && !m.isNode ? '_' : '.',
              name: null,
              index: null,
              flags: referenceFlags,
            };

            if (embeddedNodeMatcher.value.name === Symbol.for('NullNodeMatcher')) {
              if (resolvedRefMatcher && effects.success === 'eat') {
                let { name } = resolvedRefMatcher;

                if (!has(name, s.getNode())) {
                  let ownReference = resolvedRefMatcher;
                  if ((effects.success === 'eat' && effects.failure === 'fail') || options.bind) {
                    yield buildCall(
                      'advance',
                      buildEmbeddedTag(
                        printTag(
                          buildChild(
                            ReferenceTag,
                            m.isNode
                              ? ownReference
                              : mergeReferences(m.mergedReference, ownReference),
                          ),
                        ),
                      ),
                    );
                    yield buildCall('advance', buildEmbeddedTag('null'));
                  }
                }
              }

              returnValue = null;
              break;
            } else if (embeddedNodeMatcher.value.name === Symbol.for('GapNodeMatcher')) {
              if (resolvedRefMatcher && effects.success === 'eat') {
                if (
                  s.held ||
                  (yield buildCall(
                    'match',
                    buildEmbeddedMatcher(
                      buildPattern(buildAlternatives([buildRegexGap()]), buildRegexFlags()),
                    ),
                  ))
                ) {
                  let ownReference = referenceFromMatcher(resolvedRefMatcher);
                  if (!s.held) {
                    yield buildCall(
                      'advance',
                      buildEmbeddedTag(
                        printTag(
                          buildChild(
                            ReferenceTag,
                            m.isNode
                              ? ownReference
                              : mergeReferences(m.mergedReference, ownReference),
                          ),
                        ),
                      ),
                    );
                  }
                  start = yield buildCall('advance', buildEmbeddedTag('<//>'));
                }

                if (
                  (!start && effects.failure === 'fail') ||
                  (start && effects.success === 'fail')
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

            let { flags, type, name, attributes } = nodeMatcher;

            let languages = s.languages;
            let language = BList.getAt(-1, s.languages);

            for (let bindingMatcher of bindingMatchers) {
              let { segments } = bindingMatcher || { segments: [] };
              language = resolveLanguage(languages, segments);

              if (!language) {
                throw new Error(`Unresolvable language ${printBinding(bindingMatcher)}`);
              }
              languages = BList.push(language, languages);
            }

            const grammar = ctx.getGrammar(language);
            const isNode = !type;
            const isCover = type === '_';
            const isLiteral = !name || BSet.has(name, grammar.literals) || options?.literal;

            let mergedReference = referenceFromMatcher(resolvedRefMatcher);

            const canInterpolate =
              (s.source.atGap || (s.shifted && options.held === 'eat')) &&
              (isNode || isCover) &&
              (mergedReference.flags.hasGap ||
                (!m.isNode && m.getCoveredBoundary().mergedReference.flags.hasGap));

            const shouldInterpolate = canInterpolate && !options?.suppressGap;

            if (isShift && !(m.isNode || m.isCover)) {
              throw new Error('shift must be returned from a node or cover production');
            }

            if (isShift && m.getCover() && !m.getCover().mergedReference.flags.expression) {
              throw new Error('Merged reference must have + for hold');
            }

            if (co.done) {
              let finishedMatch = m;
              m = yield buildCall('return');

              s = getState();

              if (finishedMatch.isNode && !finishedMatch.options.hold) {
                yield buildCall('eatHeld');
              }
            }

            // if (sreferenceTagPath?.value.name) {
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
                literal: isLiteral,
                shift: outerOptions.shift ?? true,
                bind: !!outerOptions.bind,
                allowEmpty: outerOptions.allowEmpty ?? BSet.has(name, grammar.emptyables),
                internal: co.done,
                hold: outerOptions.hold ?? false,
              };

              let reuseMatcher =
                !matcher.refMatcher || refEqualsMatcher(mergedReference, matcher.refMatcher);

              if (!shouldInterpolate) {
                m = yield buildCall(
                  'call',
                  Symbol.for(verb),
                  reuseMatcher
                    ? embeddedMatcher
                    : buildEmbeddedMatcher(
                        buildPropertyMatcher(
                          buildReferenceMatcher(
                            resolvedRefMatcher.type,
                            resolvedRefMatcher.name,
                            buildReferenceFlags(resolvedRefMatcher.flags),
                          ),
                          buildBoundNodeMatcher(
                            [...list('bindingMatchers', embeddedMatcher.value)],
                            get(nodeMatcher, embeddedMatcher.value),
                          ),
                        ),
                      ),
                  buildOptions(options),
                );
                co = null;

                s = getState();

                if (s.status === 'rejected') {
                  throwing = true;
                  break;
                } else if (m.literalMatcher && !m.literalValue) {
                  returnValue = defer;
                  break;
                }
              }

              if (s.held && outerOptions.held && !s.shifted) {
                switch (outerOptions.held) {
                  case 'eat':
                    yield buildCall('eatHeld');
                    break;
                  case 'drop':
                    yield buildCall('dropHeld');
                    break;
                  case 'return':
                    yield buildCall('returnHeld');
                    break;
                  default:
                    throw new Error();
                }
              }

              // advance reference?
              if (
                (isNode || isCover) &&
                !(s.depths.path === 0 && m.getParent()?.getNodeMatch().flags.token)
              ) {
                if (isShift) {
                  yield buildCall('advance', buildEmbeddedTag('^^^'));
                } else {
                  yield buildCall(
                    'advance',
                    buildEmbeddedTag(printTag(buildChild(ReferenceTag, mergedReference))),
                  );
                }
              }

              let nodeMatch = m.getParent() ? m.getParent().getNodeMatch() : m;
              let hasGap =
                gapsAllowed &&
                (flags.token || mergedReference?.type === '@'
                  ? false
                  : nodeMatch.flags.hasGap &&
                    !(mergedReference.flags.intrinsic && nodeMatch.flags.token));

              // advance gap or start tag
              if (shouldInterpolate) {
                start = buildGapTag();
              } else if (isNode) {
                let staticAttributes = hasOwn(grammar, 'attributes')
                  ? BMap.get(name, grammar.attributes) || {}
                  : {};

                if (resolvedRefMatcher.type === '@') {
                  staticAttributes = { ...staticAttributes, cooked: undefined };
                }

                let cookedLiteral = isLiteral && m.literalValue ? getCooked(m.literalValue) : null;

                start = buildOpenNodeTag(
                  freeze({ token: flags.token, hasGap }),
                  name,
                  cookedLiteral,
                  freeze({ ...staticAttributes, ...attributes }),
                  cookedLiteral != null,
                );
              } else if (isCover) {
                start = buildFullOpenNodeTag(freeze({ token: false, hasGap }), type, name);
              }

              if (start) {
                for (let bindingMatcher of bindingMatchers) {
                  yield buildCall(
                    'advance',
                    buildEmbeddedTag(printTag(buildBindingTag(bindingMatcher?.segments))),
                  );
                }

                yield buildCall('advance', buildEmbeddedTag(printTag(start)));

                if (isLiteral && !start.value?.selfClosing) {
                  if (m.literalValue) {
                    for (let tag of Tags.traverse(m.literalValue.value.children)) {
                      if (isObject(tag) && tag.type === Property) {
                        if (tag.value.node.type === GapNode) {
                          yield buildCall('advance', buildEmbeddedTag('<//>'));
                        } else {
                          throw new Error();
                        }
                      } else {
                        yield buildCall('advance', buildEmbeddedTag(printTag(tag)));
                      }
                    }
                  }
                  if (start.type === OpenNodeTag) {
                    yield buildCall('advance', buildEmbeddedTag('</>'));
                  }
                }
              }
            }

            s = getState();

            // how should we continue?
            if (shouldInterpolate) {
              let returnNode = TagPath.wrap(s.resultPath).inner?.node;
              returnValue = returnNode && freeze({ node: returnNode, value: undefined });
            } else {
              if (!isLiteral) {
                // TODO m.literalValue
                co = buildCoroutine(ctx, getState, m, props, m.literalValue);
                co.advance();
              }

              returnValue = defer;
            }
          } else {
            throw new Error();
          }
          break;
        }

        case 'eatHeld': {
          yield buildCall('eatHeld');
          break;
        }

        case 'pinHeld': {
          yield buildCall('pinHeld');
          break;
        }

        case 'dropHeld': {
          yield buildCall('dropHeld');
          break;
        }

        case 'returnHeld': {
          yield buildCall('returnHeld');
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
          let { 0: name, 1: guard, 2: merge, 3: props } = args;
          yield buildCall(verb, name, guard, merge, props);
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

          yield buildCall(
            'advance',
            buildEmbeddedTag(printTag(buildAttributeDefinitionTag(path, value))),
          );
          break;
        }

        default: {
          throw new Error(`Unknown instruction {type: ${verb}}`);
        }
      }

      if (throwing || !co) break;

      if (returnValue === defer) {
        // execution is suspeneded until the state stack unwinds
      } else if (!co.done) {
        co.advance(returnValue);
      }
    } // end instrLoop

    {
      // resume suspended execution
      const { isNode, effects, allowEmpty, options, isCover, literalMatcher, literalValue } = m;
      const isThrowing = throwing;
      finishedMatch = m;
      let finishedCo = co;

      if (finishedCo) {
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
          yield buildCall('advance', buildEmbeddedTag(printTag('</>')));
        }

        if (finishedMatch.options.shift && finishedCo.value?.shift && coroutines.has(m)) {
          // there is a return value to process
          processingReturn = true;
          alreadyAdvanced = true;

          coroutines.delete(m);
          continue;
        }
      }

      let { getGapNode } = ctx;

      let isEmpty_ =
        !isThrowing &&
        isEmpty(streamFromTree(finishedMatch.getNode(), { getGapNode, checkBalance: false }));

      // let emptyCover = isCoverBoundary && m.rangeCurrentIndex === m.rangePreviousIndex;
      let emptyCover = false;

      let failing =
        isThrowing || emptyCover || (!allowEmpty && isEmpty_) || (literalMatcher && !literalValue);
      throwing = failing && !shouldBranch(effects);

      if (failing) {
        m = yield buildCall('throw');
      } else {
        let finishedMatch = m;
        m = yield buildCall('return');

        if (isNode && !options.hold && finishedMatch.effects.success === 'eat') {
          yield buildCall('eatHeld');
        }
      }

      if (m) {
        s = getState();
      }

      let node = finishedMatch.getNode();

      if (finishedMatch.depth === 0) {
        if (!throwing && node) {
          return node;
        } else {
          throw new Error(`parse failed after ${finishedMatch.getState().source.index} characters`);
        }
      }

      co = coroutines.get(m);

      if (s.status === 'rejected') {
        co.finalize();
        alreadyAdvanced = true;
        continue;
      }

      let returnNode = !failing
        ? node
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
          value:
            finishedCo &&
            (finishedMatch.options.shift ? finishedCo.value?.value : finishedCo.value),
        });
      continue;
    }
  }
}
