import { effectsFor, isShiftVerb, shouldBranch } from '@bablr/agast-vm-helpers';
import {
  buildGapTag,
  buildOpenNodeTag,
  buildAttributeDefinitionTag,
  printTag,
  buildLiteralTag,
  buildReference,
  parseObject,
  parseReferenceFlags,
  parseTagType,
  printReference,
  parseTag,
} from 'agast';
import * as BList from '@bablr/agast-helpers/b-list';
import * as BMap from '@bablr/agast-helpers/b-map';
import { isEmpty, streamFromTree } from '@bablr/agast-helpers/stream';
import { continue_, StreamGenerator, wait, arrayValues } from '@bablr/agast-helpers/iterable';
import { mergeReferences, printSource, referenceFromMatcher } from '@bablr/agast-helpers/tree';
import * as Tags from '@bablr/agast-helpers/tags';
import {
  CloseNodeTag,
  OpenNodeTag,
  GapNode,
  Property,
  TreeNodeMatcher,
  RegexMatcher,
  GapNodeMatcher,
  StringMatcher,
  Node,
  Callable,
  NullNodeMatcher,
} from '@bablr/agast-vm-helpers/symbols';
import { getEmbeddedObject } from '@bablr/agast-vm-helpers/deembed';
import { isArray } from '@bablr/helpers/object';
import {
  buildCall,
  buildCallableTag,
  buildObjectTag,
  buildRegexMatcherTag,
  buildTagTag,
  buildTreeNodeMatcherTag,
  buildOptions,
  buildTreeNodeMatcher,
} from '@bablr/agast-vm-helpers/builders';
import { freezeRecord, isDeepRecord, isObject } from '@bablr/agast-helpers/object';
import { has } from '@bablr/agast-helpers/path';
import { resolveLanguage } from '@bablr/helpers/grammar';
import * as BSet from '@bablr/agast-helpers/b-set';
import { Match } from './match.js';
import { State } from './state.js';

const { hasOwn } = Object;

const defer = Symbol('defer');

export const createParseStrategy = (rootMatcher, rootProps) => {
  if (rootMatcher.type !== Callable) throw new Error();

  return new StreamGenerator(parseStrategy(rootMatcher, rootProps));
};

const refEqualsMatcher = (ref, matcher) => {
  return (
    matcher &&
    ref.name === matcher.name &&
    ref.type === matcher.type &&
    ref.flags.array === matcher.flags.array &&
    ref.flags.intrinsic === matcher.flags.intrinsic &&
    ref.flags.hasGap === matcher.flags.hasGap
  );
};

function* parseStrategy(rootMatcher, rootValue) {
  let matchReturnValue = undefined;
  let processingReturn = false;
  let alreadyAdvanced = false;
  let finishedMatch = null;
  let zombie = false;
  let throwing = false;
  let m;
  let s;
  let co;
  let ctx = yield buildCall('getContext');

  {
    let matcher = rootMatcher.value;

    if (matcher.nodeMatcher.type !== Symbol.for('TreeNodeMatcher')) throw new Error();

    let { flags, type, name, literalValue, attributes } = matcher.nodeMatcher.value;

    s = new State(yield buildCall('getState'));

    if (!flags.token) {
      m = Match.from(
        yield buildCall(
          'call',
          buildCallableTag(
            freezeRecord({
              reference: null,
              bindings: freezeRecord([]),
              nodeMatcher: buildTreeNodeMatcherTag({
                flags,
                type: type || Symbol.for('_'),
                name: null,
                literalValue: null,
                attributes: '{}',
              }),
            }),
          ),
          '     ',
        ),
        s,
      );

      if (type !== Symbol.for('__')) {
        yield buildCall('advance', buildTagTag(printTag(buildOpenNodeTag(flags, type || '_'))));
      }

      let noGapMatcher = buildCallableTag(
        freezeRecord({
          reference: matcher.reference,
          bindings: matcher.bindings,
          nodeMatcher: buildTreeNodeMatcherTag({
            flags,
            type,
            name,
            literalValue,
            attributes,
          }),
        }),
      );

      co = m.buildCoroutine(buildObjectTag({ rootMatcher: noGapMatcher }));
    } else {
      m = Match.from(yield buildCall('call', rootMatcher, '     '), s);
      yield buildCall(
        'advance',
        buildTagTag(printTag(buildOpenNodeTag(matcher.nodeMatcher.flags))),
      );

      co = m.buildCoroutine(rootValue);
    }
  }

  while (co) {
    if (!co.done && !alreadyAdvanced && !throwing) {
      co.advance(matchReturnValue);
    }

    alreadyAdvanced = false;
    matchReturnValue = undefined;

    instrLoop: for (;;) {
      while (co.current === null || co.current instanceof Promise) {
        if (co.current === null) yield continue_(), co.advance();
        if (co.current instanceof Promise) co.current = yield wait(co.current);
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
        case 'hold':
        case 'holdMatch':
        case 'shift':
        case 'shiftMatch': {
          let effects = effectsFor(verb);
          let isShift = ['shift', 'shiftMatch'].includes(verb);
          let isHold = ['holdMatch', 'hold'].includes(verb);

          let { 0: embeddedMatcher, 1: props, 2: embeddedOptions } = args;
          let start;
          let options = getEmbeddedObject(embeddedOptions) || {};

          if (isShift) {
            // if (!co.done) throw new Error('shift instructions must be returned from productions');

            if (
              !embeddedMatcher ||
              embeddedMatcher.type === RegexMatcher ||
              !embeddedMatcher.value.nodeMatcher.value.name
            ) {
              throw new Error('shift needs a node matcher');
            }
          }

          if (
            embeddedMatcher.type === Node ||
            embeddedMatcher.type === GapNodeMatcher ||
            embeddedMatcher.type === StringMatcher ||
            embeddedMatcher.type === RegexMatcher
          ) {
            let result;

            result = yield buildCall('match', embeddedMatcher);

            if ((!result && effects.failure === 'fail') || (result && effects.success === 'fail')) {
              throwing = true;
              break instrLoop;
            }

            if (result && effects.success === 'eat') {
              let depth = 0;
              for (let tag of Tags.traverse(result)) {
                let tagType = parseTagType(tag);
                if (
                  (tagType === CloseNodeTag && --depth === 0) ||
                  (tagType === OpenNodeTag && depth++ === 0)
                ) {
                  continue;
                }
                yield buildCall('advance', buildTagTag(tag));
              }
            }

            returnValue = result;
            break;
          } else if (embeddedMatcher.type === Callable) {
            let matcher = embeddedMatcher.value;
            let { reference, bindings, nodeMatcher } = matcher;

            let resolvedRef = isShift
              ? finishedMatch.mergedReference
              : reference?.value ||
                buildReference(
                  (m.cover || !m.depth) && m.type !== Symbol.for('__') && !m.isNode ? '_' : '.',
                  null,
                  parseReferenceFlags(''),
                );

            if (nodeMatcher.type === NullNodeMatcher) {
              if (resolvedRef && effects.success === 'eat') {
                let { name } = resolvedRef;

                if (!has(name, s.node)) {
                  let ownReference = resolvedRef;
                  if ((effects.success === 'eat' && effects.failure === 'fail') || options.bind) {
                    yield buildCall(
                      'advance',
                      buildTagTag(
                        printReference(
                          m.isNode
                            ? ownReference
                            : mergeReferences(m.mergedReference, ownReference),
                        ),
                      ),
                    );
                    yield buildCall('advance', buildTagTag('null '));
                  }
                }
              }

              returnValue = null;
              break;
            } else if (nodeMatcher.type === GapNodeMatcher) {
              if (resolvedRef && effects.success === 'eat') {
                if (s.held || (yield buildCall('match', buildRegexMatcherTag(`/\\g/`)))) {
                  let ownReference = referenceFromMatcher(resolvedRef);
                  if (!s.held) {
                    yield buildCall(
                      'advance',
                      buildTagTag(
                        printReference(
                          m.isNode
                            ? ownReference
                            : mergeReferences(m.mergedReference, ownReference),
                        ),
                      ),
                    );
                  }
                  start = yield buildCall('advance', buildTagTag('<//>'));
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

            if (nodeMatcher.type !== TreeNodeMatcher) throw new Error();

            let { flags, type, name, attributes } = nodeMatcher.value;

            let languages = s.languages;
            let language = BList.getAt(-1, s.languages);

            for (let bindingTag of arrayValues(bindings)) {
              language = resolveLanguage(languages, bindingTag);

              if (!language) {
                throw new Error(`Unresolvable language ${printTag(bindingTag)}`);
              }
              languages = BList.push(language, languages);
            }

            let grammar = ctx.getGrammar(language);
            let isNode = !type;
            let isCover = type === Symbol.for('_');
            let isLiteral =
              !name || BSet.has(name.description, grammar.literals) || options?.literal;

            let mergedReference = referenceFromMatcher(resolvedRef);

            let canInterpolate =
              (s.source.atGap || (s.heldShift && options.held === 'eat')) &&
              (isNode || isCover) &&
              (mergedReference.flags.hasGap ||
                (!m.isNode && m.getCoveredBoundary().mergedReference.flags.hasGap));

            let shouldInterpolate = canInterpolate && !options?.suppressGap;

            if (co.done) {
              if (s.heldProperty && parseTag(s.heldProperty[0]).value.type !== '#') {
                yield buildCall('eatHeld');
              }

              let finishedMatch = m;
              yield buildCall('return');
              m = finishedMatch.parent;
              s = m.state;
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

            let literalValue = null;
            let failed = false;

            if (isLiteral && !nodeMatcher.value.literalValue) {
              throw new Error('literal production needs a string matcher');
            }

            if (nodeMatcher.value.literalValue) {
              literalValue = yield buildCall('match', nodeMatcher.value.literalValue);

              if (!literalValue && !isLiteral) {
                failed = true;
                if (effects.failure === 'fail') {
                  throwing = true;
                  break;
                }
                if (options.bind) {
                  yield buildCall('advance', buildTagTag(printReference(mergedReference)));
                  yield buildCall('advance', buildTagTag('null '));
                }

                break;
              }
            }

            if (shouldBranch(effects)) {
              yield buildCall('branch');
            }

            if (isShift) {
              yield buildCall('advance', buildTagTag('^^^'));
            }

            let outerOptions = options;
            {
              if (nodeMatcher.type === '?') throw new Error();

              let options = {
                shift: outerOptions.shift ?? true,
                bind: !!outerOptions.bind,
                allowEmpty:
                  outerOptions.allowEmpty ?? BSet.has(name?.description, grammar.emptyables),
                escape: outerOptions.escape ?? false,
                internal: co.done,
              };

              let nodeMatch = m.parent ? m.parent.nodeMatch : m;

              if (!(isShift || shouldInterpolate) && outerOptions.hold) {
                yield buildCall('holdTrivia');
              }

              if (isLiteral) {
                if (!literalValue) {
                  failed = true;
                  if (effects.failure === 'fail') {
                    throwing = true;
                    break;
                  }
                  if (options.bind) {
                    yield buildCall('advance', buildTagTag(printReference(mergedReference)));
                    yield buildCall('advance', buildTagTag('null '));
                  }
                } else {
                  returnValue = { node: literalValue, value: undefined };
                }
              } else if (!shouldInterpolate) {
                let noLiteralNodeMatcher = nodeMatcher;

                if (nodeMatcher.value.literalValue) {
                  let { flags, type, name, literalValue, attributes } = nodeMatcher.value;

                  noLiteralNodeMatcher = buildTreeNodeMatcherTag(
                    buildTreeNodeMatcher(flags, type, name, null, attributes),
                  );
                }

                m = yield* m.call(
                  buildCallableTag(
                    freezeRecord({
                      reference,
                      bindings,
                      nodeMatcher: noLiteralNodeMatcher,
                    }),
                  ),
                  s,
                  buildOptions(options),
                );

                co = null;
              }

              if (s.held && outerOptions.held && !s.heldShift) {
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
                !isShift &&
                !failed &&
                (isNode || isCover) &&
                !(s.depths.path === 0 && m.parent?.nodeMatch.flags.token)
              ) {
                yield buildCall('advance', buildTagTag(printReference(mergedReference)));
              }

              if (nodeMatcher.value.flags.shift && !s.heldShift && !shouldInterpolate) {
                yield buildCall('holdShift');
              }

              // advance gap or start tag
              if (shouldInterpolate) {
                start = buildGapTag();
              } else if (isNode) {
                let staticAttributes =
                  name && hasOwn(grammar, 'attributes')
                    ? BMap.get(name.description, grammar.attributes) || freezeRecord({})
                    : freezeRecord({});

                if (!isDeepRecord(staticAttributes)) throw new Error();

                if (options.escape) {
                  staticAttributes = freezeRecord({ ...staticAttributes, cooked: undefined });
                }

                let cookedLiteral = isLiteral && literalValue ? printSource(literalValue) : null;

                start =
                  !isLiteral || literalValue
                    ? buildOpenNodeTag(
                        freezeRecord({ token: flags.token }),
                        null,
                        name,
                        cookedLiteral ? buildLiteralTag(cookedLiteral) : null,
                        freezeRecord({ ...staticAttributes, ...parseObject(attributes) }),
                        cookedLiteral != null,
                      )
                    : null;
              } else if (isCover) {
                start = buildOpenNodeTag(freezeRecord({ token: false }), type, name);
              }

              if (start) {
                for (let bindingTag of arrayValues(bindings)) {
                  yield buildCall('advance', buildTagTag(printTag(bindingTag)));
                }

                yield buildCall('advance', buildTagTag(printTag(start)));

                if (isLiteral && !start.value?.selfClosing) {
                  if (literalValue) {
                    for (let tag of Tags.traverse(literalValue.value.children)) {
                      if (isObject(tag) && tag.type === Property) {
                        if (tag.value.node.type === GapNode) {
                          yield buildCall('advance', buildTagTag('<//>'));
                        } else {
                          throw new Error();
                        }
                      } else {
                        yield buildCall('advance', buildTagTag(printTag(tag)));
                      }
                    }
                  }
                  if (start.type === OpenNodeTag) {
                    yield buildCall('advance', buildTagTag('</>'));
                  }
                }
              }
            }

            if (isLiteral && literalValue) {
              // yield eatHeld();
            }

            // how should we continue?
            if (shouldInterpolate) {
              let returnNode = s.resultProperty?.[4];
              returnValue = returnNode && freezeRecord({ node: returnNode, value: undefined });
            } else {
              if (!isLiteral) {
                co = m.buildCoroutine(props, literalValue);
                returnValue = defer;
                co.advance(returnValue);
              }
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
            buildTagTag(printTag(buildAttributeDefinitionTag(path, value))),
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
      let { isNode, effects, allowEmpty, options, isCover } = m;
      let isThrowing = throwing;
      finishedMatch = m;
      let finishedCo = co;

      if (finishedCo) {
        zombie = !co.done;

        if (zombie) {
          finishedCo.return();

          while (finishedCo.current === null || finishedCo.current instanceof Promise) {
            if (finishedCo.current === null) yield continue_(), finishedCo.return();
            if (finishedCo.current instanceof Promise)
              finishedCo.current = yield wait(finishedCo.current);
          }

          alreadyAdvanced = true;
          continue;
        }

        if (m.co) {
          if (s.heldProperty && parseTag(s.heldProperty[0]).value.type !== '#') {
            yield buildCall('eatHeld');
          }

          if (
            (isNode || isCover || (m.depth === 0 && m.matcher.type !== Symbol.for('__'))) &&
            !isThrowing
          ) {
            yield buildCall('advance', buildTagTag('</>'));

            if (
              s.heldShift != null &&
              finishedMatch.matcher.flags.shift &&
              !isShiftVerb(finishedMatch.verb)
            ) {
              yield buildCall('advance', buildTagTag('</>'));
            }
          }
        }

        if (finishedMatch.options.shift && finishedCo.value?.shift && m.co) {
          // there is a return value to process
          processingReturn = true;
          alreadyAdvanced = true;

          coroutines.delete(m);
          continue;
        }
      }

      let { getGapNode } = ctx;

      let isEmpty_ =
        !isThrowing && isEmpty(streamFromTree(s.node, { getGapNode, checkBalance: false }));

      // let emptyCover = isCoverBoundary && m.rangeCurrentIndex === m.rangePreviousIndex;
      let emptyCover = false;

      let failing = isThrowing || emptyCover || (!allowEmpty && isEmpty_);
      throwing = failing && !shouldBranch(effects);

      if (failing) {
        yield buildCall('throw');
        m = getThrowMatch();
        rejectState();
        s = m.state;

        if (
          finishedMatch.getShiftMatch() &&
          s.heldProperty &&
          parseTag(s.heldProperty[0]).value.type !== '#'
        ) {
          yield buildCall('eatHeld');
        }
      } else {
        let finishedMatch = m;

        yield buildCall('return');

        m = m.parent;
      }

      s = m.state;

      let node = s.finishedNode;

      if (finishedMatch.depth === 0) {
        if (!throwing && node) {
          return node;
        } else {
          throw new Error(`parse failed after ${finishedMatch.getState().source.index} characters`);
        }
      }

      ({ co } = m);

      if (s.status === 'rejected') {
        co.return();
        while (co.current === null || co.current instanceof Promise) {
          if (co.current === null) yield continue_(), co.return();
          if (co.current instanceof Promise) co.current = yield wait(co.current);
        }
        alreadyAdvanced = true;
        zombie = true;
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
        freezeRecord({
          node: returnNode,
          value:
            finishedCo &&
            (finishedMatch.options.shift ? finishedCo.value?.value : finishedCo.value),
        });
      continue;
    }
  }
}
