import { Coroutine } from '@bablr/coroutine';
import { getProduction } from '@bablr/helpers/grammar';
import { buildCall, buildEmbeddedNode } from '@bablr/agast-vm-helpers/builders';
import { EmbeddedObject } from '@bablr/agast-vm-helpers/symbols';
import { isPlainObject } from '@bablr/helpers/object';

const { freeze } = Object;

export const coroutines = new WeakMap();

function* defaultFragment({ props: { rootMatcher } }) {
  yield buildCall('eat', rootMatcher);
}

export const buildCoroutine = (ctx, s, m, value, literalValue = null) => {
  const { grammars, productionEnhancer } = ctx;
  const { propertyMatcher, language, isCover, isNode, cover, isCoverBoundary, allowEmpty } = m;
  const { nodeMatcher } = propertyMatcher;
  const { flags, type } = nodeMatcher;
  const grammar = grammars.get(language);
  const resolvedType = type === null ? Symbol.for('@bablr/fragment') : type;

  let production = getProduction(grammar, resolvedType);

  if (!production) {
    if (resolvedType === Symbol.for('@bablr/fragment')) {
      production = defaultFragment;
    } else {
      throw new Error(`Unknown production {type: ${type}}`);
    }
  }

  const enhancedProduction = productionEnhancer ? productionEnhancer(production, type) : production;

  const props =
    isPlainObject(value) && value.type === EmbeddedObject && isPlainObject(value.value)
      ? value.value
      : value === undefined
      ? {}
      : { value: value?.type === EmbeddedObject ? value.value : value };

  const args = freeze({
    type,
    props,
    state: s,
    s,
    flags,
    isCover,
    isCovered: cover && !isNode,
    isCoverBoundary,
    allowEmpty,
    grammar,
    context: ctx,
    ctx,
    mergedReference: m.mergedReference,
    literalValue: literalValue && buildEmbeddedNode(literalValue),
  });

  const co = new Coroutine(enhancedProduction.call(grammar, args));

  if (!co.generator) {
    throw new Error('Production was not a generator');
  }

  coroutines.set(m, co);

  return co;
};
