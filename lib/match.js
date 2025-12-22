import { Coroutine } from '@bablr/coroutine';
import { getProduction, normalizeProps } from '@bablr/helpers/grammar';
import { buildCall } from '@bablr/agast-vm-helpers/builders';

const { freeze } = Object;

export const coroutines = new WeakMap();

function* defaultFragment({ props: { rootMatcher } }) {
  yield buildCall('eat', rootMatcher);
}

export const buildCoroutine = (ctx, getState, m, value, literalValue = null) => {
  const { grammars, productionEnhancer } = ctx;
  const { propertyMatcher, language, isCover, isCoverBoundary, allowEmpty } = m;
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

  const props = normalizeProps(value);

  // TODO make this more internally consistent
  const args = freeze({
    type,
    props,
    getState,
    s: getState,
    flags,
    isCover,
    isCoverBoundary,
    allowEmpty,
    grammar,
    matcher: m.rawPropertyMatcher,
    literalValue,
  });

  const co = new Coroutine(enhancedProduction.call(grammar, args));

  if (!co.generator) {
    throw new Error('Production was not a generator');
  }

  coroutines.set(m, co);

  return co;
};
