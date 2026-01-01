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
  const { flags, name } = nodeMatcher;
  const grammar = grammars.get(language);
  const resolvedType = name === null ? Symbol.for('@bablr/fragment') : name;

  let production = getProduction(grammar, resolvedType);

  if (!production) {
    if (resolvedType === Symbol.for('@bablr/fragment')) {
      production = defaultFragment;
    } else {
      throw new Error(`Unknown production {type: ${name}}`);
    }
  }

  const enhancedProduction = productionEnhancer ? productionEnhancer(production, name) : production;

  const props = normalizeProps(value);

  // TODO make this more internally consistent
  const args = freeze({
    get type() {
      throw new Error('deprecated');
    },
    name,
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
