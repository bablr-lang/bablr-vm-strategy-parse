import { Coroutine } from '@bablr/coroutine';
import { getProduction, normalizeProps } from '@bablr/helpers/grammar';
import { buildCall } from '@bablr/agast-vm-helpers/builders';

const { freeze } = Object;

export const coroutines = new WeakMap();

function* defaultFragment({ props: { rootMatcher } }) {
  yield buildCall('eat', rootMatcher);
}

export const buildCoroutine = (ctx, getState, m, value, literalValue = null) => {
  const { getGrammar, productionEnhancer } = ctx;
  const { propertyMatcher, language, isCover, isCoverBoundary, allowEmpty } = m;
  const { nodeMatcher } = propertyMatcher;
  const { flags, name, type } = nodeMatcher;
  const grammar = getGrammar(language);
  let resolvedName = !name ? language.fragmentProduction : name;

  let production = getProduction(grammar, resolvedName);

  if (!production) {
    if (!m.depth) {
      production = defaultFragment;
    } else {
      throw new Error(`Unknown production {name: ${name}}`);
    }
  }

  const enhancedProduction = productionEnhancer
    ? productionEnhancer(production, resolvedName)
    : production;

  const props = normalizeProps(value);

  // TODO make this more internally consistent
  const args = freeze({
    ctx,
    type,
    name: resolvedName,
    props,
    getState,
    s: getState,
    language,
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
