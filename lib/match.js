import { Coroutine } from '@bablr/coroutine';
import { getProduction } from '@bablr/helpers/grammar';
import {
  buildBasicNodeMatcher,
  buildPropertyMatcher,
  buildSpamMatcher,
  buildIdentifier,
} from '@bablr/helpers/builders';
import { buildCall, buildEmbeddedMatcher } from '@bablr/agast-vm-helpers/builders';

const { freeze } = Object;

export const coroutines = new WeakMap();

function* defaultFragment({ value: { productionName } }) {
  yield buildCall(
    'eat',
    buildEmbeddedMatcher(
      buildPropertyMatcher(
        null,
        buildBasicNodeMatcher(buildSpamMatcher(buildIdentifier(productionName))),
      ),
    ),
  );
}

export const buildCoroutine = (ctx, s, m, value, intrinsicValue = null) => {
  const { grammars, productionEnhancer } = ctx;
  const { propertyMatcher, language, isCover, cover, isCoverBoundary } = m;
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
  const { attributes } = nodeMatcher;

  const props = freeze({
    type,
    value,
    state: s,
    s,
    flags,
    isCover,
    isCovered: cover && !isCoverBoundary,
    isCoverBoundary,
    grammar,
    context: ctx,
    ctx,
    attributes,
    attrs: attributes,
    intrinsicValue,
  });

  const co = new Coroutine(enhancedProduction.call(grammar, props));

  if (!co.generator) {
    throw new Error('Production was not a generator');
  }

  coroutines.set(m, co);

  return co;
};
