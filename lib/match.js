import { Coroutine } from '@bablr/coroutine';
import { getProduction, normalizeProps } from '@bablr/helpers/grammar';
import { buildCall } from '@bablr/agast-vm-helpers/builders';
import { stringName } from '@bablr/agast-helpers/path';
import { effectsFor } from '@bablr/agast-vm-helpers';

let { freeze } = Object;

function* defaultFragment({ props: { rootMatcher } }) {
  yield buildCall('eat', rootMatcher);
}

export class Match {
  static from(vm, state, co = null) {
    return new Match(null, vm, 'eat', state, co);
  }

  constructor(parent, vm, verb, state, co) {
    this.parent = parent;
    this.vm = vm;
    this.verb = verb;
    this.state = state;
    this.co = co;
  }

  *call(verb, matcher, s, options) {
    return new Match(this, yield buildCall('call', matcher, options), verb, s);
  }

  *return() {}

  *throw() {}

  buildCoroutine(value, literalValue = null) {
    let { ctx, state, propertyMatcher, language, allowEmpty } = this;
    let { isNode, isCover, isCoverBoundary } = this;
    let { getGrammar, productionEnhancer } = ctx;

    let { nodeMatcher } = propertyMatcher.value;
    let { flags, name, type } = nodeMatcher.value;
    let grammar = getGrammar(language);
    let resolvedName = !name ? Symbol.for(language.fragmentProduction) : name;

    let production = resolvedName && getProduction(grammar, resolvedName);

    if (!production) {
      if (!this.depth) {
        production = defaultFragment;
      } else {
        throw new Error(`Unknown production {name: ${stringName(resolvedName)}}`);
      }
    }

    let enhancedProduction = productionEnhancer
      ? productionEnhancer(production, resolvedName, !resolvedName ? nodeMatcher.type : null)
      : production;

    let props = normalizeProps(value);

    // TODO make this more internally consistent
    let args = freeze({
      ctx,
      type,
      name: resolvedName,
      props,
      m: this.vm,
      s: state.vm,
      state: state.vm,
      language,
      flags,
      isNode,
      isCover,
      isCoverBoundary,
      allowEmpty,
      grammar,
      coverRef: this.coveredBoundary.mergedReference,
      matcher: this.propertyMatcher,
      literalValue,
    });

    let co = new Coroutine(enhancedProduction.call(grammar, args));

    if (!co.generator) {
      throw new Error('Production was not a generator');
    }

    this.co = co;

    return co;
  }

  get effects() {
    return effectsFor(this.verb);
  }

  get ctx() {
    return this.vm.ctx();
  }

  get name() {
    return this.vm.name();
  }

  get type() {
    return this.vm.type();
  }

  get cover() {
    return this.vm.cover();
  }

  get coveredBoundary() {
    return this.vm.coveredBoundary();
  }

  get nodeMatch() {
    return this.vm.nodeMatch();
  }

  get shiftMatch() {
    return this.vm.shiftMatch();
  }

  get node() {
    return this.vm.node();
  }

  get flags() {
    return this.vm.flags();
  }

  get mergedReference() {
    return this.vm.mergedReference();
  }

  get matcher() {
    return this.vm.matcher();
  }

  get propertyMatcher() {
    return this.vm.propertyMatcher();
  }

  get language() {
    return this.vm.language();
  }

  get literalMatcher() {
    return this.vm.literalMatcher();
  }

  get literalValue() {
    return this.vm.literalValue();
  }

  get isNode() {
    return this.vm.isNode();
  }

  get isCover() {
    return this.vm.isCover();
  }

  get isCoverBoundary() {
    return this.vm.isCoverBoundary();
  }

  get options() {
    return this.vm.options();
  }

  get allowEmpty() {
    return this.vm.allowEmpty();
  }

  get depth() {
    return this.vm.depth();
  }
}
