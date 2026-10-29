import { Coroutine } from '@bablr/coroutine';
import { getProduction, normalizeProps } from '@bablr/helpers/grammar';
import { buildCall } from '@bablr/agast-vm-helpers/builders';
import { stringName } from '@bablr/agast-helpers/path';

let { freeze } = Object;

function* defaultFragment({ props: { rootMatcher } }) {
  yield buildCall('eat', rootMatcher);
}

export class Match {
  static from(vm, co = null) {
    return new Match(null, vm, co);
  }

  constructor(parent, vm, co) {
    this.parent = parent;
    this.vm = vm;
    this.co = co;
  }

  *call(matcher, options) {
    return new Match(this, yield buildCall('call', matcher, options));
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
      s: state,
      state,
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

  get ctx() {
    return this.vm.ctx();
  }

  get state() {
    return this.vm.state();
  }

  get name() {
    return this.vm.name();
  }

  get type() {
    return this.vm.type();
  }

  get verb() {
    return this.vm.verb();
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

  get effects() {
    return;
  }
}
