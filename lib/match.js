import { Coroutine } from '@bablr/coroutine';
import { getProduction, normalizeProps } from '@bablr/helpers/grammar';
import {
  buildCall,
  buildCallableTag,
  buildTreeNodeMatcher,
  buildTreeNodeMatcherTag,
} from '@bablr/agast-vm-helpers/builders';
import { isGapNode, stringName } from '@bablr/agast-helpers/path';
import { effectsFor } from '@bablr/agast-vm-helpers';
import { freezeRecord } from '@bablr/agast-helpers/object';

let { freeze } = Object;

function* defaultFragment({ props: { rootMatcher } }) {
  yield buildCall('eat', rootMatcher);
}

export class Match {
  static *call(parent, state, verb, matcher, options) {
    let { nodeMatcher } = matcher.value;
    let { flags, type, name, literalValue, attributes } = nodeMatcher.value;

    let plainNodeMatcher = buildTreeNodeMatcherTag(
      buildTreeNodeMatcher(flags, type, name, null, attributes),
    );

    let plainMatcher = buildCallableTag(
      freezeRecord({
        reference: null,
        bindings: freezeRecord([]),
        nodeMatcher: plainNodeMatcher,
      }),
    );

    let vm = yield buildCall('call', plainMatcher, options);

    return new Match(parent, state, matcher, vm, verb);
  }

  constructor(parent, state, matcher, vm, verb) {
    this.parent = parent;
    this.state = state;
    this.matcher_ = matcher;
    this.vm = vm;
    this.verb = verb;

    this.externalShift = state.heldShift && isGapNode(state.heldShift);

    this.co = null;
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
      coverRef: this.coveredBoundary.reference,
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
    let m = this;
    let _m = this.vm.coveredBoundary();

    while (m && m !== m) m = m.parent;

    return m;
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

  get reference() {
    return this.vm.reference();
  }

  get matcher() {
    return this.matcher_.value.nodeMatcher.value;
  }

  get propertyMatcher() {
    return this.matcher_;
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
