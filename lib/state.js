import { buildCall } from '@bablr/agast-vm-helpers/builders';

export class State {
  static from(vm) {
    return new State(null, vm);
  }

  constructor(parent, vm, externalShift) {
    this.parent = parent;
    this.vm = vm;
    this.externalShift = externalShift;

    this.depth = parent ? parent.depth + 1 : 0;
  }

  *branch() {
    let { externalShift } = this;
    let s = yield buildCall('branch');
    return new State(this, s, externalShift);
  }

  *accept() {
    yield buildCall('accept');

    let { parent } = this;

    parent.externalShift = this.externalShift;

    return parent;
  }

  get languages() {
    return this.vm.languages();
  }

  get span() {
    return this.vm.span();
  }

  get spans() {
    return this.vm.spans();
  }

  get depths() {
    return this.vm.depths();
  }

  get returning() {
    return this.vm.returning();
  }

  get heldShift() {
    return this.vm.heldShift();
  }

  get heldTrivia() {
    return this.vm.heldTrivia();
  }

  get node() {
    return this.vm.node();
  }

  get finishedNode() {
    return this.vm.finishedNode();
  }

  get source() {
    return this.vm.source();
  }

  get status() {
    return this.vm.status();
  }
}
