import SYM

/-! Axiom audit of the new theorems. The build fails if any of them depends on anything
other than the three standard axioms (in particular on `sorryAx`). -/

/-- info: 'YM.SYM.fieldStrength_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms YM.SYM.fieldStrength_shift

/-- info: 'YM.SYM.covD_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms YM.SYM.covD_shift

/-- info: 'YM.SYM.hasDerivAt_fieldStrength_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms YM.SYM.hasDerivAt_fieldStrength_shift

/-- info: 'YM.SYM.hasDerivAt_covD_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms YM.SYM.hasDerivAt_covD_shift

/-- info: 'YM.SYM.lagrangian_gauge_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms YM.SYM.lagrangian_gauge_invariant
