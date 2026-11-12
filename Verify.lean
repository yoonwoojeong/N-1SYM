import SYM
import SYM6

/-! Axiom audit. The build fails if any of the main theorems depends on anything other than
the three standard axioms (in particular on `sorryAx`). -/

/-- info: 'SYM.Fields.susy_invariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM.Fields.susy_invariance

/-- info: 'SYM.Fields.closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM.Fields.closure

/-- info: 'SYM.bianchi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM.bianchi

/-- info: 'SYM.superYangMills_susy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM.superYangMills_susy

/-- info: 'SYM.superYangMills_closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM.superYangMills_closure

/-- info: 'YM.SYM.fieldStrength_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms YM.SYM.fieldStrength_shift

/-- info: 'YM.SYM.lagrangian_gauge_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms YM.SYM.lagrangian_gauge_invariant

/-- info: 'SYM.TwoGenerators.grassmann' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM.TwoGenerators.grassmann

/-- info: 'SYM.TwoGenerators.oddMul_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM.TwoGenerators.oddMul_ne_zero

/-- info: 'SYM.adjoin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM.adjoin

/-- info: 'SYM.FourGenerators.grassmann' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM.FourGenerators.grassmann

/-- info: 'SYM.FourGenerators.quartic_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM.FourGenerators.quartic_ne_zero

/-- info: 'SYM.IsFirstVariation.unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SYM.IsFirstVariation.unique

/-- info: 'SYM.Fields.isFirstVariation_lagrangian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM.Fields.isFirstVariation_lagrangian

/-- info: 'SYM.Fields.susy_invariance_derived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM.Fields.susy_invariance_derived

/-- info: 'SYM.Fields.isFirstVariation_susy_lam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM.Fields.isFirstVariation_susy_lam

/-- info: 'SYM.Fields.isFirstVariation_susy_D' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM.Fields.isFirstVariation_susy_D

/-- info: 'SYM.Fields.first_variation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM.Fields.first_variation

/-- info: 'SYM.Fields.noether_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM.Fields.noether_identity

/-- info: 'SYM.Fields.supercurrent_conserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM.Fields.supercurrent_conserved

/-- info: 'SYM.Fields.supercurrent_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM.Fields.supercurrent_eq

/-- info: 'SYM6.extD_extD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM6.extD_extD

/-- info: 'SYM6.star_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM6.star_star

/-- info: 'SYM6.pairing3_selfDual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM6.pairing3_selfDual

/-- info: 'SYM6.pairing3_extD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM6.pairing3_extD

/-- info: 'SYM6.div_eq_zero_of_antiSelfDual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM6.div_eq_zero_of_antiSelfDual

/-- info: 'SYM6.dLagNC_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM6.dLagNC_eq

/-- info: 'SYM6.fieldEquation_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM6.fieldEquation_iff

/-- info: 'SYM6.selfDual_of_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM6.selfDual_of_exact

/-- info: 'SYM6.clifford6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM6.clifford6

/-- info: 'SYM6.qI_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SYM6.qI_comm
