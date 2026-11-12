import SYM6.Forms
import SYM.Calculus

/-!
# Grassmann differential calculus in any dimension

`SuperCalc ι R M` is `SYM.SuperCalculus` with the four derivations replaced by derivations
indexed by an arbitrary type `ι`. Nothing else changes: `R` is the commutative ring of even
fields, `M` the module of odd fields, and `pair` the alternating, associative product of two
odd fields.

* `SuperCalc.toDiffRing`: the even part is a `DiffRing`, so forms and `d² = 0` apply;
* `superCalcOfSuperCalculus`: the four-dimensional calculus is the case `ι = Fin 4`.
-/

set_option autoImplicit false
namespace SYM6

/-- A supercommutative differential algebra with commuting derivations indexed by `ι`,
presented by its even part `R` and odd part `M`. -/
class SuperCalc (ι : Type*) (R : outParam (Type*)) (M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] where
  /-- Product of two odd elements. -/
  pair : M →ₗ[R] M →ₗ[R] R
  pair_self : ∀ θ, pair θ θ = 0
  /-- Associativity of the product of three odd elements. -/
  pair_cyclic : ∀ θ η ζ : M, pair θ η • ζ = pair η ζ • θ
  dR : ι → R →+ R
  dM : ι → M →+ M
  dR_mul : ∀ i a b, dR i (a * b) = dR i a * b + a * dR i b
  dM_smul : ∀ i (a : R) (θ : M), dM i (a • θ) = dR i a • θ + a • dM i θ
  dR_pair : ∀ i θ η, dR i (pair θ η) = pair (dM i θ) η + pair θ (dM i η)
  dR_comm : ∀ i j a, dR i (dR j a) = dR j (dR i a)
  dM_comm : ∀ i j θ, dM i (dM j θ) = dM j (dM i θ)
  two_torsion : ∀ a : R, 2 * a = 0 → a = 0
  three_torsion : ∀ a : R, 3 * a = 0 → a = 0

namespace SuperCalc
variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [SuperCalc ι R M]

/-- Two odd elements anticommute. -/
theorem pair_antisymm (θ η : M) : pair ι θ η = -pair ι η θ := by
  have h := pair_self (ι := ι) (θ + η)
  simp only [map_add, LinearMap.add_apply, pair_self, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

/-- `(θ₁ θ₂)(θ₃ θ₄) = (θ₂ θ₃)(θ₁ θ₄)`. -/
theorem pair_mul_pair (a b c d : M) : pair ι a b * pair ι c d = pair ι b c * pair ι a d := by
  have h := congrArg (fun x => pair ι x d) (pair_cyclic (ι := ι) a b c)
  simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul] using h

/-- Exchanging the second and fourth of four odd elements costs a sign. -/
theorem pair_mul_pair_swap (a b c d : M) :
    pair ι a b * pair ι c d = -(pair ι a d * pair ι c b) := by
  rw [pair_mul_pair a b c d, pair_antisymm (ι := ι) b c]; ring

/-- The even part of a Grassmann calculus is a `DiffRing`. -/
@[reducible] def toDiffRing (ι R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [SuperCalc ι R M] : DiffRing ι R where
  d := dR (M := M)
  d_mul := dR_mul
  d_comm := dR_comm
  two_torsion := two_torsion (ι := ι) (M := M)

end SuperCalc

/-- The four-dimensional calculus is the case `ι = Fin 4`. -/
@[reducible] def superCalcOfSuperCalculus (R M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] [SYM.SuperCalculus R M] : SuperCalc (Fin 4) R M where
  pair := SYM.SuperCalculus.pair
  pair_self := SYM.SuperCalculus.pair_self
  pair_cyclic := SYM.SuperCalculus.pair_cyclic
  dR := SYM.SuperCalculus.dR (M := M)
  dM := SYM.SuperCalculus.dM
  dR_mul := SYM.SuperCalculus.dR_mul
  dM_smul := SYM.SuperCalculus.dM_smul
  dR_pair := SYM.SuperCalculus.dR_pair
  dR_comm := SYM.SuperCalculus.dR_comm
  dM_comm := SYM.SuperCalculus.dM_comm
  two_torsion := SYM.SuperCalculus.two_torsion (M := M)
  three_torsion := SYM.SuperCalculus.three_torsion (M := M)

end SYM6
