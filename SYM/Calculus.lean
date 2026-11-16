import Mathlib

/-!
# Grassmann differential calculus

The algebraic setting in which classical supersymmetric field theory is formulated.

A `SuperCalculus R M` consists of

* a commutative ring `R` of *even* (bosonic) fields,
* an `R`-module `M` of *odd* (fermionic) fields,
* the product `pair : M → M → R` of two odd fields, which is alternating and associative
  (`pair θ η • ζ = pair η ζ • θ`, both sides being `θ η ζ`),
* four commuting derivations `dR μ`, `dM μ` obeying the Leibniz rule for every product.

Together `R ⊕ M` is a supercommutative `ℤ/2`-graded differential algebra. Keeping the two
parities in separate types makes every sign rule a theorem about `pair` instead of a side
condition, and lets `ring` work on bosonic expressions.

The model to keep in mind: smooth functions on spacetime with values in the even and odd
parts of a Grassmann algebra (`SYM/Model.lean`).
-/

set_option autoImplicit false
namespace SYM

/-- A supercommutative differential algebra with four commuting derivations, presented by its
even part `R` and odd part `M`. -/
class SuperCalculus (R : outParam (Type*)) (M : Type*) [CommRing R] [AddCommGroup M] [Module R M] where
  /-- Product of two odd elements. -/
  pair : M →ₗ[R] M →ₗ[R] R
  pair_self : ∀ θ, pair θ θ = 0
  /-- Associativity of the product of three odd elements. -/
  pair_cyclic : ∀ θ η ζ : M, pair θ η • ζ = pair η ζ • θ
  /-- Coordinate derivatives of even fields. -/
  dR : Fin 4 → R →+ R
  /-- Coordinate derivatives of odd fields. -/
  dM : Fin 4 → M →+ M
  dR_mul : ∀ μ a b, dR μ (a * b) = dR μ a * b + a * dR μ b
  dM_smul : ∀ μ (a : R) (θ : M), dM μ (a • θ) = dR μ a • θ + a • dM μ θ
  dR_pair : ∀ μ θ η, dR μ (pair θ η) = pair (dM μ θ) η + pair θ (dM μ η)
  dR_comm : ∀ μ ν a, dR μ (dR ν a) = dR ν (dR μ a)
  dM_comm : ∀ μ ν θ, dM μ (dM ν θ) = dM ν (dM μ θ)
  /-- `R` has no 2-torsion (true whenever `R` contains `ℚ`). -/
  two_torsion : ∀ a : R, 2 * a = 0 → a = 0
  /-- `R` has no 3-torsion. -/
  three_torsion : ∀ a : R, 3 * a = 0 → a = 0

namespace SuperCalculus
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [SuperCalculus R M]

theorem pair_antisymm (θ η : M) : pair (R := R) θ η = -pair η θ := by
  have h := pair_self (R := R) (θ + η)
  simp only [map_add, LinearMap.add_apply, pair_self, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

/-- `θ η ζ = ζ θ η`. -/
theorem pair_cyclic' (θ η ζ : M) : pair (R := R) θ η • ζ = pair (R := R) ζ θ • η := by
  rw [pair_cyclic, pair_cyclic]

/-- `(θ₁ θ₂)(θ₃ θ₄) = (θ₂ θ₃)(θ₁ θ₄)`. -/
theorem pair_mul_pair (a b c d : M) :
    pair (R := R) a b * pair (R := R) c d = pair (R := R) b c * pair (R := R) a d := by
  have h := congrArg (fun x => pair (R := R) x d) (pair_cyclic (R := R) a b c)
  simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul] using h

/-- Exchanging the second and fourth of four odd elements costs a sign. -/
theorem pair_mul_pair_swap (a b c d : M) :
    pair (R := R) a b * pair (R := R) c d = -(pair (R := R) a d * pair (R := R) c b) := by
  rw [pair_mul_pair a b c d, pair_antisymm (R := R) b c]; ring

theorem dR_one (μ : Fin 4) : dR (M := M) μ (1 : R) = 0 := by
  have h := dR_mul (M := M) μ (1 : R) 1
  simp only [mul_one, one_mul] at h
  have h' : dR (M := M) μ (1 : R) + 0 = dR (M := M) μ 1 + dR (M := M) μ 1 := by
    rw [add_zero]; exact h
  exact (add_left_cancel h').symm

theorem dR_intCast (μ : Fin 4) (n : ℤ) : dR (M := M) μ (n : R) = 0 := by
  have h : (n : R) = n • (1 : R) := by simp
  rw [h, map_zsmul, dR_one, smul_zero]

end SuperCalculus
end SYM
