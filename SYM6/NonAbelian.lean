import SYM6.Forms

/-!
# Non-abelian deformation D1: minimal coupling

The first deformation of the abelian 2-form theory to examine. Fields take values in an
associative algebra `A` (matrices), with the commutator as bracket.

**Deformation D1.** Introduce a connection `C_i` and replace `d` by the covariant exterior
derivative `D = d + [C, ·]` everywhere:

* field strength `H = D B`,
* tensor gauge transformation `δ_Λ B = D Λ` with `Λ` a 1-form, and `δ_Λ C = 0`.

**Result** (`covD_covD`, `minimal_coupling_variation`): `D² = F ∧ ·`, so
`δ_Λ H = F ∧ Λ`, where `F` is the curvature of `C`. The tensor gauge symmetry, which removes
the unphysical components of `B`, survives only when the curvature acts trivially. For a flat
connection it does survive (`covD_covD_of_flat`).

Hypotheses of the obstruction: values in an associative algebra with the commutator bracket;
the same connection in `H` and in `δB`; `δ_Λ C = 0`; no further fields; no 2-torsion.
-/

set_option autoImplicit false
namespace SYM6
open Finset

/-- A ring, not necessarily commutative, with commuting derivations and no 2-torsion. -/
class DiffAlg (ι : Type*) (A : Type*) [Ring A] where
  d : ι → A →+ A
  d_mul : ∀ i a b, d i (a * b) = d i a * b + a * d i b
  d_comm : ∀ i j a, d i (d j a) = d j (d i a)
  two_torsion : ∀ a : A, a + a = 0 → a = 0

variable {n : ℕ} {A : Type*} [Ring A] [DiffAlg (Fin n) A]

/-- The covariant derivative `∇_i X = ∂_i X + [C_i, X]` in the adjoint representation. -/
def nabla (C : Fin n → A) (i : Fin n) : A →+ A where
  toFun X := DiffAlg.d i X + (C i * X - X * C i)
  map_zero' := by simp
  map_add' X Y := by simp only [map_add, mul_add, add_mul]; abel

theorem nabla_apply (C : Fin n → A) (i : Fin n) (X : A) :
    nabla C i X = DiffAlg.d i X + (C i * X - X * C i) := rfl

/-- The curvature `F_ij = ∂_i C_j - ∂_j C_i + [C_i, C_j]`. -/
def curv (C : Fin n → A) (i j : Fin n) : A :=
  DiffAlg.d i (C j) - DiffAlg.d j (C i) + (C i * C j - C j * C i)

/-- The Ricci identity `[∇_i, ∇_j] X = [F_ij, X]`. -/
theorem ricci (C : Fin n → A) (i j : Fin n) (X : A) :
    nabla C i (nabla C j X) - nabla C j (nabla C i X) = curv C i j * X - X * curv C i j := by
  simp only [nabla_apply, curv, map_add, map_sub, DiffAlg.d_mul]
  rw [DiffAlg.d_comm j i X]
  noncomm_ring

/-- The covariant exterior derivative `D = d + [C, ·]` on algebra-valued forms. -/
def covD (C : Fin n → A) (ω : Finset (Fin n) → A) : Finset (Fin n) → A :=
  fun S => ∑ i ∈ S, sgn S i • nabla C i (ω (S.erase i))

theorem covD_add (C : Fin n → A) (ω ω' : Finset (Fin n) → A) :
    covD C (ω + ω') = covD C ω + covD C ω' := by
  funext S
  simp only [covD, Pi.add_apply, map_add, smul_add, sum_add_distrib]

/-- **`D² = F ∧ ·`.** Twice the square of the covariant exterior derivative is the curvature
acting on the form. -/
theorem covD_covD (C : Fin n → A) (ω : Finset (Fin n) → A) (S : Finset (Fin n)) :
    covD C (covD C ω) S + covD C (covD C ω) S =
      ∑ i ∈ S, ∑ j ∈ S, if j ≠ i then (sgn S i * sgn (S.erase i) j) •
        (curv C i j * ω ((S.erase i).erase j) - ω ((S.erase i).erase j) * curv C i j)
        else 0 := by
  set G : Fin n → Fin n → A := fun i j =>
    if j ≠ i then (sgn S i * sgn (S.erase i) j) •
      nabla C i (nabla C j (ω ((S.erase i).erase j))) else 0 with hG
  have h1 : covD C (covD C ω) S = ∑ i ∈ S, ∑ j ∈ S, G i j := by
    simp only [covD, map_sum, map_zsmul, smul_sum, smul_smul]
    refine sum_congr rfl fun i _ => ?_
    have key : ∀ f : Fin n → A, ∑ j ∈ S.erase i, f j = ∑ j ∈ S, if j ≠ i then f j else 0 :=
      fun f => by rw [← sum_filter, filter_ne']
    rw [key]
  have h2 : ∑ i ∈ S, ∑ j ∈ S, G i j = ∑ i ∈ S, ∑ j ∈ S, G j i := sum_comm
  rw [h1]
  nth_rewrite 2 [h2]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i hi => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j hj => ?_
  simp only [hG]
  by_cases hij : j = i
  · subst hij; simp
  · have hji : i ≠ j := fun e => hij e.symm
    rw [if_pos hij, if_pos hji, if_pos hij, sgn_mul_sgn_erase S hj hi hij, erase_right_comm,
      neg_smul, ← sub_eq_add_neg, ← smul_sub, ricci]

/-- For a flat connection, `D² = 0`. -/
theorem covD_covD_of_flat (C : Fin n → A) (hF : ∀ i j, curv C i j = 0)
    (ω : Finset (Fin n) → A) : covD C (covD C ω) = 0 := by
  funext S
  apply DiffAlg.two_torsion (ι := Fin n)
  rw [covD_covD]
  refine sum_eq_zero fun i _ => sum_eq_zero fun j _ => ?_
  split_ifs
  · rw [hF]; simp
  · rfl

/-- **Deformation D1 breaks the tensor gauge symmetry by the curvature.** With `H = D B` and
`δ_Λ B = D Λ`, twice the change of `H` is `F ∧ Λ`. -/
theorem minimal_coupling_variation (C : Fin n → A) (B Λ : Finset (Fin n) → A)
    (S : Finset (Fin n)) :
    (covD C (B + covD C Λ) S - covD C B S) + (covD C (B + covD C Λ) S - covD C B S) =
      ∑ i ∈ S, ∑ j ∈ S, if j ≠ i then (sgn S i * sgn (S.erase i) j) •
        (curv C i j * Λ ((S.erase i).erase j) - Λ ((S.erase i).erase j) * curv C i j)
        else 0 := by
  rw [covD_add, Pi.add_apply, add_sub_cancel_left, covD_covD]

end SYM6
