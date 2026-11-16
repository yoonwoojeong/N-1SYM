import Mathlib

/-!
# Differential forms in components, in any dimension

The four-dimensional framework (`SYM.SuperCalculus`) fixes the index type `Fin 4` and carries
an odd part. For the six-dimensional investigation the bosonic part is generalized here:

* `DiffRing ι R`: a commutative ring with commuting derivations indexed by an arbitrary type;
* a form is a function on `Finset (Fin n)`: its value on `S` is the component `ω_{i₁ … i_p}`
  with `i₁ < … < i_p` the elements of `S`. All degrees are carried at once;
* `extD` is the exterior derivative and `extD_extD` is `d² = 0`, in every degree and
  dimension.
-/

set_option autoImplicit false
namespace SYM6
open Finset

/-- A commutative ring with commuting derivations `d i`, without 2-torsion. -/
class DiffRing (ι : Type*) (R : Type*) [CommRing R] where
  d : ι → R →+ R
  d_mul : ∀ i a b, d i (a * b) = d i a * b + a * d i b
  d_comm : ∀ i j a, d i (d j a) = d j (d i a)
  two_torsion : ∀ a : R, 2 * a = 0 → a = 0

variable {n : ℕ}

/-- The number of elements of `S` below `i`: the position of `i` in `S`. -/
def pos (S : Finset (Fin n)) (i : Fin n) : ℕ := (S.filter (· < i)).card

/-- The sign `(-1)^{position of i in S}`. -/
def sgn (S : Finset (Fin n)) (i : Fin n) : ℤ := (-1) ^ pos S i

theorem sgn_erase_of_not_lt (S : Finset (Fin n)) {i j : Fin n} (h : ¬ i < j) :
    sgn (S.erase i) j = sgn S j := by
  have : (S.erase i).filter (· < j) = S.filter (· < j) := by
    ext x
    simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨⟨_, hx⟩, hlt⟩; exact ⟨hx, hlt⟩
    · rintro ⟨hx, hlt⟩; exact ⟨⟨fun e => h (e ▸ hlt), hx⟩, hlt⟩
  simp only [sgn, pos, this]

theorem sgn_erase_of_lt (S : Finset (Fin n)) {i j : Fin n} (hi : i ∈ S) (h : i < j) :
    sgn (S.erase i) j = -sgn S j := by
  have e : (S.erase i).filter (· < j) = (S.filter (· < j)).erase i := by
    ext x
    simp only [mem_filter, mem_erase]
    tauto
  have hm : i ∈ S.filter (· < j) := mem_filter.mpr ⟨hi, h⟩
  have hc : 0 < (S.filter (· < j)).card := card_pos.mpr ⟨i, hm⟩
  obtain ⟨k, hk⟩ : ∃ k, (S.filter (· < j)).card = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hc).symm⟩
  simp only [sgn, pos, e, card_erase_of_mem hm, hk, Nat.add_sub_cancel, pow_succ]
  ring

/-- Removing two indices in either order gives opposite signs. -/
theorem sgn_mul_sgn_erase (S : Finset (Fin n)) {i j : Fin n} (hi : i ∈ S) (hj : j ∈ S)
    (hij : i ≠ j) : sgn S i * sgn (S.erase i) j = -(sgn S j * sgn (S.erase j) i) := by
  rcases lt_or_gt_of_ne hij with h | h
  · rw [sgn_erase_of_lt S hi h, sgn_erase_of_not_lt S (not_lt.mpr h.le)]; ring
  · rw [sgn_erase_of_not_lt S (not_lt.mpr h.le), sgn_erase_of_lt S hj h]; ring

variable {R : Type*} [CommRing R] [DiffRing (Fin n) R]

/-- A differential form on `n`-dimensional space, all degrees at once. -/
abbrev Form (n : ℕ) (R : Type*) := Finset (Fin n) → R

/-- The exterior derivative: `(dω)_S = ∑_{i ∈ S} (-1)^{pos} ∂_i ω_{S ∖ i}`. -/
def extD (ω : Form n R) : Form n R :=
  fun S => ∑ i ∈ S, sgn S i • DiffRing.d i (ω (S.erase i))

theorem extD_add (ω ω' : Form n R) : extD (ω + ω') = extD ω + extD ω' := by
  funext S
  simp only [extD, Pi.add_apply, map_add, smul_add, sum_add_distrib]

theorem extD_neg (ω : Form n R) : extD (-ω) = -extD ω := by
  funext S
  simp only [extD, Pi.neg_apply, map_neg, smul_neg, sum_neg_distrib]

/-- **`d² = 0`**, in every degree and dimension. -/
theorem extD_extD (ω : Form n R) : extD (extD ω) = 0 := by
  funext S
  set G : Fin n → Fin n → R := fun i j =>
    if j ≠ i then (sgn S i * sgn (S.erase i) j) •
      DiffRing.d i (DiffRing.d j (ω ((S.erase i).erase j))) else 0 with hG
  have h1 : extD (extD ω) S = ∑ i ∈ S, ∑ j ∈ S, G i j := by
    simp only [extD, map_sum, map_zsmul, smul_sum, smul_smul]
    refine sum_congr rfl fun i _ => ?_
    have key : ∀ f : Fin n → R, ∑ j ∈ S.erase i, f j = ∑ j ∈ S, if j ≠ i then f j else 0 :=
      fun f => by rw [← sum_filter, filter_ne']
    rw [key]
  have h2 : ∀ i ∈ S, ∀ j ∈ S, G j i = -G i j := by
    intro i hi j hj
    simp only [hG]
    by_cases hij : j = i
    · subst hij; simp
    · have hji : i ≠ j := fun e => hij e.symm
      rw [if_pos hji, if_pos hij, sgn_mul_sgn_erase S hj hi hij, erase_right_comm,
        DiffRing.d_comm, neg_smul]
  have h3 : ∑ i ∈ S, ∑ j ∈ S, G i j = -∑ i ∈ S, ∑ j ∈ S, G i j := by
    conv_lhs => rw [sum_comm]
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun i hi => ?_
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun j hj => h2 i hi j hj
  rw [h1]
  apply DiffRing.two_torsion (ι := Fin n)
  rw [two_mul]
  nth_rewrite 1 [h3]
  exact neg_add_cancel _

end SYM6
