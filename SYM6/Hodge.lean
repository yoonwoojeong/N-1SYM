import SYM6.Forms

/-!
# Six dimensions: Hodge star on 3-forms, and why `H ∧ *H` fails

Signature `(+,+,+,+,+,-)`, time last. The Hodge star is `(*ω)_S = κ(S) ω_{Sᶜ}` with
`κ(S) = ε(S, Sᶜ) η(Sᶜ)`, where `ε` is the sign of the shuffle and `η(T) = ∏_{i ∈ T} η_i`.

Results:

* `star_star`: `** = 1` on 3-forms, so real self-dual 3-forms exist;
* `pairing3_selfDual`: the density `H ∧ *H` vanishes identically on self-dual `H`;
* `pairing3_extD`: integration by parts, giving the field equation `div H = 0` of `H ∧ *H`;
* `star_extD_star`: `div = * d *` on 3-forms;
* `div_eq_zero_of_antiSelfDual`: every closed anti-self-dual `H` solves that field equation.

Together: `H ∧ *H` is not an action for a self-dual field (candidate C1 in the log).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace SYM6
open Finset

/-- Diagonal of the metric, time last. -/
def η6 (i : Fin 6) : ℤ := if i = 5 then -1 else 1

/-- `η(S) = ∏_{i ∈ S} η_i`. -/
def ηF (S : Finset (Fin 6)) : ℤ := ∏ i ∈ S, η6 i

/-- Sign of the shuffle `(S, Sᶜ)`: the Levi-Civita symbol on increasing indices. -/
def shuf (S : Finset (Fin 6)) : ℤ := ∏ a ∈ S, ∏ b ∈ Sᶜ, if b < a then -1 else 1

/-- Coefficient of the Hodge star. -/
def κ (S : Finset (Fin 6)) : ℤ := shuf S * ηF Sᶜ

/-- Weight of a 3-form component in the inner product. -/
def w3 (S : Finset (Fin 6)) : ℤ := if S.card = 3 then ηF S else 0

/-- Weight of a 2-form component in the inner product. -/
def w2 (S : Finset (Fin 6)) : ℤ := if S.card = 2 then ηF S else 0

set_option maxRecDepth 100000 in
theorem κ_mul_κ_compl : ∀ S : Finset (Fin 6), S.card = 3 → κ S * κ Sᶜ = 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem w3_κ_compl : ∀ S : Finset (Fin 6), w3 Sᶜ * κ Sᶜ = -(w3 S * κ S) := by decide +kernel

set_option maxRecDepth 100000 in
theorem κ_sgn_κ : ∀ T : Finset (Fin 6), T.card = 2 → ∀ i, i ∉ T →
    κ T * (sgn Tᶜ i * κ (Tᶜ.erase i)) = η6 i * sgn (insert i T) i := by decide +kernel

set_option maxRecDepth 100000 in
theorem w3_insert : ∀ (T : Finset (Fin 6)) (i : Fin 6), i ∉ T →
    w3 (insert i T) = w2 T * η6 i := by decide +kernel

variable {R : Type*} [CommRing R] [DiffRing (Fin 6) R]

/-- The Hodge star. -/
def star (ω : Form 6 R) : Form 6 R := fun S => κ S • ω Sᶜ

/-- **`** = 1` on 3-forms** in signature `(5,1)`. -/
theorem star_star (ω : Form 6 R) (S : Finset (Fin 6)) (h : S.card = 3) :
    star (star ω) S = ω S := by
  simp only [star, smul_smul, compl_compl, κ_mul_κ_compl S h, one_smul]

/-- A 3-form is self-dual. -/
def SelfDual (H : Form 6 R) : Prop := ∀ S, S.card = 3 → H S = star H S

/-- A 3-form is anti-self-dual. -/
def AntiSelfDual (H : Form 6 R) : Prop := ∀ S, S.card = 3 → H S = -star H S

/-- The inner product of 3-forms; `pairing3 H H` is the density of `H ∧ *H`. -/
def pairing3 (ω ω' : Form 6 R) : R := ∑ S : Finset (Fin 6), w3 S • (ω S * ω' S)

/-- The inner product of 2-forms. -/
def pairing2 (ω ω' : Form 6 R) : R := ∑ S : Finset (Fin 6), w2 S • (ω S * ω' S)

/-- `∑_S t(S) = 0` when `t(Sᶜ) = -t(S)`. -/
theorem sum_compl_antisymm (t : Finset (Fin 6) → R) (h : ∀ S, t Sᶜ = -t S) :
    ∑ S, t S = 0 := by
  have e : ∑ S, t S = ∑ S, t Sᶜ :=
    (Equiv.sum_comp (⟨compl, compl, compl_compl, compl_compl⟩ :
      Finset (Fin 6) ≃ Finset (Fin 6)) t).symm
  have e' : ∑ S, t S = -∑ S, t S := by
    conv_lhs => rw [e]
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun S _ => h S
  apply DiffRing.two_torsion (ι := Fin 6)
  rw [two_mul]
  nth_rewrite 1 [e']
  exact neg_add_cancel _

/-- **The density `H ∧ *H` vanishes identically on self-dual 3-forms.** -/
theorem pairing3_selfDual (H : Form 6 R) (h : SelfDual H) : pairing3 H H = 0 := by
  have e : pairing3 H H = ∑ S : Finset (Fin 6), (w3 S * κ S) • (H S * H Sᶜ) := by
    refine sum_congr rfl fun S _ => ?_
    by_cases hc : S.card = 3
    · have hS := h S hc
      simp only [star] at hS
      nth_rewrite 2 [hS]
      rw [mul_smul_comm, smul_smul]
    · simp [w3, hc]
  rw [e]
  refine sum_compl_antisymm _ fun S => ?_
  rw [w3_κ_compl, compl_compl, neg_smul, mul_comm (H Sᶜ) (H S)]

/-- The same for anti-self-dual 3-forms. -/
theorem pairing3_antiSelfDual (H : Form 6 R) (h : AntiSelfDual H) : pairing3 H H = 0 := by
  have e : pairing3 H H = -∑ S : Finset (Fin 6), (w3 S * κ S) • (H S * H Sᶜ) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun S _ => ?_
    by_cases hc : S.card = 3
    · have hS := h S hc
      simp only [star] at hS
      nth_rewrite 2 [hS]
      rw [mul_neg, mul_smul_comm, smul_neg, smul_smul]
    · simp [w3, hc]
  rw [e, neg_eq_zero]
  refine sum_compl_antisymm _ fun S => ?_
  rw [w3_κ_compl, compl_compl, neg_smul, mul_comm (H Sᶜ) (H S)]

/-- The divergence `(div H)_T = ∑_i η_i ∂_i H_{i T}` of a 3-form. -/
def div (H : Form 6 R) : Form 6 R :=
  fun T => ∑ i ∈ Tᶜ, (η6 i * sgn (insert i T) i) • DiffRing.d i (H (insert i T))

/-- `div = * d *` on 3-forms. -/
theorem star_extD_star (H : Form 6 R) (T : Finset (Fin 6)) (hT : T.card = 2) :
    star (extD (star H)) T = div H T := by
  simp only [star, extD, div, map_zsmul, smul_sum, smul_smul, compl_erase, compl_compl]
  refine sum_congr rfl fun i hi => ?_
  rw [κ_sgn_κ T hT i (mem_compl.mp hi)]

/-- Every closed anti-self-dual 3-form solves `div H = 0`. -/
theorem div_eq_zero_of_antiSelfDual (H : Form 6 R) (h : AntiSelfDual H)
    (hcl : ∀ U : Finset (Fin 6), U.card = 4 → extD H U = 0) (T : Finset (Fin 6))
    (hT : T.card = 2) : div H T = 0 := by
  rw [← star_extD_star H T hT]
  have hc : Tᶜ.card = 4 := by rw [card_compl, hT]; rfl
  have e : extD (star H) Tᶜ = -extD H Tᶜ := by
    simp only [extD, ← sum_neg_distrib]
    refine sum_congr rfl fun i hi => ?_
    have h3 : (Tᶜ.erase i).card = 3 := by rw [card_erase_of_mem hi, hc]
    have hS := h _ h3
    rw [hS, map_neg, smul_neg, neg_neg]
  show κ T • extD (star H) Tᶜ = 0
  rw [e, hcl _ hc, neg_zero, smul_zero]

/-- Every closed self-dual 3-form solves `div H = 0`. -/
theorem div_eq_zero_of_selfDual (H : Form 6 R) (h : SelfDual H)
    (hcl : ∀ U : Finset (Fin 6), U.card = 4 → extD H U = 0) (T : Finset (Fin 6))
    (hT : T.card = 2) : div H T = 0 := by
  rw [← star_extD_star H T hT]
  have hc : Tᶜ.card = 4 := by rw [card_compl, hT]; rfl
  have e : extD (star H) Tᶜ = extD H Tᶜ := by
    simp only [extD]
    refine sum_congr rfl fun i hi => ?_
    have h3 : (Tᶜ.erase i).card = 3 := by rw [card_erase_of_mem hi, hc]
    rw [← h _ h3]
  show κ T • extD (star H) Tᶜ = 0
  rw [e, hcl _ hc, smul_zero]

/-! ## The field equation of `H ∧ *H` -/

theorem sum_mem_eq_sum_ite {P : Type*} [AddCommMonoid P] (S : Finset (Fin 6)) (f : Fin 6 → P) :
    ∑ i ∈ S, f i = ∑ i : Fin 6, if i ∈ S then f i else 0 := by
  rw [← sum_filter, filter_univ_mem]

/-- Reindexing a sum over sets containing `i` by the sets not containing `i`. -/
theorem sum_insert_reindex {P : Type*} [AddCommMonoid P] (i : Fin 6)
    (F : Finset (Fin 6) → P) :
    (∑ S : Finset (Fin 6), if i ∈ S then F S else 0) =
      ∑ T : Finset (Fin 6), if i ∉ T then F (insert i T) else 0 := by
  rw [← sum_filter, ← sum_filter]
  refine sum_bij' (fun S _ => S.erase i) (fun T _ => insert i T) ?_ ?_ ?_ ?_ ?_
  · intro S hS; simp
  · intro T hT; simp
  · intro S hS; exact insert_erase (mem_filter.mp hS).2
  · intro T hT; exact erase_insert (mem_filter.mp hT).2
  · intro S hS; rw [insert_erase (mem_filter.mp hS).2]

/-- The boundary term of the integration by parts. -/
def flux (H b : Form 6 R) (i : Fin 6) : R :=
  ∑ S : Finset (Fin 6), if i ∈ S then (w3 S * sgn S i) • (H S * b (S.erase i)) else 0

/-- **Integration by parts:** `⟨H, db⟩ = ∂_i (flux) - ⟨div H, b⟩`. Hence the first variation
of `⟨dB, dB⟩` along `b` is `-2 ⟨div dB, b⟩` up to a divergence, and its field equation is
`div dB = 0`. -/
theorem pairing3_extD (H b : Form 6 R) :
    pairing3 H (extD b) = ∑ i, DiffRing.d i (flux H b i) - pairing2 (div H) b := by
  have h1 : pairing3 H (extD b) = ∑ i : Fin 6, ∑ S : Finset (Fin 6),
      if i ∈ S then (w3 S * sgn S i) • (H S * DiffRing.d i (b (S.erase i))) else 0 := by
    rw [sum_comm]
    refine sum_congr rfl fun S _ => ?_
    simp only [extD, mul_sum, smul_sum, mul_smul_comm, smul_smul]
    exact sum_mem_eq_sum_ite S _
  have h2 : ∀ i : Fin 6, DiffRing.d i (flux H b i) = ∑ S : Finset (Fin 6),
      if i ∈ S then (w3 S * sgn S i) • (DiffRing.d i (H S) * b (S.erase i)
        + H S * DiffRing.d i (b (S.erase i))) else 0 := by
    intro i
    simp only [flux, map_sum]
    refine sum_congr rfl fun S _ => ?_
    split_ifs
    · rw [map_zsmul, DiffRing.d_mul]
    · rw [map_zero]
  have h3 : pairing2 (div H) b = ∑ i : Fin 6, ∑ S : Finset (Fin 6),
      if i ∈ S then (w3 S * sgn S i) • (DiffRing.d i (H S) * b (S.erase i)) else 0 := by
    have e : ∀ i : Fin 6, (∑ S : Finset (Fin 6),
        if i ∈ S then (w3 S * sgn S i) • (DiffRing.d i (H S) * b (S.erase i)) else 0) =
        ∑ T : Finset (Fin 6), if i ∉ T then
          (w2 T * (η6 i * sgn (insert i T) i)) • (DiffRing.d i (H (insert i T)) * b T)
          else 0 := by
      intro i
      rw [sum_insert_reindex i fun S =>
        (w3 S * sgn S i) • (DiffRing.d i (H S) * b (S.erase i))]
      refine sum_congr rfl fun T _ => ?_
      by_cases hi : i ∈ T
      · simp [hi]
      · rw [if_pos hi, if_pos hi, w3_insert T i hi, erase_insert hi, mul_assoc]
    simp only [e]
    rw [sum_comm]
    refine sum_congr rfl fun T _ => ?_
    simp only [div, sum_mul, smul_sum, smul_mul_assoc, smul_smul]
    rw [sum_mem_eq_sum_ite]
    refine sum_congr rfl fun i _ => ?_
    simp only [mem_compl]
  rw [h1, h3]
  simp only [h2]
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun S _ => ?_
  split_ifs
  · rw [smul_add]; abel
  · simp

end SYM6
