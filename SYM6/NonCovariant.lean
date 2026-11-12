import SYM6.Hodge

/-!
# Candidate C2: an action with non-manifest Lorentz covariance

Split the 3-form `H = dB` into magnetic components `H_S` (`S` spatial) and electric
components (`S` containing time). The self-duality defect is `D = H - *H`. The candidate is

`L(B) = -∑_{S spatial} H_S D_S = ∑_{S spatial} (κ_S H_S H_{Sᶜ} - H_S²)`,

"magnetic times electric minus magnetic squared". It is not `H ∧ *H`, and it is not
manifestly Lorentz invariant.

Results:

* `dLagNC_eq`: the first variation is `-⟨codiff Y, b⟩` up to a divergence;
* `codiff_Y`: the field equation is `d(D_el) = 0`, where `D_el` is the electric part of the
  self-duality defect: the field equation is first order in time and is the curl of the
  self-duality condition;
* `fieldEquation_of_selfDual`: self-dual configurations solve it;
* `selfDual_of_exact`: if `D_el` is the exterior derivative of a 2-form with only time
  components, the configuration differs from a self-dual one by that 2-form.

So the field equations give self-duality exactly when closed implies exact for the electric
defect: a Poincaré lemma, which is a hypothesis on the space of fields and is not available
in an abstract `DiffRing`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace SYM6
open Finset

/-- Indicator of spatial 3-index sets. -/
def mSp (S : Finset (Fin 6)) : ℤ := if S.card = 3 ∧ (5 : Fin 6) ∉ S then 1 else 0

/-- Indicator of 3-index sets containing time. -/
def tEl (S : Finset (Fin 6)) : ℤ := if S.card = 3 ∧ (5 : Fin 6) ∈ S then 1 else 0

set_option maxRecDepth 100000 in
theorem nc_sign₁ : ∀ T : Finset (Fin 6), T.card = 2 → ∀ i, i ∉ T →
    sgn (insert i T) i * mSp (insert i T) =
      -shuf T * (sgn Tᶜ i * (tEl (Tᶜ.erase i) * κ (Tᶜ.erase i))) := by decide +kernel

set_option maxRecDepth 100000 in
theorem nc_sign₂ : ∀ T : Finset (Fin 6), T.card = 2 → ∀ i, i ∉ T →
    sgn (insert i T) i * (mSp (insert i T) * κ (insert i T)
        + mSp (Tᶜ.erase i) * κ (Tᶜ.erase i)) =
      2 * -shuf T * (sgn Tᶜ i * tEl (Tᶜ.erase i)) + shuf T * sgn Tᶜ i := by decide +kernel

set_option maxRecDepth 100000 in
theorem shuf_mul_self : ∀ T : Finset (Fin 6), shuf T * shuf T = 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem mSp_insert_of_card : ∀ (T : Finset (Fin 6)) (i : Fin 6), T.card ≠ 2 → i ∉ T →
    mSp (insert i T) = 0 ∧ mSp (Tᶜ.erase i) = 0 := by decide +kernel

variable {R : Type*} [CommRing R] [DiffRing (Fin 6) R]

theorem extD_sub (ω ω' : Form 6 R) : extD (ω - ω') = extD ω - extD ω' := by
  rw [sub_eq_add_neg, extD_add, extD_neg, ← sub_eq_add_neg]

/-- The self-duality defect `D = H - *H`. -/
def defect (H : Form 6 R) : Form 6 R := fun S => H S - star H S

/-- The electric part of the self-duality defect. -/
def elDefect (H : Form 6 R) : Form 6 R := fun S => tEl S • defect H S

/-- The candidate Lagrangian. -/
def lagNC (B : Form 6 R) : R := -∑ S : Finset (Fin 6), mSp S • (extD B S * defect (extD B) S)

/-- Its first variation along `b` (the polarization of the quadratic form `lagNC`). -/
def dLagNC (B b : Form 6 R) : R :=
  -∑ S : Finset (Fin 6), mSp S •
    (extD b S * defect (extD B) S + extD B S * defect (extD b) S)

/-- The 3-form paired with `db` in the first variation. -/
def Y (H : Form 6 R) : Form 6 R :=
  fun S => mSp S • (κ S • H Sᶜ - (2 : ℤ) • H S) + (mSp Sᶜ * κ Sᶜ) • H Sᶜ

/-- The codifferential without metric: `(codiff Y)_T = ∑_{i ∉ T} ± ∂_i Y_{iT}`. -/
def codiff (Y : Form 6 R) : Form 6 R :=
  fun T => ∑ i ∈ Tᶜ, sgn (insert i T) i • DiffRing.d i (Y (insert i T))

/-- The boundary term. -/
def fluxY (Y b : Form 6 R) (i : Fin 6) : R :=
  ∑ S : Finset (Fin 6), if i ∈ S then sgn S i • (Y S * b (S.erase i)) else 0

/-- Integration by parts for an arbitrary form paired with `db`. -/
theorem sum_mul_extD (Y b : Form 6 R) :
    ∑ S : Finset (Fin 6), Y S * extD b S =
      ∑ i, DiffRing.d i (fluxY Y b i) - ∑ T : Finset (Fin 6), codiff Y T * b T := by
  have h1 : ∑ S : Finset (Fin 6), Y S * extD b S = ∑ i : Fin 6, ∑ S : Finset (Fin 6),
      if i ∈ S then sgn S i • (Y S * DiffRing.d i (b (S.erase i))) else 0 := by
    rw [sum_comm]
    refine sum_congr rfl fun S _ => ?_
    simp only [extD, mul_sum, mul_smul_comm]
    exact sum_mem_eq_sum_ite S _
  have h2 : ∀ i : Fin 6, DiffRing.d i (fluxY Y b i) = ∑ S : Finset (Fin 6),
      if i ∈ S then sgn S i • (DiffRing.d i (Y S) * b (S.erase i)
        + Y S * DiffRing.d i (b (S.erase i))) else 0 := by
    intro i
    simp only [fluxY, map_sum]
    refine sum_congr rfl fun S _ => ?_
    split_ifs
    · rw [map_zsmul, DiffRing.d_mul]
    · rw [map_zero]
  have h3 : ∑ T : Finset (Fin 6), codiff Y T * b T = ∑ i : Fin 6, ∑ S : Finset (Fin 6),
      if i ∈ S then sgn S i • (DiffRing.d i (Y S) * b (S.erase i)) else 0 := by
    have e : ∀ i : Fin 6, (∑ S : Finset (Fin 6),
        if i ∈ S then sgn S i • (DiffRing.d i (Y S) * b (S.erase i)) else 0) =
        ∑ T : Finset (Fin 6), if i ∉ T then
          sgn (insert i T) i • (DiffRing.d i (Y (insert i T)) * b T) else 0 := by
      intro i
      rw [sum_insert_reindex i fun S => sgn S i • (DiffRing.d i (Y S) * b (S.erase i))]
      refine sum_congr rfl fun T _ => ?_
      by_cases hi : i ∈ T
      · simp [hi]
      · rw [if_pos hi, if_pos hi, erase_insert hi]
    simp only [e]
    rw [sum_comm]
    refine sum_congr rfl fun T _ => ?_
    simp only [codiff, sum_mul, smul_mul_assoc]
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

/-- The first variation is the pairing of `Y(dB)` with `db`. -/
theorem dLagNC_eq_sum (B b : Form 6 R) :
    dLagNC B b = ∑ S : Finset (Fin 6), Y (extD B) S * extD b S := by
  have e : ∑ S : Finset (Fin 6), (mSp S * κ S) • (extD B S * extD b Sᶜ) =
      ∑ S : Finset (Fin 6), (mSp Sᶜ * κ Sᶜ) • (extD B Sᶜ * extD b S) := by
    have := Equiv.sum_comp (⟨compl, compl, compl_compl, compl_compl⟩ :
      Finset (Fin 6) ≃ Finset (Fin 6))
      (fun S => (mSp S * κ S) • (extD B S * extD b Sᶜ))
    simp only [Equiv.coe_fn_mk, compl_compl] at this
    exact this.symm
  have e2 : dLagNC B b = ∑ S : Finset (Fin 6),
      (mSp S • ((κ S • extD B Sᶜ - (2 : ℤ) • extD B S) * extD b S)
        + (mSp S * κ S) • (extD B S * extD b Sᶜ)) := by
    rw [dLagNC, ← sum_neg_distrib]
    refine sum_congr rfl fun S _ => ?_
    simp only [defect, star, zsmul_eq_mul]
    push_cast; ring
  rw [e2, sum_add_distrib, e, ← sum_add_distrib]
  refine sum_congr rfl fun S _ => ?_
  simp only [Y, zsmul_eq_mul]
  push_cast; ring

/-- **The first-variation formula of the candidate.** -/
theorem dLagNC_eq (B b : Form 6 R) :
    dLagNC B b = ∑ i, DiffRing.d i (fluxY (Y (extD B)) b i)
      - ∑ T : Finset (Fin 6), codiff (Y (extD B)) T * b T := by
  rw [dLagNC_eq_sum, sum_mul_extD]

/-- The field equation in terms of the electric defect, for any 3-form `H`. -/
theorem codiff_Y_general (H : Form 6 R) (T : Finset (Fin 6)) (hT : T.card = 2) :
    codiff (Y H) T =
      (2 * -shuf T) • extD (elDefect H) Tᶜ + shuf T • extD H Tᶜ := by
  simp only [codiff, extD, smul_sum]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ∉ T := mem_compl.mp hi
  have a1 := congrArg (fun z : ℤ => z • DiffRing.d i (H (insert i T))) (nc_sign₁ T hT i hi')
  have a2 := congrArg (fun z : ℤ => z • DiffRing.d i (H (Tᶜ.erase i))) (nc_sign₂ T hT i hi')
  simp only [Y, elDefect, defect, star, compl_insert, compl_erase, compl_compl, map_add,
    map_sub, map_zsmul]
  linear_combination (norm := module) a2 - (2 : ℤ) • a1

/-- **The field equation of the candidate is the curl of the self-duality condition:**
`codiff Y = ∓2 d(D_el)`. -/
theorem codiff_Y (B : Form 6 R) (T : Finset (Fin 6)) (hT : T.card = 2) :
    codiff (Y (extD B)) T = (2 * -shuf T) • extD (elDefect (extD B)) Tᶜ := by
  rw [codiff_Y_general _ T hT, extD_extD]
  simp

/-- The field equation holds on 2-index sets iff the electric defect is closed. -/
theorem fieldEquation_iff (B : Form 6 R) :
    (∀ T : Finset (Fin 6), T.card = 2 → codiff (Y (extD B)) T = 0) ↔
      ∀ U : Finset (Fin 6), U.card = 4 → extD (elDefect (extD B)) U = 0 := by
  constructor
  · intro h U hU
    have hc : Uᶜ.card = 2 := by rw [card_compl, hU]; rfl
    have h1 := h Uᶜ hc
    rw [codiff_Y B Uᶜ hc, compl_compl] at h1
    have h2 := congrArg (fun x : R => shuf Uᶜ • x) h1
    simp only [smul_smul, smul_zero] at h2
    have h3 : shuf Uᶜ * (2 * -shuf Uᶜ) = -2 := by
      have := shuf_mul_self Uᶜ; linear_combination -2 * this
    rw [h3] at h2
    apply DiffRing.two_torsion (ι := Fin 6)
    have h4 : (2 : R) * extD (elDefect (extD B)) U = -((-2 : ℤ) • extD (elDefect (extD B)) U) := by
      simp
    rw [h4, h2, neg_zero]
  · intro h T hT
    have hc : Tᶜ.card = 4 := by rw [card_compl, hT]; rfl
    rw [codiff_Y B T hT, h _ hc, smul_zero]

/-- Self-dual configurations solve the field equation. -/
theorem fieldEquation_of_selfDual (B : Form 6 R) (h : SelfDual (extD B)) (T : Finset (Fin 6))
    (hT : T.card = 2) : codiff (Y (extD B)) T = 0 := by
  have h0 : elDefect (extD B) = 0 := by
    funext S
    by_cases hc : S.card = 3
    · simp only [elDefect, defect, ← h S hc, sub_self, smul_zero, Pi.zero_apply]
    · simp [elDefect, tEl, hc]
  rw [codiff_Y B T hT, h0]
  simp [extD]

/-- **Gauge fixing.** If the electric defect is the exterior derivative of a 2-form `β` with
only time components, then `B - β` is self-dual. -/
theorem selfDual_of_exact (B β : Form 6 R) (hβ : ∀ T : Finset (Fin 6), (5 : Fin 6) ∉ T → β T = 0)
    (hex : ∀ S : Finset (Fin 6), S.card = 3 → (5 : Fin 6) ∈ S →
      defect (extD B) S = extD β S) : SelfDual (extD (B - β)) := by
  have hsp : ∀ S : Finset (Fin 6), (5 : Fin 6) ∉ S → extD β S = 0 := by
    intro S hS
    simp only [extD]
    refine sum_eq_zero fun i _ => ?_
    rw [hβ _ (fun h => hS (mem_of_mem_erase h)), map_zero, smul_zero]
  have key : ∀ S : Finset (Fin 6), S.card = 3 → (5 : Fin 6) ∈ S →
      extD (B - β) S = star (extD (B - β)) S := by
    intro S hS h5
    have h := hex S hS h5
    simp only [defect, star] at h
    simp only [extD_sub, star, Pi.sub_apply, hsp Sᶜ (fun hh => (mem_compl.mp hh) h5), sub_zero]
    linear_combination h
  intro S hS
  by_cases h5 : (5 : Fin 6) ∈ S
  · exact key S hS h5
  · have hc : Sᶜ.card = 3 := by rw [card_compl, hS]; rfl
    have h := key Sᶜ hc (mem_compl.mpr h5)
    simp only [star, compl_compl] at h ⊢
    rw [h, smul_smul, κ_mul_κ_compl S hS, one_smul]

end SYM6
