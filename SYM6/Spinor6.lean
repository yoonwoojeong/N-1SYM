import SYM6.SuperCalc
import SYM6.Gamma6

/-!
# The fermion calculus in six dimensions

The four-dimensional spinor bilinear calculus (`SYM.sbil`, `SYM.mv`) fixed the spinor index
to `Fin 4`. Here it is generalized to any finite spinor index type and then specialized.

* `sbilG`, `mvG`: spinor bilinears and matrix action for any spinor size, with the same
  lemmas as in four dimensions (linearity, moving a matrix across, exchange of the two
  spinors, Leibniz rule);
* six dimensions: 16-component real spinors, chirality, and the sign rules for exchanging two
  odd spinors in `ψ̄ χ`, `ψ̄ Γ^a χ`, `ψ̄ q χ`, `ψ̄ q Γ^a χ`;
* (2,0): a pair of 16-component spinors, the ten generators of the R-symmetry `Sp(4)`
  (anti-Hermitian `2 × 2` quaternionic matrices), invariance of the pairing, and
  preservation of chirality.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace SYM6
open Finset Matrix

section generic
variable {R : Type*} [CommRing R]
variable {U V W : Type*} [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]
variable {σ : Type*} [Fintype σ]

/-- The spinor bilinear with coefficient matrix `N`, for any spinor index type. -/
def sbilG (B : U →ₗ[R] V →ₗ[R] W) (N : Matrix σ σ ℤ) (u : σ → U) (v : σ → V) : W :=
  ∑ α, ∑ β, N α β • B (u α) (v β)

/-- Action of an integer matrix on a spinor. -/
def mvG (P : Matrix σ σ ℤ) (w : σ → V) : σ → V := fun α => ∑ β, P α β • w β

variable (B : U →ₗ[R] V →ₗ[R] W) (N N' : Matrix σ σ ℤ) (u u' : σ → U) (v v' : σ → V)

theorem sbilG_add_mat : sbilG B (N + N') u v = sbilG B N u v + sbilG B N' u v := by
  simp only [sbilG, Matrix.add_apply, add_smul, sum_add_distrib]

theorem sbilG_neg_mat : sbilG B (-N) u v = -sbilG B N u v := by
  simp only [sbilG, Matrix.neg_apply, neg_smul, sum_neg_distrib]

theorem sbilG_zsmul_mat (n : ℤ) : sbilG B (n • N) u v = n • sbilG B N u v := by
  simp only [sbilG, Matrix.smul_apply, smul_eq_mul, mul_smul, smul_sum]

theorem sbilG_zero_mat : sbilG B 0 u v = 0 := by
  simp only [sbilG, Matrix.zero_apply, zero_smul, sum_const_zero]

theorem sbilG_add_right :
    sbilG B N u (fun β => v β + v' β) = sbilG B N u v + sbilG B N u v' := by
  simp only [sbilG, map_add, smul_add, sum_add_distrib]

theorem sbilG_add_left :
    sbilG B N (fun α => u α + u' α) v = sbilG B N u v + sbilG B N u' v := by
  simp only [sbilG, map_add, LinearMap.add_apply, smul_add, sum_add_distrib]

theorem sbilG_zsmul_right (n : ℤ) : sbilG B N u (fun β => n • v β) = n • sbilG B N u v := by
  simp only [sbilG, map_zsmul, smul_sum, smul_comm n]

theorem sbilG_zsmul_left (n : ℤ) : sbilG B N (fun α => n • u α) v = n • sbilG B N u v := by
  simp only [sbilG, map_zsmul, LinearMap.smul_apply, smul_sum, smul_comm n]

theorem sbilG_sum_right {κ : Type*} (s : Finset κ) (w : κ → σ → V) :
    sbilG B N u (fun β => ∑ i ∈ s, w i β) = ∑ i ∈ s, sbilG B N u (w i) := by
  simp only [sbilG, map_sum, smul_sum]
  exact (sum_congr rfl fun α _ => sum_comm).trans sum_comm

theorem sbilG_sum_left {κ : Type*} (s : Finset κ) (w : κ → σ → U) :
    sbilG B N (fun α => ∑ i ∈ s, w i α) v = ∑ i ∈ s, sbilG B N (w i) v := by
  simp only [sbilG, map_sum, LinearMap.sum_apply, smul_sum]
  exact (sum_congr rfl fun α _ => sum_comm).trans sum_comm

/-- Moving a matrix off the right spinor. -/
theorem sbilG_mv_right (P : Matrix σ σ ℤ) (w : σ → V) :
    sbilG B N u (mvG P w) = sbilG B (N * P) u w := by
  simp only [sbilG, mvG, map_sum, map_zsmul, smul_sum, smul_smul, Matrix.mul_apply, sum_smul]
  exact sum_congr rfl fun α _ => sum_comm

/-- Moving a matrix off the left spinor. -/
theorem sbilG_mv_left (P : Matrix σ σ ℤ) (w : σ → U) :
    sbilG B N (mvG P w) v = sbilG B (P.transpose * N) w v := by
  simp only [sbilG, mvG, map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_sum, smul_smul, Matrix.mul_apply, Matrix.transpose_apply, sum_smul]
  calc _ = ∑ β, ∑ α, ∑ γ', (N α β * P α γ') • B (w γ') (v β) := sum_comm
    _ = ∑ β, ∑ γ', ∑ α, (N α β * P α γ') • B (w γ') (v β) :=
      sum_congr rfl fun _ _ => sum_comm
    _ = ∑ γ', ∑ β, ∑ α, (N α β * P α γ') • B (w γ') (v β) := sum_comm
    _ = _ := sum_congr rfl fun γ' _ => sum_congr rfl fun β _ => sum_congr rfl fun α _ => by
      rw [mul_comm]

/-- Exchanging the two spinors of a bilinear built from an antisymmetric product. -/
theorem sbilG_flip (B' : V →ₗ[R] U →ₗ[R] W) (h : ∀ x y, B x y = -B' y x) :
    sbilG B N u v = -sbilG B' N.transpose v u := by
  simp only [sbilG, Matrix.transpose_apply]
  rw [sum_comm, ← sum_neg_distrib]
  refine sum_congr rfl fun β _ => ?_
  rw [← sum_neg_distrib]
  exact sum_congr rfl fun α _ => by rw [h, smul_neg]

/-- Leibniz rule for a spinor bilinear. -/
theorem sbilG_deriv {U₁ V₁ W₁ : Type*} [AddCommGroup U₁] [Module R U₁] [AddCommGroup V₁]
    [Module R V₁] [AddCommGroup W₁] [Module R W₁] (D : W →+ W₁) (B₁ : U₁ →ₗ[R] V →ₗ[R] W₁)
    (B₂ : U →ₗ[R] V₁ →ₗ[R] W₁) (dU : U → U₁) (dV : V → V₁)
    (h : ∀ x y, D (B x y) = B₁ (dU x) y + B₂ x (dV y)) :
    D (sbilG B N u v) = sbilG B₁ N (fun α => dU (u α)) v + sbilG B₂ N u (fun β => dV (v β)) := by
  simp only [sbilG, map_sum, map_zsmul, h, smul_add, sum_add_distrib]

theorem mvG_mvG (P Q : Matrix σ σ ℤ) (w : σ → V) : mvG P (mvG Q w) = mvG (P * Q) w := by
  funext α
  simp only [mvG, smul_sum, smul_smul, Matrix.mul_apply, sum_smul]
  exact sum_comm

theorem mvG_zsmul (P : Matrix σ σ ℤ) (n : ℤ) (w : σ → V) :
    mvG P (fun β => n • w β) = fun α => n • mvG P w α := by
  funext α
  simp only [mvG, smul_sum, smul_comm n]

theorem mvG_sum {κ : Type*} (s : Finset κ) (P : Matrix σ σ ℤ) (w : κ → σ → V) :
    mvG P (fun β => ∑ i ∈ s, w i β) = fun α => ∑ i ∈ s, mvG P (w i) α := by
  funext α
  simp only [mvG, smul_sum]
  exact sum_comm

theorem mvG_one [DecidableEq σ] (w : σ → V) : mvG (1 : Matrix σ σ ℤ) w = w := by
  funext α
  simp [mvG, Matrix.one_apply]

end generic

/-! ## Six dimensions -/

set_option maxRecDepth 1000000

theorem qI_transpose_C : qI.transpose * chargeC6 = -(chargeC6 * qI) := by decide +kernel
theorem qJ_transpose_C : qJ.transpose * chargeC6 = -(chargeC6 * qJ) := by decide +kernel
theorem qK_transpose_C : qK.transpose * chargeC6 = -(chargeC6 * qK) := by decide +kernel
theorem Γ7_qI : Γ7 * qI = qI * Γ7 := by decide +kernel
theorem Γ7_qJ : Γ7 * qJ = qJ * Γ7 := by decide +kernel
theorem Γ7_qK : Γ7 * qK = qK * Γ7 := by decide +kernel

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [SuperCalc (Fin 6) R M]

local notation "pr" => (SuperCalc.pair : M →ₗ[R] M →ₗ[R] R)

/-- A six-dimensional spinor of odd fields: 16 real components. -/
abbrev Spinor6 (M : Type*) := Fin 16 → M

/-- A chiral spinor. -/
def IsChiral (ψ : Spinor6 M) : Prop := mvG Γ7 ψ = ψ

/-- The bilinear `ψ̄ N χ = ψᵀ C N χ`. -/
def bar6 (N : Mat16) (ψ χ : Spinor6 M) : R := sbilG pr (chargeC6 * N) ψ χ

theorem flip6 (N : Mat16) (ψ χ : Spinor6 M) :
    sbilG pr N ψ χ = -sbilG pr N.transpose χ ψ :=
  sbilG_flip pr N ψ χ pr (SuperCalc.pair_antisymm (ι := Fin 6))

/-- `ψ̄ χ = χ̄ ψ` for odd spinors. -/
theorem bar6_one_symm (ψ χ : Spinor6 M) : bar6 1 ψ χ = bar6 1 χ ψ := by
  rw [bar6, bar6, flip6, mul_one, C6_transpose, sbilG_neg_mat, neg_neg]

/-- `ψ̄ Γ^a χ = -χ̄ Γ^a ψ` for odd spinors. -/
theorem bar6_Γ_antisymm (a : Fin 6) (ψ χ : Spinor6 M) :
    bar6 (Γ a) ψ χ = -bar6 (Γ a) χ ψ := by
  rw [bar6, bar6, flip6, C6Γ_transpose]

/-- `ψ̄ I χ = -χ̄ I ψ` for odd spinors, and likewise for `J`, `K`. -/
theorem bar6_qI_antisymm (ψ χ : Spinor6 M) : bar6 qI ψ χ = -bar6 qI χ ψ := by
  rw [bar6, bar6, flip6, C6qI_transpose]

theorem bar6_qJ_antisymm (ψ χ : Spinor6 M) : bar6 qJ ψ χ = -bar6 qJ χ ψ := by
  rw [bar6, bar6, flip6, C6qJ_transpose]

/-- `ψ̄ I Γ^a χ = χ̄ I Γ^a ψ` for odd spinors. -/
theorem bar6_qIΓ_symm (a : Fin 6) (ψ χ : Spinor6 M) :
    bar6 (qI * Γ a) ψ χ = bar6 (qI * Γ a) χ ψ := by
  rw [bar6, bar6, flip6, ← Matrix.mul_assoc, C6qIΓ_transpose, sbilG_neg_mat, neg_neg]

/-- Leibniz rule for the six-dimensional bilinears. -/
theorem dR_bar6 (i : Fin 6) (N : Mat16) (ψ χ : Spinor6 M) :
    SuperCalc.dR (M := M) i (bar6 N ψ χ) =
      bar6 N (fun α => SuperCalc.dM i (ψ α)) χ + bar6 N ψ (fun β => SuperCalc.dM i (χ β)) :=
  sbilG_deriv pr (chargeC6 * N) ψ χ (SuperCalc.dR (M := M) i) pr pr
    (SuperCalc.dM i) (SuperCalc.dM i) (SuperCalc.dR_pair i)

/-! ## (2,0): a pair of spinors and the R-symmetry `Sp(4)` -/

/-- A (2,0) spinor: two 16-component spinors, i.e. a spinor with values in `ℍ²`. -/
abbrev Spinor20 (M : Type*) := Fin 2 → Fin 16 → M

/-- The `Sp(4)`-invariant pairing with coefficient matrix `N` on the spinor index. -/
def pairing20 (N : Mat16) (ψ χ : Spinor20 M) : R := ∑ A, sbilG pr N (ψ A) (χ A)

/-- The action of `E ⊗ q` on a (2,0) spinor. -/
def rAct (E : Matrix (Fin 2) (Fin 2) ℤ) (q : Mat16) (ψ : Spinor20 M) : Spinor20 M :=
  fun A α => ∑ B, E A B • mvG q (ψ B) α

/-- The ten generators of `Sp(4)`: anti-Hermitian `2 × 2` quaternionic matrices. -/
def sp4Gen : Fin 10 → Matrix (Fin 2) (Fin 2) ℤ × Mat16 :=
  ![(!![1, 0; 0, 0], qI), (!![1, 0; 0, 0], qJ), (!![1, 0; 0, 0], qK),
    (!![0, 0; 0, 1], qI), (!![0, 0; 0, 1], qJ), (!![0, 0; 0, 1], qK),
    (!![0, 1; -1, 0], 1),
    (!![0, 1; 1, 0], qI), (!![0, 1; 1, 0], qJ), (!![0, 1; 1, 0], qK)]

theorem sp4Gen_skew : ∀ (k : Fin 10) (A B : Fin 2),
    (sp4Gen k).1 A B • ((sp4Gen k).2.transpose * chargeC6)
      + (sp4Gen k).1 B A • (chargeC6 * (sp4Gen k).2) = 0 := by decide +kernel

theorem sp4Gen_Γ7 : ∀ k : Fin 10, Γ7 * (sp4Gen k).2 = (sp4Gen k).2 * Γ7 := by decide +kernel

/-- A generator `E ⊗ q` that is skew for `C` leaves the pairing invariant. -/
theorem pairing20_invariant (E : Matrix (Fin 2) (Fin 2) ℤ) (q : Mat16)
    (h : ∀ A B, E A B • (q.transpose * chargeC6) + E B A • (chargeC6 * q) = 0)
    (ψ χ : Spinor20 M) :
    pairing20 chargeC6 (rAct E q ψ) χ + pairing20 chargeC6 ψ (rAct E q χ) = 0 := by
  have hr : ∀ (φ : Spinor20 M) (A : Fin 2),
      rAct E q φ A = fun α => ∑ B, E A B • mvG q (φ B) α := fun _ _ => rfl
  have h1 : pairing20 chargeC6 (rAct E q ψ) χ =
      ∑ A, ∑ B, E A B • sbilG pr (q.transpose * chargeC6) (ψ B) (χ A) := by
    simp only [pairing20, hr, sbilG_sum_left, sbilG_zsmul_left, sbilG_mv_left]
  have h2 : pairing20 chargeC6 ψ (rAct E q χ) =
      ∑ A, ∑ B, E B A • sbilG pr (chargeC6 * q) (ψ B) (χ A) := by
    simp only [pairing20, hr, sbilG_sum_right, sbilG_zsmul_right, sbilG_mv_right]
    exact sum_comm
  rw [h1, h2, ← sum_add_distrib]
  refine sum_eq_zero fun A _ => ?_
  rw [← sum_add_distrib]
  refine sum_eq_zero fun B _ => ?_
  rw [← sbilG_zsmul_mat, ← sbilG_zsmul_mat, ← sbilG_add_mat, h, sbilG_zero_mat]

/-- **The pairing of (2,0) spinors is `Sp(4)`-invariant.** -/
theorem pairing20_sp4 (k : Fin 10) (ψ χ : Spinor20 M) :
    pairing20 chargeC6 (rAct (sp4Gen k).1 (sp4Gen k).2 ψ) χ
      + pairing20 chargeC6 ψ (rAct (sp4Gen k).1 (sp4Gen k).2 χ) = 0 :=
  pairing20_invariant _ _ (sp4Gen_skew k) ψ χ

/-- **`Sp(4)` preserves chirality.** -/
theorem rAct_chiral (k : Fin 10) (ψ : Spinor20 M) (h : ∀ A, IsChiral (ψ A)) (A : Fin 2) :
    IsChiral (rAct (sp4Gen k).1 (sp4Gen k).2 ψ A) := by
  have e : ∀ B, mvG Γ7 (mvG (sp4Gen k).2 (ψ B)) = mvG (sp4Gen k).2 (ψ B) := by
    intro B
    rw [mvG_mvG, sp4Gen_Γ7, ← mvG_mvG, h B]
  show mvG Γ7 (fun α => ∑ B, (sp4Gen k).1 A B • mvG (sp4Gen k).2 (ψ B) α) =
    fun α => ∑ B, (sp4Gen k).1 A B • mvG (sp4Gen k).2 (ψ B) α
  rw [mvG_sum]
  simp only [mvG_zsmul, e]

end SYM6
