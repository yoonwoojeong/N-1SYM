import SYM.Theory

/-!
# Off-shell closure of the supersymmetry algebra

The commutator of two supersymmetry transformations of the vector multiplet is a translation
plus a gauge transformation, without using the equations of motion:

`[δ₁, δ₂] = ξ^σ ∂_σ + δ_gauge(ξ^σ A_σ)`, with `ξ^σ = 8 ε̄₂ γ^σ ε₁`.

`dsusy ε Φ Ψ` is the linearization of `Φ ↦ susy ε Φ` at `Φ` in the direction `Ψ`, so
`δ₁ (δ₂ Φ) = dsusy ε₂ Φ (susy ε₁ Φ)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace SYM
open SuperCalculus Finset Matrix

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [SuperCalculus R M]
variable {I : Type*} [Fintype I] (c : StructureConstants R M I)

local notation "dRM" => dR (R := R) (M := M)
local notation "pairRM" => (pair : M →ₗ[R] M →ₗ[R] R)

/-- The spinor `(γ^{ρσ} X_ρσ + 2 γ5 Y) ε`. -/
def spinorOf (X : Fin 4 → Fin 4 → I → R) (Y : I → R) (ε : Fin 4 → M) : Fin 4 → I → M :=
  fun α => ∑ ρ, ∑ σ, mv (γ2 ρ σ) (fun β => ms (X ρ σ) (ε β)) α
    + (2 : ℤ) • mv γ5 (fun β => ms Y (ε β)) α

theorem sbil_sm_spinorOf (N : Mat4) (ε₂ ε₁ : Fin 4 → M) (X : Fin 4 → Fin 4 → I → R)
    (Y : I → R) : sbil sm N ε₂ (spinorOf X Y ε₁) =
      ∑ ρ, ∑ σ, sbil pairRM (N * γ2 ρ σ) ε₂ ε₁ • X ρ σ
        + (2 : ℤ) • (sbil pairRM (N * γ5) ε₂ ε₁ • Y) := by
  have hs : spinorOf X Y ε₁ = fun α => ∑ ρ, ∑ σ, mv (γ2 ρ σ) (fun β => ms (X ρ σ) (ε₁ β)) α
      + (2 : ℤ) • mv γ5 (fun β => ms Y (ε₁ β)) α := rfl
  rw [hs, sbil_add_right, sbil_sum_right, sbil_zsmul_right]
  simp only [sbil_sum_right, sbil_mv_right, sbil_ms_right]

/-- Antisymmetrizing in the two supersymmetry parameters keeps the symmetric part of the
coefficient matrices. -/
theorem sbil_sm_spinorOf_comm (N : Mat4) (ε₂ ε₁ : Fin 4 → M) (X : Fin 4 → Fin 4 → I → R)
    (Y : I → R) : sbil sm N ε₂ (spinorOf X Y ε₁) - sbil sm N ε₁ (spinorOf X Y ε₂) =
      ∑ ρ, ∑ σ, sbil pairRM (N * γ2 ρ σ + (N * γ2 ρ σ).transpose) ε₂ ε₁ • X ρ σ
        + (2 : ℤ) • (sbil pairRM (N * γ5 + (N * γ5).transpose) ε₂ ε₁ • Y) := by
  have fl : ∀ P : Mat4, sbil pairRM P ε₁ ε₂ = -sbil pairRM P.transpose ε₂ ε₁ := fun P =>
    sbil_flip pairRM P ε₁ ε₂ pairRM pair_antisymm
  rw [sbil_sm_spinorOf, sbil_sm_spinorOf]
  simp only [fl, sbil_add_mat, add_smul, neg_smul, sum_add_distrib, sum_neg_distrib, smul_add,
    smul_neg]
  abel

theorem covO_spinorOf (A : Fin 4 → I → R) (μ : Fin 4) (X : Fin 4 → Fin 4 → I → R) (Y : I → R)
    {ε : Fin 4 → M} (hε : ∀ α, dM μ (ε α) = 0) (α : Fin 4) :
    covO c A μ (spinorOf X Y ε α) =
      spinorOf (fun ρ σ => covE c A μ (X ρ σ)) (covE c A μ Y) ε α := by
  simp only [spinorOf, covO_add, covO_sum, covO_zsmul, covO_mv, covO_ms c A μ (hε _)]

theorem η_mul_self : ∀ μ, η μ * η μ = 1 := by decide

/-- A cyclically symmetric scalar tensor contracted with a tensor obeying the Bianchi identity
vanishes. -/
theorem bianchi_contraction_smul (h3t : ∀ a : R, 3 * a = 0 → a = 0)
    (z : Fin 4 → Fin 4 → Fin 4 → R) (Y : Fin 4 → Fin 4 → Fin 4 → I → R)
    (hY : ∀ μ ρ σ, Y μ ρ σ + Y ρ σ μ + Y σ μ ρ = 0) (hz : ∀ μ ρ σ, z ρ σ μ = z μ ρ σ) :
    ∑ μ, ∑ ρ, ∑ σ, z μ ρ σ • Y μ ρ σ = 0 := by
  have s0 : ∑ μ, ∑ ρ, ∑ σ, z μ ρ σ • Y μ ρ σ = ∑ μ, ∑ ρ, ∑ σ, z μ ρ σ • Y σ μ ρ := by
    rw [sum_rot fun μ ρ σ => z μ ρ σ • Y μ ρ σ]
    exact sum_congr rfl fun μ _ => sum_congr rfl fun ρ _ => sum_congr rfl fun σ _ => by
      rw [hz ρ σ μ, hz μ ρ σ]
  have s1 : ∑ μ, ∑ ρ, ∑ σ, z μ ρ σ • Y μ ρ σ = ∑ μ, ∑ ρ, ∑ σ, z μ ρ σ • Y ρ σ μ := by
    rw [sum_rot' fun μ ρ σ => z μ ρ σ • Y μ ρ σ]
    exact sum_congr rfl fun μ _ => sum_congr rfl fun ρ _ => sum_congr rfl fun σ _ => by
      rw [hz μ ρ σ]
  have h3 : (3 : ℤ) • ∑ μ, ∑ ρ, ∑ σ, z μ ρ σ • Y μ ρ σ = 0 := by
    have e : (3 : ℤ) • ∑ μ, ∑ ρ, ∑ σ, z μ ρ σ • Y μ ρ σ =
        ∑ μ, ∑ ρ, ∑ σ, z μ ρ σ • (Y μ ρ σ + Y ρ σ μ + Y σ μ ρ) := by
      simp only [smul_add, sum_add_distrib]
      rw [← s0, ← s1]; abel
    rw [e]
    exact sum_eq_zero fun μ _ => sum_eq_zero fun ρ _ => sum_eq_zero fun σ _ => by
      rw [hY, smul_zero]
  funext a
  apply h3t
  have h := congrFun h3 a
  simpa using h

namespace Fields
variable (Φ Ψ : Fields R M I) (ε ε₁ ε₂ : Fin 4 → M)

/-- Linearization of the supersymmetry variation at `Φ` in the direction `Ψ`. -/
def dsusy : Fields R M I where
  A μ := -((2 * η μ) • sbil sm (Cγ μ) ε Ψ.lam)
  lam := spinorOf (Φ.dF c Ψ.A) Ψ.D ε
  D := (2 : ℤ) • ∑ μ, sbil sm (chargeC * γ5 * γ μ) ε (Φ.dDlam c Ψ μ)

/-- The translation vector `ξ^σ = 8 ε̄₂ γ^σ ε₁` of the commutator. -/
def xi (σ : Fin 4) : R := (8 : ℤ) • sbil pairRM (Cγ σ) ε₂ ε₁

theorem susy_lam_eq : (Φ.susy c ε).lam = spinorOf (Φ.F c) Φ.D ε := rfl

/-- **Closure on the gauge field:** `[δ₁, δ₂] A_μ = ξ^σ F_σμ`. -/
theorem closure_A (μ : Fin 4) :
    (Φ.dsusy c (Φ.susy c ε₁) ε₂).A μ - (Φ.dsusy c (Φ.susy c ε₂) ε₁).A μ =
      ∑ σ, xi ε₁ ε₂ σ • Φ.F c σ μ := by
  have h := sbil_sm_spinorOf_comm (Cγ μ) ε₂ ε₁ (Φ.F c) Φ.D
  have hA : ∀ ε ε', (Φ.dsusy c (Φ.susy c ε') ε).A μ =
      -((2 * η μ) • sbil sm (Cγ μ) ε (spinorOf (Φ.F c) Φ.D ε')) := fun _ _ => rfl
  have e : (Φ.dsusy c (Φ.susy c ε₁) ε₂).A μ - (Φ.dsusy c (Φ.susy c ε₂) ε₁).A μ =
      -((2 * η μ) • (sbil sm (Cγ μ) ε₂ (spinorOf (Φ.F c) Φ.D ε₁)
        - sbil sm (Cγ μ) ε₁ (spinorOf (Φ.F c) Φ.D ε₂))) := by
    rw [hA, hA, smul_sub]; abel
  rw [e, h, Cγγ5_symm, sbil_zero_mat, zero_smul, smul_zero, add_zero]
  have key : ∀ ρ σ, sbil pairRM (Cγ μ * γ2 ρ σ + (Cγ μ * γ2 ρ σ).transpose) ε₂ ε₁ • Φ.F c ρ σ =
      (2 * η μ) • ((if μ = ρ then sbil pairRM (Cγ σ) ε₂ ε₁ • Φ.F c ρ σ else 0)
        - (if μ = σ then sbil pairRM (Cγ ρ) ε₂ ε₁ • Φ.F c ρ σ else 0)) := fun ρ σ => by
    rw [Cγγ2_symm, sbil_zsmul_mat, sbil_sub_mat, sbil_zsmul_mat, sbil_zsmul_mat]
    split_ifs <;>
      simp only [one_smul, zero_smul, sub_zero, zero_sub, sub_self, smul_zero, smul_assoc,
        sub_smul, neg_smul, smul_neg]
  simp only [key, ← smul_sum, sum_sub_distrib]
  have a1 : ∑ ρ, ∑ σ, (if μ = ρ then sbil pairRM (Cγ σ) ε₂ ε₁ • Φ.F c ρ σ else 0) =
      -∑ σ, sbil pairRM (Cγ σ) ε₂ ε₁ • Φ.F c σ μ := by
    rw [sum_comm, ← sum_neg_distrib]
    refine sum_congr rfl fun σ _ => ?_
    rw [sum_ite_eq, if_pos (mem_univ _), F, F, fieldStrength_antisymm c Φ.A σ μ, smul_neg]
  have a2 : ∑ ρ, ∑ σ, (if μ = σ then sbil pairRM (Cγ ρ) ε₂ ε₁ • Φ.F c ρ σ else 0) =
      ∑ σ, sbil pairRM (Cγ σ) ε₂ ε₁ • Φ.F c σ μ :=
    sum_congr rfl fun ρ _ => by rw [sum_ite_eq, if_pos (mem_univ _)]
  rw [a1, a2, smul_smul]
  have hη : 2 * η μ * (2 * η μ) = 4 := by
    have := η_mul_self μ; linear_combination 4 * this
  rw [hη]
  simp only [xi, smul_assoc, ← smul_sum]
  module

end Fields

/-! ## Auxiliary field -/

section sums4
variable {P : Type*} [AddCommMonoid P] (h : Fin 4 → Fin 4 → Fin 4 → Fin 4 → P)

theorem sum4_pairs : ∑ a, ∑ b, ∑ d, ∑ e, h a b d e = ∑ a, ∑ b, ∑ d, ∑ e, h d e a b :=
  calc _ = ∑ a, ∑ d, ∑ b, ∑ e, h a b d e := sum_congr rfl fun _ _ => sum_comm
    _ = ∑ d, ∑ a, ∑ b, ∑ e, h a b d e := sum_comm
    _ = _ := sum_congr rfl fun d _ => sum_rot' fun a b e => h a b d e

theorem sum4_swap24 : ∑ a, ∑ b, ∑ d, ∑ e, h a b d e = ∑ a, ∑ b, ∑ d, ∑ e, h a e d b :=
  sum_congr rfl fun a _ => sum_swap13 fun b d e => h a b d e

end sums4

/-- The term of `[δ₁, δ₂] D` quadratic in the gaugino vanishes. -/
theorem aux_cubic_vanishes (ε₁ ε₂ : Fin 4 → M) (lam : Fin 4 → I → M) :
    ∑ μ, (sbil sm (chargeC * γ5 * γ μ) ε₂
          (fun β => act c (-((2 * η μ) • sbil sm (Cγ μ) ε₁ lam)) (lam β))
        - sbil sm (chargeC * γ5 * γ μ) ε₁
          (fun β => act c (-((2 * η μ) • sbil sm (Cγ μ) ε₂ lam)) (lam β))) = (0 : I → R) := by
  set U : Fin 4 → Fin 4 → Fin 4 → Fin 4 → I → R := fun γ' δ α β =>
    sm (ε₂ α) (act c (sm (ε₁ γ') (lam δ)) (lam β)) with hU
  have hE1 : ∀ μ, sbil sm (chargeC * γ5 * γ μ) ε₂
      (fun β => act c (-((2 * η μ) • sbil sm (Cγ μ) ε₁ lam)) (lam β)) =
      ∑ α, ∑ β, ∑ γ', ∑ δ,
        (-(2 * η μ * ((chargeC * γ5 * γ μ) α β * Cγ μ γ' δ))) • U γ' δ α β := by
    intro μ
    simp only [hU, sbil, map_neg, map_zsmul, map_sum, LinearMap.neg_apply, LinearMap.smul_apply,
      LinearMap.sum_apply, smul_neg, smul_sum, smul_smul, neg_smul, mul_assoc, mul_left_comm,
      sum_neg_distrib]
  have hE2 : ∀ μ, sbil sm (chargeC * γ5 * γ μ) ε₁
      (fun β => act c (-((2 * η μ) • sbil sm (Cγ μ) ε₂ lam)) (lam β)) =
      ∑ α, ∑ β, ∑ γ', ∑ δ,
        (2 * η μ * ((chargeC * γ5 * γ μ) γ' δ * Cγ μ α β)) • U γ' δ α β := by
    intro μ
    rw [sum4_pairs fun α β γ' δ =>
      (2 * η μ * ((chargeC * γ5 * γ μ) γ' δ * Cγ μ α β)) • U γ' δ α β]
    simp only [hU, sbil, map_neg, map_zsmul, map_sum, LinearMap.neg_apply, LinearMap.smul_apply,
      LinearMap.sum_apply, smul_neg, smul_sum, smul_smul, mul_assoc, mul_left_comm,
      sum_neg_distrib, sm_act_sm_antisymm c (ε₁ _) (ε₂ _) (lam _) (lam _), neg_neg]
  simp only [hE1, hE2, ← sum_sub_distrib, ← sub_smul]
  rw [sum_in4]
  simp only [← sum_smul]
  set W : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℤ := fun α β γ' δ =>
    ∑ μ, (-(2 * η μ * ((chargeC * γ5 * γ μ) α β * Cγ μ γ' δ))
      - 2 * η μ * ((chargeC * γ5 * γ μ) γ' δ * Cγ μ α β)) with hW
  have hsym : ∀ α β γ' δ, U γ' β α δ = U γ' δ α β := fun α β γ' δ => by
    simp only [hU]; exact sm_act_sm_symm c (ε₁ γ') (ε₂ α) (lam δ) (lam β)
  have key : ∀ α β γ' δ, W α β γ' δ + W α δ γ' β = 0 := fun α β γ' δ => by
    have h := fierz_aux α β γ' δ
    simp only [hW, ← sum_add_distrib]
    have h2 : (-2 : ℤ) * ((∑ μ, η μ * ((chargeC * γ5 * γ μ) α β * Cγ μ γ' δ
        + (chargeC * γ5 * γ μ) γ' δ * Cγ μ α β))
      + ∑ μ, η μ * ((chargeC * γ5 * γ μ) α δ * Cγ μ γ' β
        + (chargeC * γ5 * γ μ) γ' β * Cγ μ α δ)) = 0 := by rw [h, mul_zero]
    rw [← sum_add_distrib, mul_sum] at h2
    rw [← h2]
    exact sum_congr rfl fun μ _ => by ring
  have s0 : ∑ α, ∑ β, ∑ γ', ∑ δ, W α β γ' δ • U γ' δ α β =
      ∑ α, ∑ β, ∑ γ', ∑ δ, W α δ γ' β • U γ' δ α β := by
    rw [sum4_swap24 fun α β γ' δ => W α β γ' δ • U γ' δ α β]
    exact sum_congr rfl fun α _ => sum_congr rfl fun β _ => sum_congr rfl fun γ' _ =>
      sum_congr rfl fun δ _ => by rw [hsym]
  have h2 : (2 : ℤ) • ∑ α, ∑ β, ∑ γ', ∑ δ, W α β γ' δ • U γ' δ α β = 0 := by
    have e : (2 : ℤ) • ∑ α, ∑ β, ∑ γ', ∑ δ, W α β γ' δ • U γ' δ α β =
        ∑ α, ∑ β, ∑ γ', ∑ δ, (W α β γ' δ + W α δ γ' β) • U γ' δ α β := by
      simp only [add_smul, sum_add_distrib]
      rw [← s0]; abel
    rw [e]
    exact sum_eq_zero fun α _ => sum_eq_zero fun β _ => sum_eq_zero fun γ' _ =>
      sum_eq_zero fun δ _ => by rw [key, zero_smul]
  funext a
  apply two_torsion (M := M)
  have h := congrFun h2 a
  rw [Pi.smul_apply, zsmul_eq_mul, Int.cast_ofNat] at h
  exact h

namespace Fields
variable (Φ : Fields R M I) (ε₁ ε₂ : Fin 4 → M)

/-- **Closure on the auxiliary field:** `[δ₁, δ₂] D = ξ^σ D_σ D`. -/
theorem closure_D (h₁ : ∀ μ α, dM μ (ε₁ α) = 0) (h₂ : ∀ μ α, dM μ (ε₂ α) = 0) :
    (Φ.dsusy c (Φ.susy c ε₁) ε₂).D - (Φ.dsusy c (Φ.susy c ε₂) ε₁).D =
      ∑ σ, xi ε₁ ε₂ σ • covE c Φ.A σ Φ.D := by
  have hD : ∀ ε ε' : Fin 4 → M, (Φ.dsusy c (Φ.susy c ε') ε).D = (2 : ℤ) • ∑ μ,
      (sbil sm (chargeC * γ5 * γ μ) ε (fun β => covO c Φ.A μ (spinorOf (Φ.F c) Φ.D ε' β))
        + sbil sm (chargeC * γ5 * γ μ) ε
          (fun β => act c (-((2 * η μ) • sbil sm (Cγ μ) ε' Φ.lam)) (Φ.lam β))) := by
    intro ε ε'
    have h : (Φ.dsusy c (Φ.susy c ε') ε).D = (2 : ℤ) • ∑ μ, sbil sm (chargeC * γ5 * γ μ) ε
        (fun β => covO c Φ.A μ (spinorOf (Φ.F c) Φ.D ε' β)
          + act c (-((2 * η μ) • sbil sm (Cγ μ) ε' Φ.lam)) (Φ.lam β)) := rfl
    rw [h]; simp only [sbil_add_right]
  have hX : ∀ μ, sbil sm (chargeC * γ5 * γ μ) ε₂
        (fun β => covO c Φ.A μ (spinorOf (Φ.F c) Φ.D ε₁ β))
      - sbil sm (chargeC * γ5 * γ μ) ε₁
        (fun β => covO c Φ.A μ (spinorOf (Φ.F c) Φ.D ε₂ β)) =
      (2 : ℤ) • ∑ ρ, ∑ σ, sbil pairRM (chargeC * γ5 * γ3 μ ρ σ) ε₂ ε₁ •
          covE c Φ.A μ (Φ.F c ρ σ)
        + (4 : ℤ) • (sbil pairRM (Cγ μ) ε₂ ε₁ • covE c Φ.A μ Φ.D) := by
    intro μ
    simp only [covO_spinorOf c Φ.A μ _ _ (h₁ μ), covO_spinorOf c Φ.A μ _ _ (h₂ μ)]
    rw [sbil_sm_spinorOf_comm]
    simp only [Cγ5γγ2_symm, Cγ5γγ5_symm, sbil_zsmul_mat, smul_assoc, ← smul_sum, smul_smul]
    norm_num
  have hcub := aux_cubic_vanishes c ε₁ ε₂ Φ.lam
  have hB := bianchi_contraction_smul (three_torsion (M := M))
    (fun μ ρ σ => sbil pairRM (chargeC * γ5 * γ3 μ ρ σ) ε₂ ε₁)
    (fun μ ρ σ => covE c Φ.A μ (Φ.F c ρ σ))
    (fun μ ρ σ => bianchi c Φ.A μ ρ σ) (fun μ ρ σ => by rw [γ3_cyclic μ ρ σ])
  rw [hD, hD, ← smul_sub, ← sum_sub_distrib]
  have e : ∀ μ, (sbil sm (chargeC * γ5 * γ μ) ε₂
          (fun β => covO c Φ.A μ (spinorOf (Φ.F c) Φ.D ε₁ β))
        + sbil sm (chargeC * γ5 * γ μ) ε₂
          (fun β => act c (-((2 * η μ) • sbil sm (Cγ μ) ε₁ Φ.lam)) (Φ.lam β)))
      - (sbil sm (chargeC * γ5 * γ μ) ε₁
          (fun β => covO c Φ.A μ (spinorOf (Φ.F c) Φ.D ε₂ β))
        + sbil sm (chargeC * γ5 * γ μ) ε₁
          (fun β => act c (-((2 * η μ) • sbil sm (Cγ μ) ε₂ Φ.lam)) (Φ.lam β))) =
      ((2 : ℤ) • ∑ ρ, ∑ σ, sbil pairRM (chargeC * γ5 * γ3 μ ρ σ) ε₂ ε₁ •
          covE c Φ.A μ (Φ.F c ρ σ)
        + (4 : ℤ) • (sbil pairRM (Cγ μ) ε₂ ε₁ • covE c Φ.A μ Φ.D))
      + (sbil sm (chargeC * γ5 * γ μ) ε₂
          (fun β => act c (-((2 * η μ) • sbil sm (Cγ μ) ε₁ Φ.lam)) (Φ.lam β))
        - sbil sm (chargeC * γ5 * γ μ) ε₁
          (fun β => act c (-((2 * η μ) • sbil sm (Cγ μ) ε₂ Φ.lam)) (Φ.lam β))) := by
    intro μ; rw [← hX μ]; abel
  simp only [e, sum_add_distrib, hcub, add_zero, ← smul_sum, hB, smul_zero, zero_add, xi,
    smul_assoc, smul_smul]
  norm_num

end Fields
/-! ## Gaugino -/

/-- A product `ε₂ ε₁ ψ` of three odd spinors contracted with a coefficient tensor. -/
def tri (ε₂ ε₁ : Fin 4 → M) (ψ : Fin 4 → I → M) (w : Fin 4 → Fin 4 → Fin 4 → ℤ) : I → M :=
  ∑ β, ∑ γ', ∑ δ, w β γ' δ • (pair (ε₂ β) (ε₁ γ') • ψ δ)

section tri
variable (ε₂ ε₁ : Fin 4 → M) (ψ : Fin 4 → I → M) (w w' : Fin 4 → Fin 4 → Fin 4 → ℤ)

theorem tri_add : tri ε₂ ε₁ ψ (fun β γ' δ => w β γ' δ + w' β γ' δ) =
    tri ε₂ ε₁ ψ w + tri ε₂ ε₁ ψ w' := by
  simp only [tri, add_smul, sum_add_distrib]

theorem tri_zsmul (n : ℤ) : tri ε₂ ε₁ ψ (fun β γ' δ => n * w β γ' δ) = n • tri ε₂ ε₁ ψ w := by
  simp only [tri, mul_smul, smul_sum]

theorem tri_sum (v : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℤ) :
    tri ε₂ ε₁ ψ (fun β γ' δ => ∑ σ, v σ β γ' δ) = ∑ σ, tri ε₂ ε₁ ψ (v σ) := by
  simp only [tri, sum_smul]
  exact (sum_congr rfl fun β _ =>
    (sum_congr rfl fun γ' _ => sum_comm).trans sum_comm).trans sum_comm

/-- Exchanging the two parameters. -/
theorem tri_swap : tri ε₁ ε₂ ψ w = -tri ε₂ ε₁ ψ (fun β γ' δ => w γ' β δ) := by
  simp only [tri]
  rw [sum_comm, ← sum_neg_distrib]
  refine sum_congr rfl fun β _ => ?_
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun γ' _ => ?_
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun δ _ => ?_
  rw [pair_antisymm (ε₁ γ') (ε₂ β), neg_smul, smul_neg]

theorem tri_diag (N : Mat4) (α : Fin 4) :
    tri ε₂ ε₁ ψ (fun β γ' δ => 8 * (N β γ' * if α = δ then 1 else 0)) =
      ((8 : ℤ) • sbil pairRM N ε₂ ε₁) • ψ α := by
  simp only [tri, sbil, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, sum_ite_eq, mem_univ,
    if_true, smul_sum, sum_smul, smul_assoc, mul_smul]

/-- The matrix `P` applied to the spinor `X ε`, as an additive function of `X`. -/
def mvms (P : Mat4) (ε : Fin 4 → M) (α : Fin 4) : (I → R) →+ (I → M) where
  toFun X := mv P (fun β => ms X (ε β)) α
  map_zero' := by simp [mv]
  map_add' X Y := by simp [mv, smul_add, sum_add_distrib]

theorem mvms_sbil (P N : Mat4) (α : Fin 4) :
    mvms P ε₂ α (sbil sm N ε₁ ψ : I → R) = tri ε₂ ε₁ ψ (fun β γ' δ => P α β * N γ' δ) := by
  simp only [mvms, AddMonoidHom.coe_mk, ZeroHom.coe_mk, mv, sbil, tri, map_sum, map_zsmul,
    ms_sm, smul_sum, smul_smul]
  refine (sum_rot' _).trans ?_
  refine sum_congr rfl fun β _ => sum_congr rfl fun γ' _ => sum_congr rfl fun δ _ => ?_
  rw [mul_comm]

end tri

namespace Fields
variable (Φ : Fields R M I) (ε₁ ε₂ : Fin 4 → M)

/-- `δ₁ (δ₂ λ)` as a contraction of `ε₂ ε₁ D_ρ λ`. -/
theorem dsusy_lam (h₁ : ∀ μ α, dM μ (ε₁ α) = 0) (α : Fin 4) :
    (Φ.dsusy c (Φ.susy c ε₁) ε₂).lam α =
      ∑ ρ, tri ε₂ ε₁ (Φ.Dlam c ρ) (closureW ρ α) := by
  have hl : (Φ.dsusy c (Φ.susy c ε₁) ε₂).lam α =
      ∑ ρ, ∑ σ, mvms (γ2 ρ σ) ε₂ α (Φ.dF c (Φ.susy c ε₁).A ρ σ)
        + (2 : ℤ) • mvms γ5 ε₂ α (Φ.susy c ε₁).D := rfl
  have hD : (Φ.susy c ε₁).D =
      (2 : ℤ) • ∑ μ, sbil sm (chargeC * γ5 * γ μ) ε₁ (Φ.Dlam c μ) := rfl
  have hW : ∀ ρ, tri ε₂ ε₁ (Φ.Dlam c ρ) (closureW ρ α) =
      ∑ σ, (-(4 * η σ)) • tri ε₂ ε₁ (Φ.Dlam c ρ) (fun β γ' δ => γ2 ρ σ α β * Cγ σ γ' δ)
        + (4 : ℤ) • tri ε₂ ε₁ (Φ.Dlam c ρ)
            (fun β γ' δ => γ5 α β * (chargeC * γ5 * γ ρ) γ' δ) := by
    intro ρ
    have e : closureW ρ α = fun β γ' δ =>
        (∑ σ, (-(4 * η σ)) * (γ2 ρ σ α β * Cγ σ γ' δ))
          + 4 * (γ5 α β * (chargeC * γ5 * γ ρ) γ' δ) := by
      funext β γ' δ
      simp only [closureW, mul_sum]
      congr 1
      exact sum_congr rfl fun σ _ => by ring
    rw [e, tri_add, tri_sum, tri_zsmul]
    simp only [tri_zsmul]
  have hanti : ∀ ρ σ, tri ε₂ ε₁ (Φ.Dlam c σ) (fun β γ' δ => γ2 ρ σ α β * Cγ ρ γ' δ) =
      -tri ε₂ ε₁ (Φ.Dlam c σ) (fun β γ' δ => γ2 σ ρ α β * Cγ ρ γ' δ) := by
    intro ρ σ
    have e : (fun β γ' δ => γ2 ρ σ α β * Cγ ρ γ' δ) =
        fun β γ' δ => (-1 : ℤ) * (γ2 σ ρ α β * Cγ ρ γ' δ) := by
      funext β γ' δ; rw [γ2_antisymm σ ρ, Matrix.neg_apply]; ring
    rw [e, tri_zsmul, neg_one_smul]
  obtain ⟨t, ht⟩ : ∃ t : Fin 4 → Fin 4 → I → M, ∀ ρ σ, t ρ σ =
      tri ε₂ ε₁ (Φ.Dlam c ρ) (fun β γ' δ => γ2 ρ σ α β * Cγ σ γ' δ) := ⟨_, fun _ _ => rfl⟩
  have e : ∀ ρ σ, mvms (γ2 ρ σ) ε₂ α (Φ.dF c (Φ.susy c ε₁).A ρ σ) =
      -((2 * η σ) • t ρ σ) - (2 * η ρ) • t σ ρ := by
    intro ρ σ
    rw [dF, covE_susyA c Φ ε₁ h₁, covE_susyA c Φ ε₁ h₁, map_sub, map_neg, map_neg, map_zsmul,
      map_zsmul, mvms_sbil, mvms_sbil, hanti, ← ht, ← ht]
    simp only [smul_neg]; abel
  have T1 : ∑ ρ, ∑ σ, mvms (γ2 ρ σ) ε₂ α (Φ.dF c (Φ.susy c ε₁).A ρ σ) =
      ∑ ρ, ∑ σ, (-(4 * η σ)) • t ρ σ := by
    simp only [e, sum_sub_distrib, sum_neg_distrib]
    rw [sum_comm (f := fun ρ σ => (2 * η ρ) • t σ ρ)]
    simp only [← sum_neg_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun ρ _ => sum_congr rfl fun σ _ => ?_
    module
  have T2 : (2 : ℤ) • mvms γ5 ε₂ α (Φ.susy c ε₁).D = ∑ ρ, (4 : ℤ) • tri ε₂ ε₁ (Φ.Dlam c ρ)
      (fun β γ' δ => γ5 α β * (chargeC * γ5 * γ ρ) γ' δ) := by
    rw [hD, map_zsmul, map_sum]
    simp only [mvms_sbil, smul_sum, smul_smul]
    norm_num
  rw [hl, T1, T2]
  simp only [hW, ← ht, sum_add_distrib]

/-- **Closure on the gaugino:** `[δ₁, δ₂] λ = ξ^σ D_σ λ`. -/
theorem closure_lam (h₁ : ∀ μ α, dM μ (ε₁ α) = 0) (h₂ : ∀ μ α, dM μ (ε₂ α) = 0) (α : Fin 4) :
    (Φ.dsusy c (Φ.susy c ε₁) ε₂).lam α - (Φ.dsusy c (Φ.susy c ε₂) ε₁).lam α =
      ∑ σ, xi ε₁ ε₂ σ • Φ.Dlam c σ α := by
  rw [dsusy_lam c Φ ε₁ ε₂ h₁, dsusy_lam c Φ ε₂ ε₁ h₂, ← sum_sub_distrib]
  refine sum_congr rfl fun ρ _ => ?_
  rw [tri_swap ε₂ ε₁, sub_neg_eq_add, ← tri_add]
  have e : (fun β γ' δ => closureW ρ α β γ' δ + closureW ρ α γ' β δ) =
      fun β γ' δ => 8 * (Cγ ρ β γ' * if α = δ then 1 else 0) := by
    funext β γ' δ; exact fierz_closure ρ α β γ' δ
  rw [e, tri_diag]
  rfl

end Fields
end SYM
