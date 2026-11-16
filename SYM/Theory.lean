import SYM.Spinor

/-!
# Classical `N = 1` super Yang–Mills theory

The off-shell vector multiplet `(A_μ, λ, D)`, its Lagrangian, the supersymmetry
transformation, and the proof that the Lagrangian is supersymmetric up to a total derivative.

## Conventions

Signature `(+,+,+,-)`, real Majorana spinors, `λ̄ = λᵀ C`. To keep all coefficients integral
the Lagrangian is four times the textbook one and the supersymmetry parameter is one quarter
of the textbook one:

* `lagrangian = -F_μν F^μν - 2 λ̄ γ^μ D_μ λ + 2 D²  = 4 · (-¼ F² - ½ λ̄ γ^μ D_μ λ + ½ D²)`,
* `δA_μ = -2 ε̄ γ_μ λ`, `δλ = (γ^{ρσ} F_ρσ + 2 γ5 D) ε`, `δD = 2 ε̄ γ5 γ^μ D_μ λ`,

which are `δA_μ = -½ ε̄' γ_μ λ`, `δλ = (¼ γ^{ρσ} F_ρσ + ½ γ5 D) ε'`, `δD = ½ ε̄' γ5 γ^μ D_μ λ`
for `ε' = 4 ε`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace SYM
open SuperCalculus Finset Matrix

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [SuperCalculus R M]
variable {I : Type*} [Fintype I] (c : StructureConstants R M I)

local notation "dRM" => dR (R := R) (M := M)

/-- A configuration of the vector multiplet, or a variation of one. -/
structure Fields (R M I : Type*) where
  /-- The gauge potential `A_μ`. -/
  A : Fin 4 → I → R
  /-- The gaugino `λ_α`, a Majorana spinor of odd adjoint fields. -/
  lam : Fin 4 → I → M
  /-- The auxiliary field `D`. -/
  D : I → R

namespace Fields
variable (Φ Ψ : Fields R M I)

/-- The field strength of the configuration. -/
def F (μ ν : Fin 4) : I → R := fieldStrength c Φ.A μ ν

/-- The covariant derivative `D_μ λ` of the gaugino. -/
def Dlam (μ : Fin 4) : Fin 4 → I → M := fun β => covO c Φ.A μ (Φ.lam β)

/-- The Lagrangian `-F_μν F^μν - 2 λ̄ γ^μ D_μ λ + 2 D²`. -/
def lagrangian : R :=
  -(∑ μ, ∑ ν, (η μ * η ν) • ip (Φ.F c μ ν) (Φ.F c μ ν))
    - (2 : ℤ) • ∑ μ, sbil opair (Cγ μ) Φ.lam (Φ.Dlam c μ)
    + (2 : ℤ) • ip Φ.D Φ.D

/-- First variation of the field strength, `δF_μν = D_μ δA_ν - D_ν δA_μ`. -/
def dF (a : Fin 4 → I → R) (μ ν : Fin 4) : I → R := covE c Φ.A μ (a ν) - covE c Φ.A ν (a μ)

/-- First variation of `D_μ λ`. -/
def dDlam (μ : Fin 4) : Fin 4 → I → M :=
  fun β => covO c Φ.A μ (Ψ.lam β) + act c (Ψ.A μ) (Φ.lam β)

/-- First variation of the Lagrangian at `Φ` in the direction `Ψ`. -/
def dLagrangian : R :=
  -(∑ μ, ∑ ν, (η μ * η ν) • ((2 : ℤ) • ip (Φ.F c μ ν) (Φ.dF c Ψ.A μ ν)))
    - (2 : ℤ) • ∑ μ, (sbil opair (Cγ μ) Ψ.lam (Φ.Dlam c μ)
        + sbil opair (Cγ μ) Φ.lam (Φ.dDlam c Ψ μ))
    + (4 : ℤ) • ip Φ.D Ψ.D

/-- The supersymmetry variation with parameter `ε`. -/
def susy (ε : Fin 4 → M) : Fields R M I where
  A μ := -((2 * η μ) • sbil sm (Cγ μ) ε Φ.lam)
  lam := fun α => ∑ ρ, ∑ σ, mv (γ2 ρ σ) (fun β => ms (Φ.F c ρ σ) (ε β)) α
    + (2 : ℤ) • mv γ5 (fun β => ms Φ.D (ε β)) α
  D := (2 : ℤ) • ∑ μ, sbil sm (chargeC * γ5 * γ μ) ε (Φ.Dlam c μ)

/-- The current whose divergence is the supersymmetry variation of the Lagrangian. -/
def susyCurrent (ε : Fin 4 → M) (μ : Fin 4) : R :=
  -((2 : ℤ) • sbil opair (Cγ μ) Φ.lam (Φ.susy c ε).lam)
    + (4 : ℤ) • ∑ ρ, ∑ σ, ip (Φ.F c ρ σ) (sbil sm (chargeC * γ3 ρ σ μ) ε Φ.lam)

end Fields

/-! ## Two cancellations -/

theorem sum_in4 {P : Type*} [AddCommMonoid P] (h : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → P) :
    ∑ i, ∑ a, ∑ b, ∑ d, ∑ e, h i a b d e = ∑ a, ∑ b, ∑ d, ∑ e, ∑ i, h i a b d e := by
  rw [sum_comm]; refine sum_congr rfl fun a _ => ?_
  rw [sum_comm]; refine sum_congr rfl fun b _ => ?_
  rw [sum_comm]; refine sum_congr rfl fun d _ => ?_
  rw [sum_comm]

/-- The cubic gaugino term vanishes: the Fierz identity together with total antisymmetry of
the structure constants. -/
theorem cubic_vanishes (ε : Fin 4 → M) (lam : Fin 4 → I → M) :
    ∑ μ, sbil opair (Cγ μ) lam
      (fun β => act c (-((2 * η μ) • sbil sm (Cγ μ) ε lam)) (lam β)) = (0 : R) := by
  have hE : ∀ μ, sbil opair (Cγ μ) lam
      (fun β => act c (-((2 * η μ) • sbil sm (Cγ μ) ε lam)) (lam β)) =
      ∑ α, ∑ β, ∑ γ', ∑ δ, (-(2 * η μ * (Cγ μ α β * Cγ μ γ' δ))) •
        T3 c (lam α) (ε γ') (lam δ) (lam β) := by
    intro μ
    simp only [sbil, T3, map_neg, map_zsmul, map_sum, LinearMap.neg_apply, LinearMap.smul_apply,
      LinearMap.sum_apply, smul_neg, smul_sum, smul_smul, neg_smul, mul_assoc, mul_left_comm,
      sum_neg_distrib]
  simp only [hE]
  rw [sum_in4]
  -- bring the index of `ε` outside
  rw [sum_rot' fun α β γ' => ∑ δ, ∑ μ, (-(2 * η μ * (Cγ μ α β * Cγ μ γ' δ))) •
    T3 c (lam α) (ε γ') (lam δ) (lam β)]
  refine sum_eq_zero fun γ' _ => ?_
  simp only [← sum_smul]
  set H : Fin 4 → Fin 4 → Fin 4 → ℤ := fun α β δ => ∑ μ, -(2 * η μ * (Cγ μ α β * Cγ μ γ' δ))
    with hH
  set x : Fin 4 → Fin 4 → Fin 4 → R := fun α β δ => T3 c (lam α) (ε γ') (lam δ) (lam β) with hx
  have hx1 : ∀ α β δ, x δ α β = x α β δ := fun α β δ => by
    simp only [hx]; rw [T3_swap13, T3_swap23]
  have hx2 : ∀ α β δ, x β δ α = x α β δ := fun α β δ => by
    simp only [hx]; rw [T3_swap23, T3_swap13]
  have key : ∀ α β δ, H α β δ + H δ α β + H β δ α = 0 := fun α β δ => by
    have h := fierz_cubic α β γ' δ
    simp only [hH, ← sum_add_distrib]
    rw [← neg_eq_zero, ← sum_neg_distrib]
    have h2 : (2 : ℤ) * ∑ μ, η μ * (Cγ μ α β * Cγ μ γ' δ + Cγ μ δ α * Cγ μ γ' β
        + Cγ μ β δ * Cγ μ γ' α) = 0 := by rw [h, mul_zero]
    rw [mul_sum] at h2
    rw [← h2]
    exact sum_congr rfl fun μ _ => by ring
  have s0 : ∑ α, ∑ β, ∑ δ, H α β δ • x α β δ = ∑ α, ∑ β, ∑ δ, H δ α β • x α β δ := by
    rw [sum_rot fun α β δ => H α β δ • x α β δ]
    exact sum_congr rfl fun α _ => sum_congr rfl fun β _ => sum_congr rfl fun δ _ => by
      rw [hx1]
  have s1 : ∑ α, ∑ β, ∑ δ, H α β δ • x α β δ = ∑ α, ∑ β, ∑ δ, H β δ α • x α β δ := by
    rw [sum_rot' fun α β δ => H α β δ • x α β δ]
    exact sum_congr rfl fun α _ => sum_congr rfl fun β _ => sum_congr rfl fun δ _ => by
      rw [hx2]
  apply three_torsion (M := M)
  have h3 : (3 : R) * ∑ α, ∑ β, ∑ δ, H α β δ • x α β δ =
      ∑ α, ∑ β, ∑ δ, (H α β δ + H δ α β + H β δ α) • x α β δ := by
    simp only [add_smul, sum_add_distrib]
    rw [← s0, ← s1]; ring
  rw [h3]
  exact sum_eq_zero fun α _ => sum_eq_zero fun β _ => sum_eq_zero fun δ _ => by
    rw [key, zero_smul]

/-- A cyclically symmetric tensor contracted with a tensor obeying the Bianchi identity
vanishes. -/
theorem bianchi_contraction (h3t : ∀ a : R, 3 * a = 0 → a = 0)
    (Y T : Fin 4 → Fin 4 → Fin 4 → I → R)
    (hY : ∀ μ ρ σ, Y μ ρ σ + Y ρ σ μ + Y σ μ ρ = 0) (hT : ∀ ρ σ μ, T σ μ ρ = T ρ σ μ) :
    ∑ μ, ∑ ρ, ∑ σ, ip (Y μ ρ σ) (T ρ σ μ) = 0 := by
  have s0 : ∑ μ, ∑ ρ, ∑ σ, ip (Y μ ρ σ) (T ρ σ μ) = ∑ μ, ∑ ρ, ∑ σ, ip (Y σ μ ρ) (T ρ σ μ) := by
    rw [sum_rot fun μ ρ σ => ip (Y μ ρ σ) (T ρ σ μ)]
    exact sum_congr rfl fun μ _ => sum_congr rfl fun ρ _ => sum_congr rfl fun σ _ => by
      rw [← hT ρ σ μ, ← hT σ μ ρ]
  have s1 : ∑ μ, ∑ ρ, ∑ σ, ip (Y μ ρ σ) (T ρ σ μ) = ∑ μ, ∑ ρ, ∑ σ, ip (Y ρ σ μ) (T ρ σ μ) := by
    rw [sum_rot' fun μ ρ σ => ip (Y μ ρ σ) (T ρ σ μ)]
    exact sum_congr rfl fun μ _ => sum_congr rfl fun ρ _ => sum_congr rfl fun σ _ => by
      rw [hT ρ σ μ]
  apply h3t
  have h3 : (3 : R) * ∑ μ, ∑ ρ, ∑ σ, ip (Y μ ρ σ) (T ρ σ μ) =
      ∑ μ, ∑ ρ, ∑ σ, ip (Y μ ρ σ + Y ρ σ μ + Y σ μ ρ) (T ρ σ μ) := by
    simp only [map_add, LinearMap.add_apply, sum_add_distrib]
    rw [← s0, ← s1]; ring
  rw [h3]
  exact sum_eq_zero fun μ _ => sum_eq_zero fun ρ _ => sum_eq_zero fun σ _ => by
    rw [hY, map_zero, LinearMap.zero_apply]

/-! ## Supersymmetry of the Lagrangian -/

namespace Fields
variable (Φ : Fields R M I) (ε : Fin 4 → M)

/-- `F_μν · ε̄ γ^ν D_μ λ`. -/
def auxP (μ ν : Fin 4) : R := ip (Φ.F c μ ν) (sbil sm (Cγ ν) ε (Φ.Dlam c μ))

/-- `F_ρσ · ε̄ γ^{ρσμ} D_μ λ`. -/
def auxQ (ρ σ μ : Fin 4) : R :=
  ip (Φ.F c ρ σ) (sbil sm (chargeC * γ3 ρ σ μ) ε (Φ.Dlam c μ))

/-- `D · ε̄ γ5 γ^μ D_μ λ`. -/
def auxS (μ : Fin 4) : R := ip Φ.D (sbil sm (chargeC * γ5 * γ μ) ε (Φ.Dlam c μ))

theorem covE_susyA (hε : ∀ μ α, dM μ (ε α) = 0) (μ ν : Fin 4) :
    covE c Φ.A μ ((Φ.susy c ε).A ν) = -((2 * η ν) • sbil sm (Cγ ν) ε (Φ.Dlam c μ)) := by
  have hA : (Φ.susy c ε).A ν = -((2 * η ν) • sbil sm (Cγ ν) ε Φ.lam) := rfl
  rw [hA, covE_neg, covE_zsmul, covE_sbil_sm (Cγ ν) c Φ.A μ (hε μ)]
  rfl

theorem ip_F_dF_susy (hε : ∀ μ α, dM μ (ε α) = 0) (μ ν : Fin 4) :
    ip (Φ.F c μ ν) (Φ.dF c (Φ.susy c ε).A μ ν) =
      -((2 * η ν) • Φ.auxP c ε μ ν) - (2 * η μ) • Φ.auxP c ε ν μ := by
  have e : ip (Φ.F c μ ν) (sbil sm (Cγ μ) ε (Φ.Dlam c ν)) = -Φ.auxP c ε ν μ := by
    rw [auxP, F, F, fieldStrength_antisymm c Φ.A ν μ, map_neg, LinearMap.neg_apply]
  rw [dF, covE_susyA c Φ ε hε, covE_susyA c Φ ε hε]
  simp only [map_sub, map_neg, map_zsmul]
  rw [e]; simp only [auxP, smul_neg]; abel

theorem sbil_susyLam (ψ : Fin 4 → I → M) (N : Mat4) :
    sbil opair N (Φ.susy c ε).lam ψ =
      ∑ ρ, ∑ σ, ip (Φ.F c ρ σ) (sbil sm ((γ2 ρ σ).transpose * N) ε ψ)
        + (2 : ℤ) • ip Φ.D (sbil sm (γ5.transpose * N) ε ψ) := by
  have hl : (Φ.susy c ε).lam = fun α =>
      ∑ ρ, ∑ σ, mv (γ2 ρ σ) (fun β => ms (Φ.F c ρ σ) (ε β)) α
        + (2 : ℤ) • mv γ5 (fun β => ms Φ.D (ε β)) α := rfl
  rw [hl, sbil_add_left, sbil_sum_left, sbil_zsmul_left]
  simp only [sbil_sum_left, sbil_mv_left, sbil_ms_left]

theorem kinetic_susy (μ : Fin 4) :
    sbil opair (Cγ μ) (Φ.susy c ε).lam (Φ.Dlam c μ) =
      -(∑ ρ, ∑ σ, (Φ.auxQ c ε ρ σ μ + (if σ = μ then η σ else 0) • (-Φ.auxP c ε σ ρ)
          - (if ρ = μ then η ρ else 0) • Φ.auxP c ε ρ σ))
        + (2 : ℤ) • Φ.auxS c ε μ := by
  have m1 : ∀ ρ σ, (γ2 ρ σ).transpose * Cγ μ = -(chargeC * γ2 ρ σ * γ μ) := fun ρ σ => by
    rw [Cγ, ← Matrix.mul_assoc, γ2_transpose_C, Matrix.neg_mul]
  have m2 : γ5.transpose * Cγ μ = chargeC * γ5 * γ μ := by
    rw [Cγ, ← Matrix.mul_assoc, γ5_transpose_C]
  rw [sbil_susyLam, m2]
  simp only [m1, sbil_neg_mat, map_neg, sum_neg_distrib]
  congr 2
  refine sum_congr rfl fun ρ _ => sum_congr rfl fun σ _ => ?_
  rw [Cγ2γ, sbil_sub_mat, sbil_add_mat, sbil_zsmul_mat, sbil_zsmul_mat, map_sub, map_add,
    map_zsmul, map_zsmul]
  have e1 : (if σ = μ then η σ else 0) • ip (Φ.F c ρ σ) (sbil sm (Cγ ρ) ε (Φ.Dlam c μ)) =
      (if σ = μ then η σ else 0) • (-Φ.auxP c ε σ ρ) := by
    split_ifs with h
    · subst h
      rw [auxP, F, F, fieldStrength_antisymm c Φ.A σ ρ, map_neg, LinearMap.neg_apply]
    · simp
  have e2 : (if ρ = μ then η ρ else 0) • ip (Φ.F c ρ σ) (sbil sm (Cγ σ) ε (Φ.Dlam c μ)) =
      (if ρ = μ then η ρ else 0) • Φ.auxP c ε ρ σ := by
    split_ifs with h
    · subst h; rfl
    · simp
  rw [e1, e2]; rfl

theorem kinetic_dDlam (μ : Fin 4) :
    sbil opair (Cγ μ) Φ.lam (Φ.dDlam c (Φ.susy c ε) μ) =
      dRM μ (sbil opair (Cγ μ) Φ.lam (Φ.susy c ε).lam)
        + sbil opair (Cγ μ) (Φ.susy c ε).lam (Φ.Dlam c μ)
        + sbil opair (Cγ μ) Φ.lam (fun β => act c ((Φ.susy c ε).A μ) (Φ.lam β)) := by
  have d := sbil_deriv (opair : (I → M) →ₗ[R] (I → M) →ₗ[R] R) (Cγ μ) Φ.lam (Φ.susy c ε).lam
    (dRM μ) opair opair (covO c Φ.A μ) (covO c Φ.A μ) (dR_opair_cov c Φ.A μ)
  have fl := sbil_flip (opair : (I → M) →ₗ[R] (I → M) →ₗ[R] R) (Cγ μ)
    (fun α => covO c Φ.A μ (Φ.lam α)) (Φ.susy c ε).lam opair opair_antisymm
  rw [Cγ_transpose] at fl
  rw [fl] at d
  have hd : Φ.dDlam c (Φ.susy c ε) μ = fun β =>
      covO c Φ.A μ ((Φ.susy c ε).lam β) + act c ((Φ.susy c ε).A μ) (Φ.lam β) := rfl
  have hDl : Φ.Dlam c μ = fun β => covO c Φ.A μ (Φ.lam β) := rfl
  rw [hd, sbil_add_right, d, hDl]
  abel

theorem dR_susyCurrent (hε : ∀ μ α, dM μ (ε α) = 0) (μ : Fin 4) :
    dRM μ (Φ.susyCurrent c ε μ) =
      -((2 : ℤ) • dRM μ (sbil opair (Cγ μ) Φ.lam (Φ.susy c ε).lam))
        + (4 : ℤ) • ∑ ρ, ∑ σ, (ip (covE c Φ.A μ (Φ.F c ρ σ))
            (sbil sm (chargeC * γ3 ρ σ μ) ε Φ.lam) + Φ.auxQ c ε ρ σ μ) := by
  simp only [susyCurrent, map_add, map_neg, map_zsmul, map_sum, dR_ip_cov c Φ.A,
    covE_sbil_sm _ c Φ.A μ (hε μ)]
  rfl

set_option maxHeartbeats 4000000 in
/-- **Supersymmetry of the `N = 1` super Yang–Mills Lagrangian.** For a constant odd spinor
`ε`, the first variation of the Lagrangian along the supersymmetry transformation is the
divergence of `susyCurrent`. -/
theorem susy_invariance (hε : ∀ μ α, dM μ (ε α) = 0) :
    Φ.dLagrangian c (Φ.susy c ε) = ∑ μ, dRM μ (Φ.susyCurrent c ε μ) := by
  have hcub := cubic_vanishes c ε Φ.lam
  have hB := bianchi_contraction (three_torsion (M := M))
    (fun μ ρ σ => covE c Φ.A μ (Φ.F c ρ σ))
    (fun ρ σ μ => sbil sm (chargeC * γ3 ρ σ μ) ε Φ.lam)
    (fun μ ρ σ => bianchi c Φ.A μ ρ σ) (fun ρ σ μ => by rw [γ3_cyclic])
  have hD : ip Φ.D (Φ.susy c ε).D = (2 : ℤ) • ∑ μ, Φ.auxS c ε μ := by
    have h : (Φ.susy c ε).D = (2 : ℤ) • ∑ μ, sbil sm (chargeC * γ5 * γ μ) ε (Φ.Dlam c μ) := rfl
    rw [h, map_zsmul, map_sum]; rfl
  have hA : ∀ μ, (Φ.susy c ε).A μ = -((2 * η μ) • sbil sm (Cγ μ) ε Φ.lam) := fun _ => rfl
  simp only [dLagrangian, ip_F_dF_susy c Φ ε hε, kinetic_dDlam, kinetic_susy, hD,
    dR_susyCurrent c Φ ε hε]
  simp only [hA] at *
  simp only [Fin.sum_univ_four] at hcub hB ⊢
  simp [η] at hcub hB ⊢
  linear_combination (-2 : R) * hcub - 4 * hB

end Fields
end SYM
