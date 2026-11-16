import SYM6.Color
import SYM6.Spinor6

/-!
# Super Yang–Mills in any dimension

The port of the field-theory layer (`SYM/Theory.lean`). The four-dimensional proof used the
gamma matrices only through a short list of identities; here they are abstracted as
`GammaData`, and the theorem holds for every spacetime index type `ι` and spinor index type
`σ` carrying such data.

`GammaData` asks for:

* `K μ`: the symmetric matrices of the bilinears `ψ̄ Γ^μ χ`;
* `G2 ρ σ`: the matrices `Γ^{ρσ}` acting on spinors, and `K3 ρ σ μ` those of `ψ̄ Γ^{ρσμ} χ`;
* `G2K`: `Γ^{ρσ} Γ^μ = Γ^{ρσμ} + Γ^ρ η^{σμ} - Γ^σ η^{ρμ}`, in bilinear form;
* `K3_cyclic`: cyclic symmetry of `Γ^{ρσμ}`;
* `fierz`: `(Γ_μ)_{α(β} (Γ^μ)_{γδ)} = 0`, which holds in dimensions 3, 4, 6 and 10.

The theory has a gauge field and an adjoint spinor, with no auxiliary field:

* `lagrangian = -F_μν F^μν - 2 λ̄ Γ^μ D_μ λ`,
* `δA_μ = -2 ε̄ Γ_μ λ`, `δλ = Γ^{ρσ} F_ρσ ε`.

`susy_invariance`: its first variation along supersymmetry is a divergence.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace SYM6
open SuperCalc Finset Matrix

/-- The gamma-matrix identities that make super Yang–Mills supersymmetric. -/
structure GammaData (ι σ : Type*) [Fintype ι] [DecidableEq ι] [Fintype σ] where
  /-- Diagonal of the metric. -/
  η : ι → ℤ
  /-- Matrices of the bilinears `ψ̄ Γ^μ χ`. -/
  K : ι → Matrix σ σ ℤ
  /-- The matrices `Γ^{ρσ}`. -/
  G2 : ι → ι → Matrix σ σ ℤ
  /-- Matrices of the bilinears `ψ̄ Γ^{ρσμ} χ`. -/
  K3 : ι → ι → ι → Matrix σ σ ℤ
  η_sq : ∀ μ, η μ * η μ = 1
  K_symm : ∀ μ, (K μ).transpose = K μ
  G2K : ∀ ρ σ' μ, (G2 ρ σ').transpose * K μ =
    -(K3 ρ σ' μ + (if σ' = μ then η σ' else 0) • K ρ - (if ρ = μ then η ρ else 0) • K σ')
  K3_cyclic : ∀ ρ σ' μ, K3 σ' μ ρ = K3 ρ σ' μ
  fierz : ∀ α β γ' δ : σ,
    ∑ μ, η μ * (K μ α β * K μ γ' δ + K μ δ α * K μ γ' β + K μ β δ * K μ γ' α) = 0

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [SuperCalc ι R M]
variable {I : Type*} [Fintype I] (c : StructureConstants R M I) (g : GammaData ι σ)

local notation "dRM" => dR (R := R) (M := M)

theorem sbilG_sub_mat {U V W : Type*} [AddCommGroup U] [Module R U] [AddCommGroup V]
    [Module R V] [AddCommGroup W] [Module R W] (B : U →ₗ[R] V →ₗ[R] W) (N N' : Matrix σ σ ℤ)
    (u : σ → U) (v : σ → V) : sbilG B (N - N') u v = sbilG B N u v - sbilG B N' u v := by
  simp only [sbilG, Matrix.sub_apply, sub_smul, sum_sub_distrib]

theorem covE_sbilG_sm (A : ι → I → R) (N : Matrix σ σ ℤ) (μ : ι) {ε : σ → M}
    (hε : ∀ α, dM μ (ε α) = 0) (ψ : σ → I → M) :
    covE c A μ (sbilG sm N ε ψ) = sbilG sm N ε (fun β => covO c A μ (ψ β)) := by
  simp only [sbilG, covE_sum, covE_zsmul, covE_sm c A μ (hε _)]

theorem sbilG_ms_left (N : Matrix σ σ ℤ) (X : I → R) (ε : σ → M) (ψ : σ → I → M) :
    sbilG opair N (fun α => ms X (ε α)) ψ = ip X (sbilG sm N ε ψ) := by
  simp only [sbilG, opair_ms, map_sum, map_zsmul]

/-- A configuration of gauge field and adjoint spinor, or a variation of one. -/
structure GFields (ι σ R M I : Type*) where
  /-- The gauge potential. -/
  A : ι → I → R
  /-- The adjoint spinor. -/
  lam : σ → I → M

namespace GFields
variable (Φ Ψ : GFields ι σ R M I)

/-- The field strength. -/
def F (μ ν : ι) : I → R := fieldStrength c Φ.A μ ν

/-- The covariant derivative of the spinor. -/
def Dlam (μ : ι) : σ → I → M := fun β => covO c Φ.A μ (Φ.lam β)

/-- The Lagrangian `-F_μν F^μν - 2 λ̄ Γ^μ D_μ λ`. -/
def lagrangian : R :=
  -(∑ μ, ∑ ν, (g.η μ * g.η ν) • ip (Φ.F c μ ν) (Φ.F c μ ν))
    - (2 : ℤ) • ∑ μ, sbilG opair (g.K μ) Φ.lam (Φ.Dlam c μ)

/-- First variation of the field strength. -/
def dF (a : ι → I → R) (μ ν : ι) : I → R := covE c Φ.A μ (a ν) - covE c Φ.A ν (a μ)

/-- First variation of `D_μ λ`. -/
def dDlam (μ : ι) : σ → I → M :=
  fun β => covO c Φ.A μ (Ψ.lam β) + act c (Ψ.A μ) (Φ.lam β)

/-- First variation of the Lagrangian at `Φ` in the direction `Ψ`. -/
def dLagrangian : R :=
  -(∑ μ, ∑ ν, (g.η μ * g.η ν) • ((2 : ℤ) • ip (Φ.F c μ ν) (Φ.dF c Ψ.A μ ν)))
    - (2 : ℤ) • ∑ μ, (sbilG opair (g.K μ) Ψ.lam (Φ.Dlam c μ)
        + sbilG opair (g.K μ) Φ.lam (Φ.dDlam c Ψ μ))

/-- The supersymmetry variation with parameter `ε`. -/
def susy (ε : σ → M) : GFields ι σ R M I where
  A μ := -((2 * g.η μ) • sbilG sm (g.K μ) ε Φ.lam)
  lam := fun α => ∑ ρ, ∑ σ', mvG (g.G2 ρ σ') (fun β => ms (Φ.F c ρ σ') (ε β)) α

/-- The current whose divergence is the supersymmetry variation of the Lagrangian. -/
def susyCurrent (ε : σ → M) (μ : ι) : R :=
  -((2 : ℤ) • sbilG opair (g.K μ) Φ.lam (Φ.susy c g ε).lam)
    + (4 : ℤ) • ∑ ρ, ∑ σ', ip (Φ.F c ρ σ') (sbilG sm (g.K3 ρ σ' μ) ε Φ.lam)

end GFields

/-! ## Two cancellations -/

theorem sum_in4' {P : Type*} [AddCommMonoid P] (h : ι → σ → σ → σ → σ → P) :
    ∑ i, ∑ a, ∑ b, ∑ d, ∑ e, h i a b d e = ∑ a, ∑ b, ∑ d, ∑ e, ∑ i, h i a b d e := by
  rw [sum_comm]; refine sum_congr rfl fun a _ => ?_
  rw [sum_comm]; refine sum_congr rfl fun b _ => ?_
  rw [sum_comm]; refine sum_congr rfl fun d _ => ?_
  rw [sum_comm]

/-- The cubic spinor term vanishes, by the Fierz identity and total antisymmetry of the
structure constants. -/
theorem cubic_vanishes (ε : σ → M) (lam : σ → I → M) :
    ∑ μ, sbilG opair (g.K μ) lam
      (fun β => act c (-((2 * g.η μ) • sbilG sm (g.K μ) ε lam)) (lam β)) = (0 : R) := by
  have hE : ∀ μ, sbilG opair (g.K μ) lam
      (fun β => act c (-((2 * g.η μ) • sbilG sm (g.K μ) ε lam)) (lam β)) =
      ∑ α, ∑ β, ∑ γ', ∑ δ, (-(2 * g.η μ * (g.K μ α β * g.K μ γ' δ))) •
        T3 c (lam α) (ε γ') (lam δ) (lam β) := by
    intro μ
    simp only [sbilG, T3, map_neg, map_zsmul, map_sum, LinearMap.neg_apply,
      LinearMap.smul_apply, LinearMap.sum_apply, smul_neg, smul_sum, smul_smul, neg_smul,
      mul_assoc, mul_left_comm, sum_neg_distrib]
  simp only [hE]
  rw [sum_in4']
  rw [sum_rot' fun α β γ' => ∑ δ, ∑ μ, (-(2 * g.η μ * (g.K μ α β * g.K μ γ' δ))) •
    T3 c (lam α) (ε γ') (lam δ) (lam β)]
  refine sum_eq_zero fun γ' _ => ?_
  simp only [← sum_smul]
  set H : σ → σ → σ → ℤ := fun α β δ => ∑ μ, -(2 * g.η μ * (g.K μ α β * g.K μ γ' δ)) with hH
  set x : σ → σ → σ → R := fun α β δ => T3 c (lam α) (ε γ') (lam δ) (lam β) with hx
  have hx1 : ∀ α β δ, x δ α β = x α β δ := fun α β δ => by
    simp only [hx]; rw [T3_swap13, T3_swap23]
  have hx2 : ∀ α β δ, x β δ α = x α β δ := fun α β δ => by
    simp only [hx]; rw [T3_swap23, T3_swap13]
  have key : ∀ α β δ, H α β δ + H δ α β + H β δ α = 0 := fun α β δ => by
    have h := g.fierz α β γ' δ
    simp only [hH, ← sum_add_distrib]
    rw [← neg_eq_zero, ← sum_neg_distrib]
    have h2 : (2 : ℤ) * ∑ μ, g.η μ * (g.K μ α β * g.K μ γ' δ + g.K μ δ α * g.K μ γ' β
        + g.K μ β δ * g.K μ γ' α) = 0 := by rw [h, mul_zero]
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

/-- A cyclically symmetric tensor contracted with one obeying the Bianchi identity vanishes. -/
theorem bianchi_contraction (h3t : ∀ a : R, 3 * a = 0 → a = 0)
    (Y T : ι → ι → ι → I → R)
    (hY : ∀ μ ρ σ', Y μ ρ σ' + Y ρ σ' μ + Y σ' μ ρ = 0) (hT : ∀ ρ σ' μ, T σ' μ ρ = T ρ σ' μ) :
    ∑ μ, ∑ ρ, ∑ σ', ip (Y μ ρ σ') (T ρ σ' μ) = 0 := by
  have s0 : ∑ μ, ∑ ρ, ∑ σ', ip (Y μ ρ σ') (T ρ σ' μ) =
      ∑ μ, ∑ ρ, ∑ σ', ip (Y σ' μ ρ) (T ρ σ' μ) := by
    rw [sum_rot fun μ ρ σ' => ip (Y μ ρ σ') (T ρ σ' μ)]
    exact sum_congr rfl fun μ _ => sum_congr rfl fun ρ _ => sum_congr rfl fun σ' _ => by
      rw [← hT ρ σ' μ, ← hT σ' μ ρ]
  have s1 : ∑ μ, ∑ ρ, ∑ σ', ip (Y μ ρ σ') (T ρ σ' μ) =
      ∑ μ, ∑ ρ, ∑ σ', ip (Y ρ σ' μ) (T ρ σ' μ) := by
    rw [sum_rot' fun μ ρ σ' => ip (Y μ ρ σ') (T ρ σ' μ)]
    exact sum_congr rfl fun μ _ => sum_congr rfl fun ρ _ => sum_congr rfl fun σ' _ => by
      rw [hT ρ σ' μ]
  apply h3t
  have h3 : (3 : R) * ∑ μ, ∑ ρ, ∑ σ', ip (Y μ ρ σ') (T ρ σ' μ) =
      ∑ μ, ∑ ρ, ∑ σ', ip (Y μ ρ σ' + Y ρ σ' μ + Y σ' μ ρ) (T ρ σ' μ) := by
    simp only [map_add, LinearMap.add_apply, sum_add_distrib]
    rw [← s0, ← s1]; ring
  rw [h3]
  exact sum_eq_zero fun μ _ => sum_eq_zero fun ρ _ => sum_eq_zero fun σ' _ => by
    rw [hY, map_zero, LinearMap.zero_apply]

/-! ## Supersymmetry of the Lagrangian -/

namespace GFields
variable (Φ : GFields ι σ R M I) (ε : σ → M)

/-- `F_μν · ε̄ Γ^ν D_μ λ`. -/
def auxP (μ ν : ι) : R := ip (Φ.F c μ ν) (sbilG sm (g.K ν) ε (Φ.Dlam c μ))

/-- `F_ρσ · ε̄ Γ^{ρσμ} D_μ λ`. -/
def auxQ (ρ σ' μ : ι) : R := ip (Φ.F c ρ σ') (sbilG sm (g.K3 ρ σ' μ) ε (Φ.Dlam c μ))

theorem covE_susyA (hε : ∀ μ α, dM μ (ε α) = 0) (μ ν : ι) :
    covE c Φ.A μ ((Φ.susy c g ε).A ν) =
      -((2 * g.η ν) • sbilG sm (g.K ν) ε (Φ.Dlam c μ)) := by
  have hA : (Φ.susy c g ε).A ν = -((2 * g.η ν) • sbilG sm (g.K ν) ε Φ.lam) := rfl
  rw [hA, covE_neg, covE_zsmul, covE_sbilG_sm c Φ.A (g.K ν) μ (hε μ)]
  rfl

theorem ip_F_dF_susy (hε : ∀ μ α, dM μ (ε α) = 0) (μ ν : ι) :
    ip (Φ.F c μ ν) (Φ.dF c (Φ.susy c g ε).A μ ν) =
      -((2 * g.η ν) • Φ.auxP c g ε μ ν) - (2 * g.η μ) • Φ.auxP c g ε ν μ := by
  have e : ip (Φ.F c μ ν) (sbilG sm (g.K μ) ε (Φ.Dlam c ν)) = -Φ.auxP c g ε ν μ := by
    rw [auxP, F, F, fieldStrength_antisymm c Φ.A ν μ, map_neg, LinearMap.neg_apply]
  rw [dF, covE_susyA c g Φ ε hε, covE_susyA c g Φ ε hε]
  simp only [map_sub, map_neg, map_zsmul]
  rw [e]; simp only [auxP, smul_neg]; abel

theorem sbilG_susyLam (ψ : σ → I → M) (N : Matrix σ σ ℤ) :
    sbilG opair N (Φ.susy c g ε).lam ψ =
      ∑ ρ, ∑ σ', ip (Φ.F c ρ σ') (sbilG sm ((g.G2 ρ σ').transpose * N) ε ψ) := by
  have hl : (Φ.susy c g ε).lam = fun α =>
      ∑ ρ, ∑ σ', mvG (g.G2 ρ σ') (fun β => ms (Φ.F c ρ σ') (ε β)) α := rfl
  rw [hl, sbilG_sum_left]
  simp only [sbilG_sum_left, sbilG_mv_left, sbilG_ms_left]

theorem kinetic_susy (μ : ι) :
    sbilG opair (g.K μ) (Φ.susy c g ε).lam (Φ.Dlam c μ) =
      -(∑ ρ, ∑ σ', (Φ.auxQ c g ε ρ σ' μ
          + (if σ' = μ then g.η σ' else 0) • (-Φ.auxP c g ε σ' ρ)
          - (if ρ = μ then g.η ρ else 0) • Φ.auxP c g ε ρ σ')) := by
  rw [sbilG_susyLam]
  simp only [g.G2K, sbilG_neg_mat, map_neg, sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun ρ _ => sum_congr rfl fun σ' _ => ?_
  rw [sbilG_sub_mat, sbilG_add_mat, sbilG_zsmul_mat, sbilG_zsmul_mat, map_sub, map_add,
    map_zsmul, map_zsmul]
  have e1 : (if σ' = μ then g.η σ' else 0) • ip (Φ.F c ρ σ') (sbilG sm (g.K ρ) ε (Φ.Dlam c μ)) =
      (if σ' = μ then g.η σ' else 0) • (-Φ.auxP c g ε σ' ρ) := by
    split_ifs with h
    · subst h
      rw [auxP, F, F, fieldStrength_antisymm c Φ.A σ' ρ, map_neg, LinearMap.neg_apply]
    · simp
  have e2 : (if ρ = μ then g.η ρ else 0) • ip (Φ.F c ρ σ') (sbilG sm (g.K σ') ε (Φ.Dlam c μ)) =
      (if ρ = μ then g.η ρ else 0) • Φ.auxP c g ε ρ σ' := by
    split_ifs with h
    · subst h; rfl
    · simp
  rw [e1, e2]; rfl

theorem kinetic_dDlam (μ : ι) :
    sbilG opair (g.K μ) Φ.lam (Φ.dDlam c (Φ.susy c g ε) μ) =
      dRM μ (sbilG opair (g.K μ) Φ.lam (Φ.susy c g ε).lam)
        + sbilG opair (g.K μ) (Φ.susy c g ε).lam (Φ.Dlam c μ)
        + sbilG opair (g.K μ) Φ.lam (fun β => act c ((Φ.susy c g ε).A μ) (Φ.lam β)) := by
  have d := sbilG_deriv (opair : (I → M) →ₗ[R] (I → M) →ₗ[R] R) (g.K μ) Φ.lam
    (Φ.susy c g ε).lam (dRM μ) opair opair (covO c Φ.A μ) (covO c Φ.A μ)
    (dR_opair_cov c Φ.A μ)
  have fl := sbilG_flip (opair : (I → M) →ₗ[R] (I → M) →ₗ[R] R) (g.K μ)
    (fun α => covO c Φ.A μ (Φ.lam α)) (Φ.susy c g ε).lam opair opair_antisymm
  rw [g.K_symm] at fl
  rw [fl] at d
  have hd : Φ.dDlam c (Φ.susy c g ε) μ = fun β =>
      covO c Φ.A μ ((Φ.susy c g ε).lam β) + act c ((Φ.susy c g ε).A μ) (Φ.lam β) := rfl
  have hDl : Φ.Dlam c μ = fun β => covO c Φ.A μ (Φ.lam β) := rfl
  rw [hd, sbilG_add_right, d, hDl]
  abel

theorem dR_susyCurrent (hε : ∀ μ α, dM μ (ε α) = 0) (μ : ι) :
    dRM μ (Φ.susyCurrent c g ε μ) =
      -((2 : ℤ) • dRM μ (sbilG opair (g.K μ) Φ.lam (Φ.susy c g ε).lam))
        + (4 : ℤ) • ∑ ρ, ∑ σ', (ip (covE c Φ.A μ (Φ.F c ρ σ'))
            (sbilG sm (g.K3 ρ σ' μ) ε Φ.lam) + Φ.auxQ c g ε ρ σ' μ) := by
  simp only [susyCurrent, map_add, map_neg, map_zsmul, map_sum, dR_ip_cov c Φ.A,
    covE_sbilG_sm c Φ.A _ μ (hε μ)]
  rfl

/-- **Supersymmetry of super Yang–Mills in any dimension with `GammaData`.** For a constant
odd spinor `ε`, the first variation of the Lagrangian along the supersymmetry transformation
is the divergence of `susyCurrent`. -/
theorem susy_invariance (hε : ∀ μ α, dM μ (ε α) = 0) :
    Φ.dLagrangian c g (Φ.susy c g ε) = ∑ μ, dRM μ (Φ.susyCurrent c g ε μ) := by
  have hcub : ∑ μ, sbilG opair (g.K μ) Φ.lam
      (fun β => act c ((Φ.susy c g ε).A μ) (Φ.lam β)) = (0 : R) :=
    cubic_vanishes c g ε Φ.lam
  have hB := bianchi_contraction (three_torsion (M := M))
    (fun μ ρ σ' => covE c Φ.A μ (Φ.F c ρ σ'))
    (fun ρ σ' μ => sbilG sm (g.K3 ρ σ' μ) ε Φ.lam)
    (fun μ ρ σ' => bianchi c Φ.A μ ρ σ') (fun ρ σ' μ => by rw [g.K3_cyclic])
  -- the three sums everything reduces to
  set S : R := ∑ μ, ∑ ν, g.η μ • Φ.auxP c g ε μ ν with hS
  set SQ : R := ∑ μ, ∑ ρ, ∑ σ', Φ.auxQ c g ε ρ σ' μ with hSQ
  set SK : R := ∑ μ, dRM μ (sbilG opair (g.K μ) Φ.lam (Φ.susy c g ε).lam) with hSK
  have hη : ∀ μ, ((g.η μ : ℤ) : R) * ((g.η μ : ℤ) : R) = 1 := fun μ => by
    rw [← Int.cast_mul, g.η_sq μ, Int.cast_one]
  have s1 : ∑ μ, ∑ ν, (g.η μ * g.η ν) • ((2 : ℤ) •
      ip (Φ.F c μ ν) (Φ.dF c (Φ.susy c g ε).A μ ν)) = -((8 : ℤ) • S) := by
    have t : ∀ μ ν, (g.η μ * g.η ν) • ((2 : ℤ) •
        ip (Φ.F c μ ν) (Φ.dF c (Φ.susy c g ε).A μ ν)) =
        (-4 : ℤ) • (g.η μ • Φ.auxP c g ε μ ν) + (-4 : ℤ) • (g.η ν • Φ.auxP c g ε ν μ) := by
      intro μ ν
      rw [ip_F_dF_susy c g Φ ε hε]
      simp only [zsmul_eq_mul]
      push_cast
      linear_combination (-4 * (g.η μ : R) * Φ.auxP c g ε μ ν) * hη ν
        + (-4 * (g.η ν : R) * Φ.auxP c g ε ν μ) * hη μ
    have e2 : ∑ μ, ∑ ν, g.η ν • Φ.auxP c g ε ν μ = S := by rw [hS]; exact sum_comm
    have e1 : ∑ μ, g.η μ • ∑ ν, Φ.auxP c g ε μ ν = S := by rw [hS]; simp only [smul_sum]
    simp only [t, sum_add_distrib, ← smul_sum, e2, e1]
    module
  have s2 : ∑ μ, sbilG opair (g.K μ) (Φ.susy c g ε).lam (Φ.Dlam c μ) =
      -SQ + (2 : ℤ) • S := by
    simp only [kinetic_susy, sum_neg_distrib, sum_add_distrib, sum_sub_distrib, ite_smul,
      zero_smul, smul_neg]
    have a1 : (∑ μ, ∑ ρ, ∑ σ', if σ' = μ then g.η σ' • Φ.auxP c g ε σ' ρ else 0) = S := by
      calc _ = ∑ ρ, ∑ σ', g.η σ' • Φ.auxP c g ε σ' ρ := by
            rw [sum_comm]
            refine sum_congr rfl fun ρ _ => ?_
            rw [sum_comm]
            refine sum_congr rfl fun σ' _ => ?_
            rw [sum_ite_eq, if_pos (mem_univ _)]
        _ = S := by rw [hS, sum_comm]
    have hq : ∑ μ, ∑ ρ, ∑ σ', Φ.auxQ c g ε ρ σ' μ = SQ := hSQ.symm
    have a2 : ∑ μ, ∑ ρ, ∑ σ', (if ρ = μ then g.η ρ • Φ.auxP c g ε ρ σ' else 0) = S := by
      rw [sum_comm]
      refine sum_congr rfl fun ρ _ => ?_
      rw [sum_comm]
      refine sum_congr rfl fun σ' _ => ?_
      rw [sum_ite_eq, if_pos (mem_univ _)]
    rw [a1, a2, hq]
    module
  have s3 : ∑ μ, dRM μ (Φ.susyCurrent c g ε μ) = -((2 : ℤ) • SK) + (4 : ℤ) • SQ := by
    simp only [dR_susyCurrent c g Φ ε hε, sum_add_distrib, sum_neg_distrib, ← smul_sum]
    rw [hB]
    simp only [← hSK, ← hSQ]
    module
  have s4 : ∑ μ, (sbilG opair (g.K μ) (Φ.susy c g ε).lam (Φ.Dlam c μ)
      + sbilG opair (g.K μ) Φ.lam (Φ.dDlam c (Φ.susy c g ε) μ)) =
      (2 : ℤ) • (-SQ + (2 : ℤ) • S) + SK := by
    simp only [kinetic_dDlam, sum_add_distrib, hcub, add_zero, s2]
    simp only [← hSK]
    module
  rw [dLagrangian, s1, s4, s3]
  module

end GFields
end SYM6
