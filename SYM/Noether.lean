import SYM.Variation

/-!
# Equations of motion and conservation of the supercurrent

## Equations of motion

Integrating the first variation of the Lagrangian by parts gives the first-variation formula
(`first_variation`): for every variation `Ψ = (a, χ, d)`,

`δL = ⟨E_A^ν, a_ν⟩ + ⟨χ, E_λ⟩ + ⟨E_D, d⟩ + ∂_μ Θ^μ(Ψ)`.

The coefficients are the Euler–Lagrange expressions, and their vanishing is the equations of
motion (`OnShell`):

* `eomA ν = 4 D_μ F^{μν} - 2 λ̄ γ^ν [·, λ]`: the Yang–Mills equation with gaugino current,
* `eomLam = -4 C γ^μ D_μ λ`: the Dirac equation,
* `eomD = 4 D`: the auxiliary field vanishes.

## Supercurrent

The supersymmetry variation of the Lagrangian is a divergence `∂_μ K^μ` off shell
(`susy_invariance`). Comparing with the first-variation formula gives Noether's identity
(`noether_identity`): the divergence of `J^μ = Θ^μ(δ_ε Φ) - K^μ` is minus the equations of
motion contracted with `δ_ε Φ`. Hence `J^μ` is conserved on shell
(`supercurrent_conserved`). Explicitly `J^μ = -4 F_ρσ · ε̄ γ^{ρσ} γ^μ λ`
(`supercurrent_eq`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace SYM
open SuperCalculus Finset Matrix

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [SuperCalculus R M]
variable {I : Type*} [Fintype I] (c : StructureConstants R M I)

local notation "dRM" => dR (R := R) (M := M)

/-- The bracket of two odd adjoint fields, an even adjoint field:
`{ψ, χ}_b = f_{abc} ψ_a χ_c`. It is the gauge current of a pair of fermions. -/
def obrk : (I → M) →ₗ[R] (I → M) →ₗ[R] (I → R) :=
  LinearMap.mk₂ R (fun ψ χ b => ∑ a, ∑ d, c.f a b d * pair (ψ a) (χ d))
    (fun ψ ψ' χ => by
      funext b; simp only [Pi.add_apply, map_add, LinearMap.add_apply, mul_add, sum_add_distrib])
    (fun r ψ χ => by
      funext b
      simp only [Pi.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_sum]
      exact sum_congr rfl fun a _ => sum_congr rfl fun d _ => by ring)
    (fun ψ χ χ' => by
      funext b; simp only [Pi.add_apply, map_add, mul_add, sum_add_distrib])
    (fun r ψ χ => by
      funext b
      simp only [Pi.smul_apply, map_smul, smul_eq_mul, mul_sum]
      exact sum_congr rfl fun a _ => sum_congr rfl fun d _ => by ring)

theorem obrk_apply (ψ χ : I → M) (b : I) :
    obrk c ψ χ b = ∑ a, ∑ d, c.f a b d * pair (ψ a) (χ d) := rfl

/-- `⟨ψ, [X, χ]⟩ = ⟨{ψ, χ}, X⟩`. -/
theorem opair_act_eq (X : I → R) (ψ χ : I → M) :
    opair ψ (act c X χ) = ip (obrk c ψ χ) X := by
  simp only [opair_apply, act_apply, ip_apply, obrk_apply, map_sum, map_smul, smul_eq_mul,
    sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun b _ => sum_congr rfl fun a _ => sum_congr rfl fun d _ => by ring

namespace Fields
variable (Φ Ψ : Fields R M I)

/-- Euler–Lagrange expression of the gauge field: `4 D_μ F^{μν} - 2 λ̄ γ^ν [·, λ]`. -/
def eomA (ν : Fin 4) : I → R :=
  (4 : ℤ) • ∑ μ, (η μ * η ν) • covE c Φ.A μ (Φ.F c μ ν)
    - (2 : ℤ) • sbil (obrk c) (Cγ ν) Φ.lam Φ.lam

/-- Euler–Lagrange expression of the gaugino: `-4 C γ^μ D_μ λ`. -/
def eomLam (α : Fin 4) : I → M := -((4 : ℤ) • ∑ μ, mv (Cγ μ) (Φ.Dlam c μ) α)

/-- Euler–Lagrange expression of the auxiliary field: `4 D`. -/
def eomD : I → R := (4 : ℤ) • Φ.D

/-- The boundary term of the first variation. -/
def boundaryTerm (μ : Fin 4) : R :=
  -((4 : ℤ) • ∑ ν, (η μ * η ν) • ip (Φ.F c μ ν) (Ψ.A ν))
    - (2 : ℤ) • sbil opair (Cγ μ) Φ.lam Ψ.lam

/-- The equations of motion contracted with a variation. -/
def eomPairing : R :=
  ∑ ν, ip (Φ.eomA c ν) (Ψ.A ν) + ∑ α, opair (Ψ.lam α) (Φ.eomLam c α) + ip Φ.eomD Ψ.D

/-- The equations of motion of `N = 1` super Yang–Mills theory. -/
structure OnShell : Prop where
  gauge : ∀ ν, Φ.eomA c ν = 0
  gaugino : ∀ α, Φ.eomLam c α = 0
  aux : Φ.eomD = 0

theorem kinetic_dDlam_general (μ : Fin 4) :
    sbil opair (Cγ μ) Φ.lam (Φ.dDlam c Ψ μ) =
      dRM μ (sbil opair (Cγ μ) Φ.lam Ψ.lam) + sbil opair (Cγ μ) Ψ.lam (Φ.Dlam c μ)
        + sbil opair (Cγ μ) Φ.lam (fun β => act c (Ψ.A μ) (Φ.lam β)) := by
  have d := sbil_deriv (opair : (I → M) →ₗ[R] (I → M) →ₗ[R] R) (Cγ μ) Φ.lam Ψ.lam
    (dRM μ) opair opair (covO c Φ.A μ) (covO c Φ.A μ) (dR_opair_cov c Φ.A μ)
  have fl := sbil_flip (opair : (I → M) →ₗ[R] (I → M) →ₗ[R] R) (Cγ μ)
    (fun α => covO c Φ.A μ (Φ.lam α)) Ψ.lam opair opair_antisymm
  rw [Cγ_transpose] at fl
  rw [fl] at d
  have hd : Φ.dDlam c Ψ μ = fun β =>
      covO c Φ.A μ (Ψ.lam β) + act c (Ψ.A μ) (Φ.lam β) := rfl
  have hDl : Φ.Dlam c μ = fun β => covO c Φ.A μ (Φ.lam β) := rfl
  rw [hd, sbil_add_right, d, hDl]
  abel

set_option maxHeartbeats 4000000 in
/-- **The first-variation formula.** The first variation of the Lagrangian is the equations
of motion contracted with the variation, plus a divergence. -/
theorem first_variation :
    Φ.dLagrangian c Ψ = Φ.eomPairing c Ψ + ∑ μ, dRM μ (Φ.boundaryTerm c Ψ μ) := by
  have e1 : ∀ μ ν, ip (Φ.F c μ ν) (Φ.dF c Ψ.A μ ν) =
      dRM μ (ip (Φ.F c μ ν) (Ψ.A ν)) - ip (covE c Φ.A μ (Φ.F c μ ν)) (Ψ.A ν)
        + (dRM ν (ip (Φ.F c ν μ) (Ψ.A μ)) - ip (covE c Φ.A ν (Φ.F c ν μ)) (Ψ.A μ)) := by
    intro μ ν
    have a := dR_ip_cov c Φ.A μ (Φ.F c μ ν) (Ψ.A ν)
    have b := dR_ip_cov c Φ.A ν (Φ.F c ν μ) (Ψ.A μ)
    have s : Φ.F c μ ν = -Φ.F c ν μ := fieldStrength_antisymm c Φ.A ν μ
    rw [dF, map_sub, a, b]
    nth_rewrite 2 [s]
    rw [map_neg, LinearMap.neg_apply]
    ring
  have e2 : ∀ μ, sbil opair (Cγ μ) Ψ.lam (Φ.Dlam c μ) =
      ∑ α, opair (Ψ.lam α) (mv (Cγ μ) (Φ.Dlam c μ) α) := by
    intro μ; simp only [sbil, mv, map_sum, map_zsmul]
  have e3 : ∀ μ, sbil opair (Cγ μ) Φ.lam (fun β => act c (Ψ.A μ) (Φ.lam β)) =
      ip (sbil (obrk c) (Cγ μ) Φ.lam Φ.lam) (Ψ.A μ) := by
    intro μ
    simp only [sbil, opair_act_eq, map_sum, map_zsmul, LinearMap.sum_apply,
      LinearMap.smul_apply]
  simp only [dLagrangian, eomPairing, eomA, eomLam, eomD, boundaryTerm, e1,
    kinetic_dDlam_general, e2, e3, map_sub, map_neg, map_zsmul, map_sum, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.sum_apply]
  simp only [Fin.sum_univ_four]
  simp [η]
  ring

/-! ## The supercurrent -/

variable (ε : Fin 4 → M)

/-- The Noether current of supersymmetry: the boundary term of the supersymmetry variation
minus the current `K^μ` whose divergence is the variation of the Lagrangian. -/
def supercurrent (μ : Fin 4) : R :=
  Φ.boundaryTerm c (Φ.susy c ε) μ - Φ.susyCurrent c ε μ

/-- **Noether's identity for supersymmetry.** Off shell, the divergence of the supercurrent
is minus the equations of motion contracted with the supersymmetry variation. -/
theorem noether_identity (hε : ∀ μ α, dM μ (ε α) = 0) :
    ∑ μ, dRM μ (Φ.supercurrent c ε μ) = -Φ.eomPairing c (Φ.susy c ε) := by
  have h1 := first_variation c Φ (Φ.susy c ε)
  have h2 := susy_invariance c Φ ε hε
  simp only [supercurrent, map_sub, sum_sub_distrib]
  linear_combination h2 - h1

/-- **Conservation of the supercurrent.** On solutions of the equations of motion, the
supercurrent is divergence-free. -/
theorem supercurrent_conserved (hε : ∀ μ α, dM μ (ε α) = 0) (h : Φ.OnShell c) :
    ∑ μ, dRM μ (Φ.supercurrent c ε μ) = 0 := by
  rw [noether_identity c Φ ε hε]
  simp only [eomPairing, h.gauge, h.gaugino, h.aux, map_zero, LinearMap.zero_apply,
    sum_const_zero, add_zero, neg_zero]

set_option maxHeartbeats 4000000 in
/-- **The supercurrent in closed form:** `J^μ = -4 F_ρσ · ε̄ γ^{ρσ} γ^μ λ`. The auxiliary field
drops out. -/
theorem supercurrent_eq (μ : Fin 4) : Φ.supercurrent c ε μ =
    -((4 : ℤ) • ∑ ρ, ∑ σ, ip (Φ.F c ρ σ) (sbil sm (chargeC * γ2 ρ σ * γ μ) ε Φ.lam)) := by
  have hA : ∀ ν, (Φ.susy c ε).A ν = -((2 * η ν) • sbil sm (Cγ ν) ε Φ.lam) := fun _ => rfl
  have key : ∀ ρ σ, ip (Φ.F c ρ σ) (sbil sm (chargeC * γ2 ρ σ * γ μ) ε Φ.lam) =
      ip (Φ.F c ρ σ) (sbil sm (chargeC * γ3 ρ σ μ) ε Φ.lam)
        + (if σ = μ then η σ else 0) • (-ip (Φ.F c σ ρ) (sbil sm (Cγ ρ) ε Φ.lam))
        - (if ρ = μ then η ρ else 0) • ip (Φ.F c ρ σ) (sbil sm (Cγ σ) ε Φ.lam) := by
    intro ρ σ
    by_cases h : ρ = σ
    · subst h
      simp [F, fieldStrength_self]
    · have e : ip (Φ.F c ρ σ) (sbil sm (Cγ ρ) ε Φ.lam) =
          -ip (Φ.F c σ ρ) (sbil sm (Cγ ρ) ε Φ.lam) := by
        rw [F, F, fieldStrength_antisymm c Φ.A σ ρ, map_neg, LinearMap.neg_apply]
      rw [Cγ2γ, sbil_sub_mat, sbil_add_mat, sbil_zsmul_mat, sbil_zsmul_mat, map_sub, map_add,
        map_zsmul, map_zsmul, e]
  simp only [supercurrent, boundaryTerm, susyCurrent, hA, key, map_neg, map_zsmul]
  fin_cases μ <;> simp [Fin.sum_univ_four, η] <;> ring

end Fields
end SYM
