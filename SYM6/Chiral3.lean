import SYM6.Fierz6

/-!
# Rank-three chiral bilinears in six dimensions

`chiralΓ3 ρ σ μ` is the matrix of `ψ̄ Γ^{ρσμ} χ` on chiral spinors, defined through
`Γ^{ρσ} Γ^μ = Γ^{ρσμ} + Γ^ρ η^{σμ} - Γ^σ η^{ρμ}`. Its cyclic symmetry is checked by kernel
evaluation, split by the first index because a single evaluation runs out of memory.
-/

set_option autoImplicit false
namespace SYM6
open Matrix

set_option maxRecDepth 1000000

/-- `Γ^{ρσ}`. -/
def Γ2 (ρ σ : Fin 6) : Mat16 := if ρ = σ then 0 else Γ ρ * Γ σ

/-- The matrices of `ψ̄ Γ^{ρσμ} χ` on chiral spinors, defined through
`Γ^{ρσ} Γ^μ = Γ^{ρσμ} + Γ^ρ η^{σμ} - Γ^σ η^{ρμ}`. -/
def chiralΓ3 (ρ σ μ : Fin 6) : Mat16 :=
  -((Γ2 ρ σ).transpose * chiralΓ μ) - (if σ = μ then ηg σ else 0) • chiralΓ ρ
    + (if ρ = μ then ηg ρ else 0) • chiralΓ σ

theorem ηg_sq : ∀ a : Fin 6, ηg a * ηg a = 1 := by decide

theorem chiralΓ_symm : ∀ a, (chiralΓ a).transpose = chiralΓ a := by decide +kernel

theorem chiralΓ3_cyclic_0 : ∀ σ μ : Fin 6, chiralΓ3 σ μ 0 = chiralΓ3 0 σ μ := by
  decide +kernel

theorem chiralΓ3_cyclic_1 : ∀ σ μ : Fin 6, chiralΓ3 σ μ 1 = chiralΓ3 1 σ μ := by
  decide +kernel

theorem chiralΓ3_cyclic_2 : ∀ σ μ : Fin 6, chiralΓ3 σ μ 2 = chiralΓ3 2 σ μ := by
  decide +kernel

theorem chiralΓ3_cyclic_3 : ∀ σ μ : Fin 6, chiralΓ3 σ μ 3 = chiralΓ3 3 σ μ := by
  decide +kernel

theorem chiralΓ3_cyclic_4 : ∀ σ μ : Fin 6, chiralΓ3 σ μ 4 = chiralΓ3 4 σ μ := by
  decide +kernel

theorem chiralΓ3_cyclic_5 : ∀ σ μ : Fin 6, chiralΓ3 σ μ 5 = chiralΓ3 5 σ μ := by
  decide +kernel

/-- Cyclic symmetry of `Γ^{ρσμ}` on chiral spinors. -/
theorem chiralΓ3_cyclic : ∀ ρ σ μ : Fin 6, chiralΓ3 σ μ ρ = chiralΓ3 ρ σ μ := by
  intro ρ
  fin_cases ρ
  · exact chiralΓ3_cyclic_0
  · exact chiralΓ3_cyclic_1
  · exact chiralΓ3_cyclic_2
  · exact chiralΓ3_cyclic_3
  · exact chiralΓ3_cyclic_4
  · exact chiralΓ3_cyclic_5

end SYM6
