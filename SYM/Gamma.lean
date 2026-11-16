import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic

/-!
# Real Majorana gamma matrices in four dimensions

Signature `(+,+,+,-)`, time last (the convention of `YM.timeAxis`). All matrices are integer
matrices, so every identity below is checked by kernel evaluation (`decide`).

* `γ μ` are the matrices `γ^μ`, with `γ^μ γ^ν + γ^ν γ^μ = 2 η^{μν}`.
* `chargeC` is the charge conjugation matrix: `ψ̄ = ψᵀ C`.
* `γ5 = γ^0 γ^1 γ^2 γ^3` is real with `γ5² = -1` (it is `i γ_*` of the complex conventions).
* `γ2 ρ σ = γ^{ρσ}` and `γ3 ρ σ μ = γ^{ρσμ}` are the antisymmetrized products.
-/

set_option autoImplicit false
namespace SYM

/-- Diagonal entries of the Minkowski metric, time last. -/
def η (μ : Fin 4) : ℤ := if μ = 3 then -1 else 1

/-- The matrices `γ^μ` in a real (Majorana) representation. -/
def γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℤ :=
  ![!![0, 0, 0, 1; 0, 0, -1, 0; 0, -1, 0, 0; 1, 0, 0, 0],
    !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1],
    !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]]

/-- Charge conjugation matrix, `C = γ^3`. -/
def chargeC : Matrix (Fin 4) (Fin 4) ℤ := γ 3

/-- `γ5 = γ^0 γ^1 γ^2 γ^3`. -/
def γ5 : Matrix (Fin 4) (Fin 4) ℤ := γ 0 * γ 1 * γ 2 * γ 3

/-- `γ^{ρσ}`. -/
def γ2 (ρ σ : Fin 4) : Matrix (Fin 4) (Fin 4) ℤ := if ρ = σ then 0 else γ ρ * γ σ

/-- `γ^{ρσμ}`. -/
def γ3 (ρ σ μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℤ :=
  if ρ = σ ∨ σ = μ ∨ ρ = μ then 0 else γ ρ * γ σ * γ μ

/-- `C γ^μ`. -/
def Cγ (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℤ := chargeC * γ μ

set_option maxRecDepth 100000

theorem clifford : ∀ μ ν : Fin 4,
    γ μ * γ ν + γ ν * γ μ = (if μ = ν then 2 * η μ else 0) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  decide +kernel

theorem γ5_sq : γ5 * γ5 = -1 := by decide +kernel
theorem chargeC_transpose : chargeC.transpose = -chargeC := by decide +kernel
theorem Cγ_transpose : ∀ μ, (Cγ μ).transpose = Cγ μ := by decide +kernel
theorem Cγ5_transpose : (chargeC * γ5).transpose = -(chargeC * γ5) := by decide +kernel

theorem γ2_antisymm : ∀ ρ σ, γ2 σ ρ = -γ2 ρ σ := by decide +kernel
theorem γ3_cyclic : ∀ ρ σ μ, γ3 σ μ ρ = γ3 ρ σ μ := by decide +kernel

/-- `γ^{ρσ} γ^μ = γ^{ρσμ} + γ^ρ η^{σμ} - γ^σ η^{ρμ}`, multiplied by `C`. -/
theorem Cγ2γ : ∀ ρ σ μ, chargeC * γ2 ρ σ * γ μ =
    chargeC * γ3 ρ σ μ + (if σ = μ then η σ else 0) • Cγ ρ - (if ρ = μ then η ρ else 0) • Cγ σ := by
  decide +kernel

theorem γ2_transpose_C : ∀ ρ σ, (γ2 ρ σ).transpose * chargeC = -(chargeC * γ2 ρ σ) := by
  decide +kernel
theorem γ5_transpose_C : γ5.transpose * chargeC = chargeC * γ5 := by decide +kernel

/-- Used for closure on the gauge field. -/
theorem Cγγ2_symm : ∀ μ ρ σ, Cγ μ * γ2 ρ σ + (Cγ μ * γ2 ρ σ).transpose =
    (2 * η μ) • ((if μ = ρ then (1 : ℤ) else 0) • Cγ σ - (if μ = σ then (1 : ℤ) else 0) • Cγ ρ) := by
  decide +kernel
theorem Cγγ5_symm : ∀ μ, Cγ μ * γ5 + (Cγ μ * γ5).transpose = 0 := by decide +kernel

/-- Used for closure on the auxiliary field. -/
theorem Cγ5γγ2_symm : ∀ μ ρ σ, chargeC * γ5 * γ μ * γ2 ρ σ +
    (chargeC * γ5 * γ μ * γ2 ρ σ).transpose = (2 : ℤ) • (chargeC * γ5 * γ3 μ ρ σ) := by
  decide +kernel
theorem Cγ5γγ5_symm : ∀ μ, chargeC * γ5 * γ μ * γ5 +
    (chargeC * γ5 * γ μ * γ5).transpose = (2 : ℤ) • Cγ μ := by decide +kernel

/-- The Fierz identity `(C γ_μ)_{(αβ} (C γ^μ)_{γ)δ} = 0` behind the vanishing of the cubic
gaugino term. -/
theorem fierz_cubic : ∀ α β γ' δ : Fin 4, ∑ μ, η μ *
    (Cγ μ α β * Cγ μ γ' δ + Cγ μ δ α * Cγ μ γ' β + Cγ μ β δ * Cγ μ γ' α) = 0 := by
  decide +kernel

/-- Coefficient tensor of the commutator of two supersymmetries on the gaugino. -/
def closureW (ρ α β γ' δ : Fin 4) : ℤ :=
  -4 * ∑ σ, η σ * (γ2 ρ σ α β * Cγ σ γ' δ) + 4 * (γ5 α β * (chargeC * γ5 * γ ρ) γ' δ)

/-- The Fierz identity behind closure of the algebra on the gaugino. -/
theorem fierz_closure : ∀ ρ α β γ' δ : Fin 4, closureW ρ α β γ' δ + closureW ρ α γ' β δ =
    8 * (Cγ ρ β γ' * if α = δ then 1 else 0) := by
  decide +kernel

/-- The Fierz identity behind closure of the algebra on the auxiliary field. -/
theorem fierz_aux : ∀ α β γ' δ : Fin 4,
    (∑ μ, η μ * ((chargeC * γ5 * γ μ) α β * Cγ μ γ' δ + (chargeC * γ5 * γ μ) γ' δ * Cγ μ α β)) +
    (∑ μ, η μ * ((chargeC * γ5 * γ μ) α δ * Cγ μ γ' β + (chargeC * γ5 * γ μ) γ' β * Cγ μ α δ))
      = 0 := by
  decide +kernel

end SYM
