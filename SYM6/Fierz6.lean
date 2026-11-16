import SYM6.Gamma6
import Mathlib.Tactic.FinCases

/-!
# The chiral Fierz identity in six dimensions

`chiralΓ a = (1 + Γ7)ᵀ C Γ^a (1 + Γ7)` is four times the matrix of the bilinear
`ψ̄ Γ^a χ` restricted to chiral spinors. The identity

`∑_a η_a (chiralΓ a)_{α(β} (chiralΓ a)_{γδ)} = 0`

is the six-dimensional analogue of the four-dimensional identity behind the vanishing of the
cubic fermion term. It is the Fierz identity on which supersymmetry of a chiral multiplet in
six dimensions rests.
-/

set_option autoImplicit false
namespace SYM6

/-- `(1 + Γ7)ᵀ C Γ^a (1 + Γ7)`, written out. -/
def chiralΓ : Fin 6 → Mat16 :=
  ![!![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0; 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0; 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, -2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0; 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, -2, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 0; 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0; -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0; 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 2, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2],
    !![0, 0, 0, -2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0; 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0; 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0; -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 0; 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 2, 0, 0, 0; 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2; 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0; 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0; 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0; 0, 0, 0, 2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0; 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2; 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0; 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 0; 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, -2, 0, 0, 0],
    !![0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0; -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0; 0, 0, 0, 2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0; 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2; 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0; 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0; 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, -2, 0, 0, 0; 0, 0, 0, 2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0; 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0; 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0; -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 0; 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, -2, 0, 0, 0; 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0],
    !![0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 0; 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 2, 0, 0, 0; 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2; 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0; 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0; 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0; -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2; 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0; 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0; 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 2, 0, 0, 0; 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0; -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0; 0, 0, 0, 2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0; 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2; 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0; 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0; 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 2, 0, 0, 0; 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0; 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0; 0, 0, 0, -2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0; 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0; 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, -2, 0, 0, 0; 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2; 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0; 0, 0, 0, 2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0; 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0; 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0; -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0],
    !![-2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0; 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0; 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, -2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0; 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2; 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 2, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 0; 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0; 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0; 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, -2, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 0; 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2]]

set_option maxRecDepth 1000000

theorem chiralΓ_eq : ∀ a, chiralΓ a = (1 + Γ7).transpose * chargeC6 * Γ a * (1 + Γ7) := by
  decide +kernel

theorem fierz6_0 : ∀ β γ δ : Fin 16, ∑ a, ηg a *
    (chiralΓ a 0 β * chiralΓ a γ δ + chiralΓ a 0 γ * chiralΓ a δ β
      + chiralΓ a 0 δ * chiralΓ a β γ) = 0 := by
  decide +kernel

theorem fierz6_1 : ∀ β γ δ : Fin 16, ∑ a, ηg a *
    (chiralΓ a 1 β * chiralΓ a γ δ + chiralΓ a 1 γ * chiralΓ a δ β
      + chiralΓ a 1 δ * chiralΓ a β γ) = 0 := by
  decide +kernel

theorem fierz6_2 : ∀ β γ δ : Fin 16, ∑ a, ηg a *
    (chiralΓ a 2 β * chiralΓ a γ δ + chiralΓ a 2 γ * chiralΓ a δ β
      + chiralΓ a 2 δ * chiralΓ a β γ) = 0 := by
  decide +kernel

theorem fierz6_3 : ∀ β γ δ : Fin 16, ∑ a, ηg a *
    (chiralΓ a 3 β * chiralΓ a γ δ + chiralΓ a 3 γ * chiralΓ a δ β
      + chiralΓ a 3 δ * chiralΓ a β γ) = 0 := by
  decide +kernel

theorem fierz6_4 : ∀ β γ δ : Fin 16, ∑ a, ηg a *
    (chiralΓ a 4 β * chiralΓ a γ δ + chiralΓ a 4 γ * chiralΓ a δ β
      + chiralΓ a 4 δ * chiralΓ a β γ) = 0 := by
  decide +kernel

theorem fierz6_5 : ∀ β γ δ : Fin 16, ∑ a, ηg a *
    (chiralΓ a 5 β * chiralΓ a γ δ + chiralΓ a 5 γ * chiralΓ a δ β
      + chiralΓ a 5 δ * chiralΓ a β γ) = 0 := by
  decide +kernel

theorem fierz6_6 : ∀ β γ δ : Fin 16, ∑ a, ηg a *
    (chiralΓ a 6 β * chiralΓ a γ δ + chiralΓ a 6 γ * chiralΓ a δ β
      + chiralΓ a 6 δ * chiralΓ a β γ) = 0 := by
  decide +kernel

theorem fierz6_7 : ∀ β γ δ : Fin 16, ∑ a, ηg a *
    (chiralΓ a 7 β * chiralΓ a γ δ + chiralΓ a 7 γ * chiralΓ a δ β
      + chiralΓ a 7 δ * chiralΓ a β γ) = 0 := by
  decide +kernel

theorem fierz6_8 : ∀ β γ δ : Fin 16, ∑ a, ηg a *
    (chiralΓ a 8 β * chiralΓ a γ δ + chiralΓ a 8 γ * chiralΓ a δ β
      + chiralΓ a 8 δ * chiralΓ a β γ) = 0 := by
  decide +kernel

theorem fierz6_9 : ∀ β γ δ : Fin 16, ∑ a, ηg a *
    (chiralΓ a 9 β * chiralΓ a γ δ + chiralΓ a 9 γ * chiralΓ a δ β
      + chiralΓ a 9 δ * chiralΓ a β γ) = 0 := by
  decide +kernel

theorem fierz6_10 : ∀ β γ δ : Fin 16, ∑ a, ηg a *
    (chiralΓ a 10 β * chiralΓ a γ δ + chiralΓ a 10 γ * chiralΓ a δ β
      + chiralΓ a 10 δ * chiralΓ a β γ) = 0 := by
  decide +kernel

theorem fierz6_11 : ∀ β γ δ : Fin 16, ∑ a, ηg a *
    (chiralΓ a 11 β * chiralΓ a γ δ + chiralΓ a 11 γ * chiralΓ a δ β
      + chiralΓ a 11 δ * chiralΓ a β γ) = 0 := by
  decide +kernel

theorem fierz6_12 : ∀ β γ δ : Fin 16, ∑ a, ηg a *
    (chiralΓ a 12 β * chiralΓ a γ δ + chiralΓ a 12 γ * chiralΓ a δ β
      + chiralΓ a 12 δ * chiralΓ a β γ) = 0 := by
  decide +kernel

theorem fierz6_13 : ∀ β γ δ : Fin 16, ∑ a, ηg a *
    (chiralΓ a 13 β * chiralΓ a γ δ + chiralΓ a 13 γ * chiralΓ a δ β
      + chiralΓ a 13 δ * chiralΓ a β γ) = 0 := by
  decide +kernel

theorem fierz6_14 : ∀ β γ δ : Fin 16, ∑ a, ηg a *
    (chiralΓ a 14 β * chiralΓ a γ δ + chiralΓ a 14 γ * chiralΓ a δ β
      + chiralΓ a 14 δ * chiralΓ a β γ) = 0 := by
  decide +kernel

theorem fierz6_15 : ∀ β γ δ : Fin 16, ∑ a, ηg a *
    (chiralΓ a 15 β * chiralΓ a γ δ + chiralΓ a 15 γ * chiralΓ a δ β
      + chiralΓ a 15 δ * chiralΓ a β γ) = 0 := by
  decide +kernel

/-- **The chiral vector Fierz identity.** -/
theorem fierz6 : ∀ α β γ δ : Fin 16, ∑ a, ηg a *
    (chiralΓ a α β * chiralΓ a γ δ + chiralΓ a α γ * chiralΓ a δ β
      + chiralΓ a α δ * chiralΓ a β γ) = 0 := by
  intro α
  fin_cases α
  · exact fierz6_0
  · exact fierz6_1
  · exact fierz6_2
  · exact fierz6_3
  · exact fierz6_4
  · exact fierz6_5
  · exact fierz6_6
  · exact fierz6_7
  · exact fierz6_8
  · exact fierz6_9
  · exact fierz6_10
  · exact fierz6_11
  · exact fierz6_12
  · exact fierz6_13
  · exact fierz6_14
  · exact fierz6_15

end SYM6
