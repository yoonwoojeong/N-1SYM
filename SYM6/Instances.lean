import SYM6.Theory
import SYM6.Chiral3
import SYM.Gamma

/-!
# Gamma data in four and six dimensions

Two instances of `GammaData`, so that `GFields.susy_invariance` gives:

* `gamma4`: four-dimensional `N = 1` super Yang–Mills without its auxiliary field, from the
  Majorana matrices of `SYM/Gamma.lean`;
* `gamma6`: six-dimensional super Yang–Mills with a chiral spinor, from the chiral bilinear
  matrices `chiralΓ` and the Fierz identity `fierz6`.

In six dimensions the spinor index runs over all 16 real components. The matrices `chiralΓ`
contain the chiral projector, so the non-chiral components do not enter the Lagrangian.
-/

set_option autoImplicit false
namespace SYM6
open Matrix

set_option maxRecDepth 1000000

/-! ## Four dimensions -/

theorem η4_sq : ∀ μ : Fin 4, SYM.η μ * SYM.η μ = 1 := by decide

/-- Gamma data of four-dimensional Majorana spinors. -/
def gamma4 : GammaData (Fin 4) (Fin 4) where
  η := SYM.η
  K := SYM.Cγ
  G2 := SYM.γ2
  K3 := fun ρ σ μ => SYM.chargeC * SYM.γ3 ρ σ μ
  η_sq := η4_sq
  K_symm := SYM.Cγ_transpose
  G2K := fun ρ σ μ => by
    rw [SYM.Cγ, ← Matrix.mul_assoc, SYM.γ2_transpose_C, Matrix.neg_mul, SYM.Cγ2γ]
  K3_cyclic := fun ρ σ μ => by rw [SYM.γ3_cyclic]
  fierz := SYM.fierz_cubic

/-! ## Six dimensions -/

/-- Gamma data of six-dimensional chiral spinors. -/
def gamma6 : GammaData (Fin 6) (Fin 16) where
  η := ηg
  K := chiralΓ
  G2 := Γ2
  K3 := chiralΓ3
  η_sq := ηg_sq
  K_symm := chiralΓ_symm
  G2K := fun ρ σ μ => by
    simp only [chiralΓ3]
    abel
  K3_cyclic := chiralΓ3_cyclic
  fierz := fun α β γ' δ => by
    have h := fierz6 α β γ' δ
    have hs : ∀ a (i j : Fin 16), chiralΓ a i j = chiralΓ a j i := fun a i j => by
      have := congrFun (congrFun (chiralΓ_symm a) j) i
      simpa [Matrix.transpose_apply] using this
    rw [← h]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hs a δ α, hs a γ' β, hs a β δ, hs a γ' α, hs a α γ']
    ring

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {I : Type*} [Fintype I]

/-- **Supersymmetry of six-dimensional super Yang–Mills.** -/
theorem superYangMills6 [SuperCalc (Fin 6) R M] (c : StructureConstants R M I)
    (Φ : GFields (Fin 6) (Fin 16) R M I) (ε : Fin 16 → M)
    (hε : ∀ μ α, SuperCalc.dM μ (ε α) = 0) :
    Φ.dLagrangian c gamma6 (Φ.susy c gamma6 ε) =
      ∑ μ, SuperCalc.dR (M := M) μ (Φ.susyCurrent c gamma6 ε μ) :=
  Φ.susy_invariance c gamma6 ε hε

/-- **Supersymmetry of four-dimensional super Yang–Mills without auxiliary field**, from the
same theorem. -/
theorem superYangMills4 [SuperCalc (Fin 4) R M] (c : StructureConstants R M I)
    (Φ : GFields (Fin 4) (Fin 4) R M I) (ε : Fin 4 → M)
    (hε : ∀ μ α, SuperCalc.dM μ (ε α) = 0) :
    Φ.dLagrangian c gamma4 (Φ.susy c gamma4 ε) =
      ∑ μ, SuperCalc.dR (M := M) μ (Φ.susyCurrent c gamma4 ε μ) :=
  Φ.susy_invariance c gamma4 ε hε

end SYM6
