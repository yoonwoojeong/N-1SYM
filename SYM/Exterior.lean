import SYM.Model

/-!
# The exterior algebra on two generators as a Grassmann algebra

`Λ(ℝ²)` has basis `1, θ₁, θ₂, θ₁θ₂`. Its even part `ℝ ⊕ ℝ θ₁θ₂` is the algebra of dual
numbers, realized as `TrivSqZeroExt ℝ ℝ`; its odd part `ℝ θ₁ ⊕ ℝ θ₂` is `ℝ × ℝ`. The product
of two odd elements is `(u₁θ₁ + u₂θ₂)(v₁θ₁ + v₂θ₂) = (u₁v₂ - u₂v₁) θ₁θ₂`.

This is a `GrassmannAlgebra` in which fermion bilinears do not vanish
(`evenOddMul_ne_zero`), so smooth fields with values in it give a model of the theory with
non-trivial gaugino bilinears. Products of three odd elements vanish, since `Λ³(ℝ²) = 0`.
-/

set_option autoImplicit false
noncomputable section
namespace SYM.TwoGenerators
open TrivSqZeroExt

/-- The even part of `Λ(ℝ²)`: `a + b θ₁θ₂`. -/
abbrev Even := TrivSqZeroExt ℝ ℝ

/-- The odd part of `Λ(ℝ²)`: `u₁ θ₁ + u₂ θ₂`. -/
abbrev Odd := ℝ × ℝ

/-- An even element acts on an odd one through its degree-zero part, because
`θ₁θ₂ · θᵢ = 0`. -/
instance : Module Even Odd := Module.compHom Odd (fstHom ℝ ℝ ℝ).toRingHom

theorem smul_def (x : Even) (v : Odd) : x • v = fst x • v := rfl

instance : IsBoundedSMul Even Odd :=
  IsBoundedSMul.of_norm_smul_le fun x v => by
    rw [smul_def, norm_smul, TrivSqZeroExt.norm_def]
    have h : ‖fst x‖ ≤ ‖fst x‖ + ‖snd x‖ := le_add_of_nonneg_right (norm_nonneg _)
    exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

instance : IsScalarTower ℝ Even Odd :=
  ⟨fun r x v => by rw [smul_def, smul_def, fst_smul, smul_assoc]⟩

/-- The product of two odd elements, `(u₁v₂ - u₂v₁) θ₁θ₂`. -/
def oddMul : Odd →L[ℝ] Odd →L[ℝ] Even :=
  (LinearMap.mk₂ ℝ (fun u v : Odd => (inr (u.1 * v.2 - u.2 * v.1) : Even))
    (fun u u' v => by
      rw [← inr_add]; congr 1; simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun r u v => by
      rw [← inr_smul]; congr 1
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (fun u v v' => by
      rw [← inr_add]; congr 1; simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun r u v => by
      rw [← inr_smul]; congr 1
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)).toContinuousBilinearMap

theorem oddMul_apply (u v : Odd) : oddMul u v = inr (u.1 * v.2 - u.2 * v.1) := rfl

/-- `Λ(ℝ²)` is a Grassmann algebra. -/
instance grassmann : GrassmannAlgebra Even Odd where
  mul := oddMul
  mul_smul a θ η := by
    rw [oddMul_apply, oddMul_apply, smul_def]
    ext
    · simp
    · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, snd_inr, snd_mul, fst_inr,
        MulOpposite.op_zero, zero_smul, add_zero]
      ring
  mul_self θ := by rw [oddMul_apply, mul_comm, sub_self, inr_zero]
  mul_cyclic θ η ζ := by
    rw [oddMul_apply, oddMul_apply, smul_def, smul_def, fst_inr, fst_inr, zero_smul, zero_smul]

/-- Fermion bilinears do not vanish: `θ₁ θ₂ ≠ 0`. -/
theorem oddMul_ne_zero : GrassmannAlgebra.mul (Λ₀ := Even) ((1, 0) : Odd) ((0, 1) : Odd) ≠ 0 := by
  intro h
  have h' := congrArg snd h
  change snd (oddMul ((1, 0) : Odd) ((0, 1) : Odd)) = snd (0 : Even) at h'
  rw [oddMul_apply] at h'
  simp at h'

/-- The product is genuinely antisymmetric: `θ₂ θ₁ = -θ₁ θ₂`. -/
theorem oddMul_swap :
    GrassmannAlgebra.mul (Λ₀ := Even) ((0, 1) : Odd) ((1, 0) : Odd) =
      -GrassmannAlgebra.mul (Λ₀ := Even) ((1, 0) : Odd) ((0, 1) : Odd) :=
  GrassmannAlgebra.mul_antisymm _ _

/-- Smooth fields with values in `Λ(ℝ²)` form a Grassmann calculus, so every theorem of the
theory applies to them. -/
example : SuperCalculus (smoothEven Even) (smoothOdd Even Odd) := inferInstance

/-- Supersymmetry of the Lagrangian for `Λ(ℝ²)`-valued fields and any gauge group. -/
example (G : YM.Gauge) (Φ : VectorMultipletFields Even Odd G) (ε : Fin 4 → smoothOdd Even Odd)
    (hε : ∀ μ α, SuperCalculus.dM μ (ε α) = 0) :
    Φ.dLagrangian (gaugeConstants Even Odd G) (Φ.susy (gaugeConstants Even Odd G) ε) =
      ∑ μ, SuperCalculus.dR (M := smoothOdd Even Odd) μ
        (Φ.susyCurrent (gaugeConstants Even Odd G) ε μ) :=
  superYangMills_susy Φ ε hε

end SYM.TwoGenerators
