import YM.Gauge.Casimir
import YM.Maxwell.Exterior
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The classical `N = 1` vector multiplet: field content and local gauge covariance

A small extension of the OpenAI Yang–Mills formalization (package `ym_core`, used unmodified)
toward classical four-dimensional `N = 1` super Yang–Mills theory.

Everything is expressed with the existing infrastructure:

* `YM.Gauge`, `G.Color`, `G.ad` (`YM.Gauge.Colors`): the gauge group, its Lie algebra in
  trace-orthonormal coordinates, and the Lie bracket in those coordinates;
* `YM.Gauge.ad_jacobi`, `YM.Gauge.ad_skew` (`YM.Gauge.Casimir`): the Jacobi identity and
  the invariance of the colour inner product;
* `YM.E4`, `YM.Axis` (`YM.Space`), `YM.Maxwell.grad`, `YM.Maxwell.grad_comm`
  (`YM.Maxwell.Exterior`): Euclidean spacetime, coordinate derivatives and their symmetry.

New here: the off-shell multiplet `(A, λ, D)`, the covariant derivative `covD`, the
non-abelian field strength `fieldStrength`, the infinitesimal local gauge transformation, and
the proof that the field strength, the covariant derivative of the gaugino and the Lagrangian
density transform as they should.

## Scope

These are gauge-covariance statements. They hold for an arbitrary spinor coefficient tensor
`Γ` in the gaugino kinetic term, so they use no Clifford relation and no Grassmann parity.
No supersymmetry transformation is defined or claimed here.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SYM

open YM.Maxwell
open scoped InnerProductSpace BigOperators

variable {G : Gauge}

/-! ## Two facts about the bracket not stated upstream -/

/-- Antisymmetry of the Lie bracket in colour coordinates. -/
theorem ad_antisymm (a b : G.Color) : G.ad a b = -G.ad b a := by
  apply G.colorMat_injective
  rw [Gauge.colorMat_ad, LinearMap.map_neg, Gauge.colorMat_ad, neg_sub]

/-- Leibniz rule for a coordinate derivative of a bracket of two colour fields. -/
theorem grad_ad {f g : E4 → G.Color} {x : E4} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (μ : Axis) :
    grad μ (fun y => G.ad (f y) (g y)) x =
      G.ad (grad μ f x) (g x) + G.ad (f x) (grad μ g x) := by
  have e : fderiv ℝ (fun y => G.ad (f y) (g y)) x = _ :=
    ((G.ad.toContinuousBilinearMap).hasFDerivAt_of_bilinear hf.hasFDerivAt hg.hasFDerivAt).fderiv
  unfold grad Analysis.D
  rw [e, add_comm]
  rfl

/-! ## Field content -/

/-- Index of a four-component spinor. -/
abbrev SpinorIndex := Fin 4

/-- The off-shell `N = 1` vector multiplet on `E4`: a gauge potential, an adjoint-valued
four-component gaugino and an adjoint-valued auxiliary field. All components are valued in
the colour coordinates `G.Color` of the Lie algebra of `G`. -/
structure VectorMultiplet (G : Gauge) where
  /-- The gauge potential `A_μ`. -/
  gauge : Axis → E4 → G.Color
  /-- The gaugino `λ_α`. -/
  gaugino : SpinorIndex → E4 → G.Color
  /-- The auxiliary field `D`. -/
  aux : E4 → G.Color

/-- Covariant derivative `D_μ φ = ∂_μ φ + [A_μ, φ]` of an adjoint-valued field. -/
def covD (A : Axis → E4 → G.Color) (μ : Axis) (φ : E4 → G.Color) (x : E4) : G.Color :=
  grad μ φ x + G.ad (A μ x) (φ x)

/-- Field strength `F_μν = ∂_μ A_ν - ∂_ν A_μ + [A_μ, A_ν]`. -/
def fieldStrength (A : Axis → E4 → G.Color) (μ ν : Axis) (x : E4) : G.Color :=
  grad μ (A ν) x - grad ν (A μ) x + G.ad (A μ x) (A ν x)

theorem fieldStrength_antisymm (A : Axis → E4 → G.Color) (μ ν : Axis) (x : E4) :
    fieldStrength A μ ν x = -fieldStrength A ν μ x := by
  unfold fieldStrength
  rw [ad_antisymm (A μ x)]
  abel

/-! ## Infinitesimal local gauge transformations

For a gauge parameter `ω : E4 → G.Color` the infinitesimal transformation is
`δA_μ = -D_μ ω` and `δφ = [ω, φ]` for adjoint matter. `shiftGauge` and `shiftAdjoint` are the
fields moved by `t` times this variation. -/

/-- `A_μ + t δA_μ` with `δA_μ = -D_μ ω`. -/
def shiftGauge (ω : E4 → G.Color) (t : ℝ) (A : Axis → E4 → G.Color) : Axis → E4 → G.Color :=
  fun μ x => A μ x - t • covD A μ ω x

/-- `φ + t δφ` with `δφ = [ω, φ]`. -/
def shiftAdjoint (ω : E4 → G.Color) (t : ℝ) (φ : E4 → G.Color) : E4 → G.Color :=
  fun x => φ x + t • G.ad (ω x) (φ x)

/-- Covariance of the covariant derivative, exactly in the parameter `t`: the first-order
term is the adjoint action of `ω` on `D_μ φ`. -/
theorem covD_shift {A : Axis → E4 → G.Color} {ω φ : E4 → G.Color} {x : E4}
    (hω : DifferentiableAt ℝ ω x) (hφ : DifferentiableAt ℝ φ x) (μ : Axis) (t : ℝ) :
    covD (shiftGauge ω t A) μ (shiftAdjoint ω t φ) x =
      covD A μ φ x + t • G.ad (ω x) (covD A μ φ x)
        - (t ^ 2) • G.ad (covD A μ ω x) (G.ad (ω x) (φ x)) := by
  have hb : DifferentiableAt ℝ (fun y => G.ad (ω y) (φ y)) x :=
    ((G.ad.toContinuousBilinearMap).hasFDerivAt_of_bilinear
      hω.hasFDerivAt hφ.hasFDerivAt).differentiableAt
  have h1 : grad μ (shiftAdjoint ω t φ) x =
      grad μ φ x + t • (G.ad (grad μ ω x) (φ x) + G.ad (ω x) (grad μ φ x)) := by
    rw [← grad_ad hω hφ]
    have e := (hφ.hasFDerivAt.add (hb.hasFDerivAt.const_smul t)).fderiv
    exact congrArg (fun L : E4 →L[ℝ] G.Color => L (basis μ)) e
  have hj := congrArg (fun L => L (φ x)) (Gauge.ad_jacobi (A μ x) (ω x))
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at hj
  unfold covD at h1 ⊢
  rw [h1]
  simp only [shiftGauge, shiftAdjoint, covD, map_add, map_sub, map_smul, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_add, smul_sub, smul_smul, hj]
  module

/-- Coordinate derivative of a covariant derivative of a twice differentiable field. -/
theorem grad_covD {A : Axis → E4 → G.Color} {ω : E4 → G.Color} {x : E4} (μ ν : Axis)
    (hA : DifferentiableAt ℝ (A ν) x) (hω : ContDiffAt ℝ 2 ω x) :
    grad μ (covD A ν ω) x =
      grad μ (grad ν ω) x + (G.ad (grad μ (A ν) x) (ω x) + G.ad (A ν x) (grad μ ω x)) := by
  have hω1 : DifferentiableAt ℝ ω x := hω.differentiableAt two_ne_zero
  have hg : DifferentiableAt ℝ (grad ν ω) x :=
    (grad_smooth ν (m := 1) hω one_add_one_eq_two.le).differentiableAt one_ne_zero
  have hb : DifferentiableAt ℝ (fun y => G.ad (A ν y) (ω y)) x :=
    ((G.ad.toContinuousBilinearMap).hasFDerivAt_of_bilinear
      hA.hasFDerivAt hω1.hasFDerivAt).differentiableAt
  rw [← grad_ad hA hω1]
  have e := (hg.hasFDerivAt.add hb.hasFDerivAt).fderiv
  exact congrArg (fun L : E4 →L[ℝ] G.Color => L (basis μ)) e

/-- Covariance of the field strength, exactly in the parameter `t`: the first-order term is
the adjoint action of `ω` on `F_μν`. -/
theorem fieldStrength_shift {A : Axis → E4 → G.Color} {ω : E4 → G.Color} {x : E4}
    (hA : ∀ μ, DifferentiableAt ℝ (A μ) x) (hω : ContDiffAt ℝ 2 ω x) (μ ν : Axis) (t : ℝ) :
    fieldStrength (shiftGauge ω t A) μ ν x =
      fieldStrength A μ ν x + t • G.ad (ω x) (fieldStrength A μ ν x)
        + (t ^ 2) • G.ad (covD A μ ω x) (covD A ν ω x) := by
  have hω1 : DifferentiableAt ℝ ω x := hω.differentiableAt two_ne_zero
  have hD (μ ν : Axis) : grad μ (shiftGauge ω t A ν) x =
      grad μ (A ν) x - t • (grad μ (grad ν ω) x +
        (G.ad (grad μ (A ν) x) (ω x) + G.ad (A ν x) (grad μ ω x))) := by
    have hc : DifferentiableAt ℝ (covD A ν ω) x := by
      have hg : DifferentiableAt ℝ (grad ν ω) x :=
        (grad_smooth ν (m := 1) hω one_add_one_eq_two.le).differentiableAt one_ne_zero
      have hb : DifferentiableAt ℝ (fun y => G.ad (A ν y) (ω y)) x :=
        ((G.ad.toContinuousBilinearMap).hasFDerivAt_of_bilinear
          (hA ν).hasFDerivAt hω1.hasFDerivAt).differentiableAt
      exact hg.add hb
    rw [← grad_covD μ ν (hA ν) hω]
    have e := ((hA ν).hasFDerivAt.sub (hc.hasFDerivAt.const_smul t)).fderiv
    exact congrArg (fun L : E4 →L[ℝ] G.Color => L (basis μ)) e
  have hc := grad_comm hω μ ν
  have e1 := ad_antisymm (ω x) (grad μ (A ν) x)
  have e2 := ad_antisymm (ω x) (grad ν (A μ) x)
  have e3 := ad_antisymm (grad μ ω x) (A ν x)
  have e5 : G.ad (A μ x) (G.ad (ω x) (A ν x)) = -G.ad (A μ x) (G.ad (A ν x) (ω x)) := by
    rw [ad_antisymm (ω x), map_neg]
  have hj := congrArg (fun L => L (A ν x)) (Gauge.ad_jacobi (A μ x) (ω x))
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at hj
  unfold fieldStrength
  rw [hD μ ν, hD ν μ]
  simp only [shiftGauge, covD, map_add, map_sub, map_smul, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_add, smul_sub, smul_smul]
  linear_combination (norm := module)
    (-t) • hc - t • e1 + t • e2 - t • e3 - t • hj - t • e5

/-! ## The multiplet and its Lagrangian density -/

/-- The multiplet moved by `t` times the infinitesimal gauge transformation with parameter
`ω`: `δA_μ = -D_μ ω`, `δλ = [ω, λ]`, `δD = [ω, D]`. -/
def VectorMultiplet.shift (ω : E4 → G.Color) (t : ℝ) (Φ : VectorMultiplet G) :
    VectorMultiplet G where
  gauge := shiftGauge ω t Φ.gauge
  gaugino α := shiftAdjoint ω t (Φ.gaugino α)
  aux := shiftAdjoint ω t Φ.aux

/-- The off-shell Lagrangian density
`¼ ⟪F_μν, F_μν⟫ + ½ Γ^μ_αβ ⟪λ_α, D_μ λ_β⟫ + ½ ⟪D, D⟫`,
with the colour inner product of `G.Color` (which is `-(1/d₀) tr` in the defining
representation, see `YM.Gauge.trace_color`) and index sums over `E4`.

`Γ` is the spinor coefficient tensor of the gaugino kinetic term (`C γ^μ` in a Majorana
basis). It is a parameter: nothing proved in this file depends on its value. -/
def lagrangian (Γ : Axis → SpinorIndex → SpinorIndex → ℝ) (Φ : VectorMultiplet G) (x : E4) :
    ℝ :=
  (1 / 4) * ∑ μ, ∑ ν, ⟪fieldStrength Φ.gauge μ ν x, fieldStrength Φ.gauge μ ν x⟫_ℝ
    + (1 / 2) * ∑ μ, ∑ α, ∑ β,
        Γ μ α β * ⟪Φ.gaugino α x, covD Φ.gauge μ (Φ.gaugino β) x⟫_ℝ
    + (1 / 2) * ⟪Φ.aux x, Φ.aux x⟫_ℝ

private theorem hasDerivAt_quadratic {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X : ℝ → V} {c a b : V} (h : ∀ t, X t = c + t • a + (t ^ 2) • b) : HasDerivAt X a 0 := by
  have e : X = fun t : ℝ => c + t • a + (t ^ 2) • b := funext h
  rw [e]
  have h1 := ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add c
  have h2 := (hasDerivAt_pow 2 (0 : ℝ)).smul_const b
  have h3 : HasDerivAt (fun t : ℝ => c + t • a + (t ^ 2) • b)
      ((1 : ℝ) • a + ((2 : ℕ) * (0 : ℝ) ^ (2 - 1)) • b) 0 := h1.add h2
  simpa using h3

/-- First-order form of `fieldStrength_shift`: `δF_μν = [ω, F_μν]`. -/
theorem hasDerivAt_fieldStrength_shift {A : Axis → E4 → G.Color} {ω : E4 → G.Color} {x : E4}
    (hA : ∀ μ, DifferentiableAt ℝ (A μ) x) (hω : ContDiffAt ℝ 2 ω x) (μ ν : Axis) :
    HasDerivAt (fun t => fieldStrength (shiftGauge ω t A) μ ν x)
      (G.ad (ω x) (fieldStrength A μ ν x)) 0 :=
  hasDerivAt_quadratic (fieldStrength_shift hA hω μ ν)

/-- First-order form of `covD_shift`: `δ(D_μ φ) = [ω, D_μ φ]`. -/
theorem hasDerivAt_covD_shift {A : Axis → E4 → G.Color} {ω φ : E4 → G.Color} {x : E4}
    (hω : DifferentiableAt ℝ ω x) (hφ : DifferentiableAt ℝ φ x) (μ : Axis) :
    HasDerivAt (fun t => covD (shiftGauge ω t A) μ (shiftAdjoint ω t φ) x)
      (G.ad (ω x) (covD A μ φ x)) 0 :=
  hasDerivAt_quadratic (b := -G.ad (covD A μ ω x) (G.ad (ω x) (φ x))) fun t => by
    rw [covD_shift hω hφ μ t, smul_neg, sub_eq_add_neg]

/-- Two colour-valued curves that both move, to first order, by the adjoint action of the same
`w` have a stationary inner product. This is where invariance of the colour inner product
(`YM.Gauge.ad_skew`) enters. -/
private theorem hasDerivAt_inner_covariant {X Y : ℝ → G.Color} {w c d b b' : G.Color}
    (hX : ∀ t, X t = c + t • G.ad w c + (t ^ 2) • b)
    (hY : ∀ t, Y t = d + t • G.ad w d + (t ^ 2) • b') :
    HasDerivAt (fun t => ⟪X t, Y t⟫_ℝ) 0 0 := by
  have h := (hasDerivAt_quadratic hX).inner ℝ (hasDerivAt_quadratic hY)
  have hX0 : X 0 = c := by simpa using hX 0
  have hY0 : Y 0 = d := by simpa using hY 0
  have e : ⟪X 0, G.ad w d⟫_ℝ + ⟪G.ad w c, Y 0⟫_ℝ = 0 := by
    rw [hX0, hY0, Gauge.ad_skew]; ring
  rwa [e] at h

/-- **Infinitesimal local gauge invariance of the `N = 1` vector-multiplet Lagrangian
density.** Along `t ↦ Φ + t δ_ω Φ` the density is stationary at `t = 0`, at every point where
the fields are differentiable and the gauge parameter is `C²`. -/
theorem lagrangian_gauge_invariant (Γ : Axis → SpinorIndex → SpinorIndex → ℝ)
    (Φ : VectorMultiplet G) {ω : E4 → G.Color} {x : E4}
    (hA : ∀ μ, DifferentiableAt ℝ (Φ.gauge μ) x)
    (hψ : ∀ α, DifferentiableAt ℝ (Φ.gaugino α) x) (hω : ContDiffAt ℝ 2 ω x) :
    HasDerivAt (fun t => lagrangian Γ (Φ.shift ω t) x) 0 0 := by
  have hω1 : DifferentiableAt ℝ ω x := hω.differentiableAt two_ne_zero
  have hF (μ ν : Axis) := hasDerivAt_inner_covariant
    (fun t => fieldStrength_shift hA hω μ ν t) (fun t => fieldStrength_shift hA hω μ ν t)
  have hψ' (α : SpinorIndex) (t : ℝ) : shiftAdjoint ω t (Φ.gaugino α) x =
      Φ.gaugino α x + t • G.ad (ω x) (Φ.gaugino α x) + (t ^ 2) • (0 : G.Color) := by
    simp [shiftAdjoint]
  have hcov (μ : Axis) (β : SpinorIndex) (t : ℝ) :
      covD (shiftGauge ω t Φ.gauge) μ (shiftAdjoint ω t (Φ.gaugino β)) x =
        covD Φ.gauge μ (Φ.gaugino β) x + t • G.ad (ω x) (covD Φ.gauge μ (Φ.gaugino β) x)
          + (t ^ 2) • -G.ad (covD Φ.gauge μ ω x) (G.ad (ω x) (Φ.gaugino β x)) := by
    rw [covD_shift hω1 (hψ β) μ t, smul_neg, sub_eq_add_neg]
  have hK (μ : Axis) (α β : SpinorIndex) :=
    (hasDerivAt_inner_covariant (hψ' α) (hcov μ β)).const_mul (Γ μ α β)
  have haux (t : ℝ) : shiftAdjoint ω t Φ.aux x =
      Φ.aux x + t • G.ad (ω x) (Φ.aux x) + (t ^ 2) • (0 : G.Color) := by
    simp [shiftAdjoint]
  have hD := hasDerivAt_inner_covariant haux haux
  have h1 := HasDerivAt.fun_sum (u := Finset.univ) fun μ _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun ν _ => hF μ ν
  have h2 := HasDerivAt.fun_sum (u := Finset.univ) fun μ _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun α _ =>
      HasDerivAt.fun_sum (u := Finset.univ) fun β _ => hK μ α β
  have h : HasDerivAt (fun t => lagrangian Γ (Φ.shift ω t) x)
      ((1 / 4) * ∑ _μ : Axis, ∑ _ν : Axis, (0 : ℝ)
        + (1 / 2) * ∑ μ : Axis, ∑ α : SpinorIndex, ∑ β : SpinorIndex, Γ μ α β * 0
        + (1 / 2) * 0) 0 :=
    ((h1.const_mul (1 / 4)).add (h2.const_mul (1 / 2))).add (hD.const_mul (1 / 2))
  simpa using h

end YM.SYM
