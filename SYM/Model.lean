import SYM.Closure
import SYM.GaugeGroup
import YM.Maxwell.Exterior

/-!
# The model: smooth Grassmann-valued fields on spacetime

The abstract calculus is realized by smooth functions on the spacetime `YM.E4` of the
Yang–Mills formalization, with values in the even part `Λ₀` and the odd part `Λ₁` of a
Grassmann algebra, and with the coordinate derivatives `YM.Maxwell.grad`. Combined with the
structure constants of a gauge group `G : YM.Gauge`, this gives classical `N = 1` super
Yang–Mills theory with gauge group `G`.

Reused from `ym_core`: `YM.E4`, `YM.Axis`, `YM.basis`, `YM.Maxwell.grad`, `grad_smooth`,
`grad_comm`.
-/

set_option autoImplicit false
noncomputable section
namespace SYM
open YM YM.Maxwell SuperCalculus
open scoped ContDiff

/-- A Grassmann algebra presented by its even part `Λ₀`, a commutative normed real algebra,
and its odd part `Λ₁`, a normed `Λ₀`-module, with the product of two odd elements. -/
class GrassmannAlgebra (Λ₀ Λ₁ : Type) [NormedCommRing Λ₀] [NormedAlgebra ℝ Λ₀]
    [NormedAddCommGroup Λ₁] [NormedSpace ℝ Λ₁] [Module Λ₀ Λ₁] [IsBoundedSMul Λ₀ Λ₁]
    [IsScalarTower ℝ Λ₀ Λ₁] where
  /-- The product of two odd elements. -/
  mul : Λ₁ →L[ℝ] Λ₁ →L[ℝ] Λ₀
  mul_smul : ∀ (a : Λ₀) (θ η : Λ₁), mul (a • θ) η = a * mul θ η
  mul_self : ∀ θ, mul θ θ = 0
  mul_cyclic : ∀ θ η ζ : Λ₁, mul θ η • ζ = mul η ζ • θ

variable {Λ₀ Λ₁ : Type} [NormedCommRing Λ₀] [NormedAlgebra ℝ Λ₀]
  [NormedAddCommGroup Λ₁] [NormedSpace ℝ Λ₁] [Module Λ₀ Λ₁] [IsBoundedSMul Λ₀ Λ₁]
  [IsScalarTower ℝ Λ₀ Λ₁] [GrassmannAlgebra Λ₀ Λ₁]

namespace GrassmannAlgebra

theorem mul_antisymm (θ η : Λ₁) : mul (Λ₀ := Λ₀) θ η = -mul η θ := by
  have h := mul_self (Λ₀ := Λ₀) (θ + η)
  simp only [map_add, add_apply, mul_self, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

theorem mul_smul_right (a : Λ₀) (θ η : Λ₁) : mul θ (a • η) = a * mul θ η := by
  rw [mul_antisymm, mul_smul, mul_antisymm η θ, mul_neg, neg_neg]

end GrassmannAlgebra

section calculus
variable {E₁ E₂ E₃ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₂] [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]

theorem smooth_bil (B : E₁ →L[ℝ] E₂ →L[ℝ] E₃) {f : E4 → E₁} {g : E4 → E₂}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ fun x => B (f x) (g x) :=
  (B.contDiff.comp hf).clm_apply hg

theorem smooth_differentiable {f : E4 → E₁} (hf : ContDiff ℝ ∞ f) (x : E4) :
    DifferentiableAt ℝ f x :=
  (hf.differentiable (by simp)) x

theorem smooth_grad {f : E4 → E₁} (hf : ContDiff ℝ ∞ f) (μ : Axis) : ContDiff ℝ ∞ (grad μ f) :=
  contDiff_iff_contDiffAt.2 fun _ => grad_smooth μ hf.contDiffAt (by simp)

theorem grad_bil (B : E₁ →L[ℝ] E₂ →L[ℝ] E₃) {f : E4 → E₁} {g : E4 → E₂}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (μ : Axis) (x : E4) :
    grad μ (fun y => B (f y) (g y)) x = B (grad μ f x) (g x) + B (f x) (grad μ g x) := by
  have e : fderiv ℝ (fun y => B (f y) (g y)) x = _ :=
    (B.hasFDerivAt_of_bilinear (smooth_differentiable hf x).hasFDerivAt
      (smooth_differentiable hg x).hasFDerivAt).fderiv
  unfold grad Analysis.D
  rw [e, add_comm]
  rfl

theorem grad_add' {f g : E4 → E₁} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (μ : Axis)
    (x : E4) : grad μ (fun y => f y + g y) x = grad μ f x + grad μ g x := by
  have e := ((smooth_differentiable hf x).hasFDerivAt.add
    (smooth_differentiable hg x).hasFDerivAt).fderiv
  exact congrArg (fun L : E4 →L[ℝ] E₁ => L (basis μ)) e

theorem grad_const' (v : E₁) (μ : Axis) (x : E4) : grad μ (fun _ : E4 => v) x = 0 := by
  unfold grad Analysis.D
  rw [fderiv_fun_const]; rfl

theorem grad_grad_comm {f : E4 → E₁} (hf : ContDiff ℝ ∞ f) (μ ν : Axis) (x : E4) :
    grad μ (grad ν f) x = grad ν (grad μ f) x :=
  grad_comm (hf.contDiffAt.of_le
    (show ((↑(2 : ℕ)) : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) μ ν

end calculus

variable (Λ₀)

/-- Smooth even fields on spacetime. -/
def smoothEven : Subalgebra ℝ (E4 → Λ₀) where
  carrier := {f | ContDiff ℝ ∞ f}
  mul_mem' {f g} hf hg := show ContDiff ℝ ∞ (f * g) from
    (show ContDiff ℝ ∞ f from hf).mul (show ContDiff ℝ ∞ g from hg)
  add_mem' {f g} hf hg := show ContDiff ℝ ∞ (f + g) from
    (show ContDiff ℝ ∞ f from hf).add (show ContDiff ℝ ∞ g from hg)
  algebraMap_mem' r := (contDiff_const : ContDiff ℝ ∞ fun _ : E4 => algebraMap ℝ Λ₀ r)

variable {Λ₀}

/-- Smooth odd fields on spacetime. The even part `Λ₀` is recorded in the type so that it can
be recovered from it. -/
def smoothOdd (_Λ₀ Λ₁ : Type) [NormedAddCommGroup Λ₁] [NormedSpace ℝ Λ₁] :
    Submodule ℝ (E4 → Λ₁) where
  carrier := {θ | ContDiff ℝ ∞ θ}
  add_mem' {f g} hf hg := show ContDiff ℝ ∞ (f + g) from
    (show ContDiff ℝ ∞ f from hf).add (show ContDiff ℝ ∞ g from hg)
  zero_mem' := (contDiff_const : ContDiff ℝ ∞ fun _ : E4 => (0 : Λ₁))
  smul_mem' r f hf := show ContDiff ℝ ∞ (r • f) from
    (show ContDiff ℝ ∞ f from hf).const_smul r

instance : SMul (smoothEven Λ₀) (smoothOdd Λ₀ Λ₁) :=
  ⟨fun f θ => ⟨fun x => f.1 x • θ.1 x,
    smooth_bil (ContinuousLinearMap.lsmul ℝ Λ₀ : Λ₀ →L[ℝ] Λ₁ →L[ℝ] Λ₁) f.2 θ.2⟩⟩

instance : Module (smoothEven Λ₀) (smoothOdd Λ₀ Λ₁) where
  one_smul θ := Subtype.ext (funext fun x => one_smul Λ₀ (θ.1 x))
  mul_smul f g θ := Subtype.ext (funext fun x => mul_smul (f.1 x) (g.1 x) (θ.1 x))
  smul_zero f := Subtype.ext (funext fun x => smul_zero (f.1 x))
  smul_add f θ η := Subtype.ext (funext fun x => smul_add (f.1 x) (θ.1 x) (η.1 x))
  add_smul f g θ := Subtype.ext (funext fun x => add_smul (f.1 x) (g.1 x) (θ.1 x))
  zero_smul θ := Subtype.ext (funext fun x => zero_smul Λ₀ (θ.1 x))

/-- Pointwise product of two smooth odd fields. -/
def smoothPair : smoothOdd Λ₀ Λ₁ →ₗ[smoothEven Λ₀] smoothOdd Λ₀ Λ₁ →ₗ[smoothEven Λ₀] smoothEven Λ₀ :=
  LinearMap.mk₂ (smoothEven Λ₀)
    (fun θ η => ⟨fun x => GrassmannAlgebra.mul (Λ₀ := Λ₀) (θ.1 x) (η.1 x),
      smooth_bil (GrassmannAlgebra.mul (Λ₀ := Λ₀)) θ.2 η.2⟩)
    (fun θ θ' η => Subtype.ext (funext fun x => by
      show GrassmannAlgebra.mul (Λ₀ := Λ₀) (θ.1 x + θ'.1 x) (η.1 x) = _
      rw [map_add]; rfl))
    (fun f θ η => Subtype.ext (funext fun x =>
      GrassmannAlgebra.mul_smul (f.1 x) (θ.1 x) (η.1 x)))
    (fun θ η η' => Subtype.ext (funext fun x => by
      show GrassmannAlgebra.mul (Λ₀ := Λ₀) (θ.1 x) (η.1 x + η'.1 x) = _
      rw [map_add]; rfl))
    (fun f θ η => Subtype.ext (funext fun x =>
      GrassmannAlgebra.mul_smul_right (f.1 x) (θ.1 x) (η.1 x)))

/-- Coordinate derivative of a smooth even field. -/
def smoothDR (μ : Fin 4) : smoothEven Λ₀ →+ smoothEven Λ₀ where
  toFun f := ⟨grad μ f.1, smooth_grad f.2 μ⟩
  map_zero' := Subtype.ext (funext fun x => grad_const' (0 : Λ₀) μ x)
  map_add' f g := Subtype.ext (funext fun x => grad_add' f.2 g.2 μ x)

/-- Coordinate derivative of a smooth odd field. -/
def smoothDM (μ : Fin 4) : smoothOdd Λ₀ Λ₁ →+ smoothOdd Λ₀ Λ₁ where
  toFun θ := ⟨grad μ θ.1, smooth_grad θ.2 μ⟩
  map_zero' := Subtype.ext (funext fun x => grad_const' (0 : Λ₁) μ x)
  map_add' θ η := Subtype.ext (funext fun x => grad_add' θ.2 η.2 μ x)

theorem torsion_free (n : ℕ) [NeZero n] (a : smoothEven Λ₀) (h : (n : smoothEven Λ₀) * a = 0) :
    a = 0 := by
  refine Subtype.ext (funext fun x => ?_)
  have h' : (n : ℝ) • a.1 x = 0 := by
    have := congrFun (congrArg Subtype.val h) x
    rw [Algebra.smul_def, map_natCast]
    exact this
  exact (smul_eq_zero.mp h').resolve_left (Nat.cast_ne_zero.mpr (NeZero.ne n))

/-- Smooth Grassmann-valued fields on spacetime form a Grassmann differential calculus. -/
instance smoothCalculus : SuperCalculus (smoothEven Λ₀) (smoothOdd Λ₀ Λ₁) where
  pair := smoothPair
  pair_self θ := Subtype.ext (funext fun x => GrassmannAlgebra.mul_self (Λ₀ := Λ₀) (θ.1 x))
  pair_cyclic θ η ζ := Subtype.ext (funext fun x =>
    GrassmannAlgebra.mul_cyclic (θ.1 x) (η.1 x) (ζ.1 x))
  dR := smoothDR
  dM := smoothDM
  dR_mul μ f g := Subtype.ext (funext fun x =>
    grad_bil (ContinuousLinearMap.mul ℝ Λ₀) f.2 g.2 μ x)
  dM_smul μ f θ := Subtype.ext (funext fun x =>
    grad_bil (ContinuousLinearMap.lsmul ℝ Λ₀ : Λ₀ →L[ℝ] Λ₁ →L[ℝ] Λ₁) f.2 θ.2 μ x)
  dR_pair μ θ η := Subtype.ext (funext fun x => grad_bil (GrassmannAlgebra.mul (Λ₀ := Λ₀)) θ.2 η.2 μ x)
  dR_comm μ ν f := Subtype.ext (funext fun x => grad_grad_comm f.2 μ ν x)
  dM_comm μ ν θ := Subtype.ext (funext fun x => grad_grad_comm θ.2 μ ν x)
  two_torsion a h := torsion_free 2 a (by exact_mod_cast h)
  three_torsion a h := torsion_free 3 a (by exact_mod_cast h)

theorem smoothDR_algebraMap (μ : Fin 4) (r : ℝ) :
    dR (M := smoothOdd Λ₀ Λ₁) μ (algebraMap ℝ (smoothEven Λ₀) r) = 0 :=
  Subtype.ext (funext fun x => grad_const' (algebraMap ℝ Λ₀ r) μ x)

/-! ## Classical `N = 1` super Yang–Mills theory with gauge group `G` -/

variable (G : YM.Gauge) (Λ₀ Λ₁)

/-- Configurations of the vector multiplet with gauge group `G`: smooth Grassmann-valued
fields on spacetime with values in the Lie algebra of `G`. -/
abbrev VectorMultipletFields := Fields (smoothEven Λ₀) (smoothOdd Λ₀ Λ₁) G.ColorIndex

/-- The structure constants of `G`, as constant smooth fields. -/
def gaugeConstants : StructureConstants (smoothEven Λ₀) (smoothOdd Λ₀ Λ₁) G.ColorIndex :=
  gaugeStructureConstants G smoothDR_algebraMap

variable {G Λ₀ Λ₁}

/-- **Supersymmetry of `N = 1` super Yang–Mills theory with gauge group `G`.** -/
theorem superYangMills_susy (Φ : VectorMultipletFields Λ₀ Λ₁ G) (ε : Fin 4 → smoothOdd Λ₀ Λ₁)
    (hε : ∀ μ α, dM μ (ε α) = 0) :
    Φ.dLagrangian (gaugeConstants Λ₀ Λ₁ G) (Φ.susy (gaugeConstants Λ₀ Λ₁ G) ε) =
      ∑ μ, dR (M := smoothOdd Λ₀ Λ₁) μ (Φ.susyCurrent (gaugeConstants Λ₀ Λ₁ G) ε μ) :=
  Φ.susy_invariance (gaugeConstants Λ₀ Λ₁ G) ε hε

/-- **Off-shell closure of the supersymmetry algebra of `N = 1` super Yang–Mills theory with
gauge group `G`.** -/
theorem superYangMills_closure (Φ : VectorMultipletFields Λ₀ Λ₁ G)
    (ε₁ ε₂ : Fin 4 → smoothOdd Λ₀ Λ₁) (h₁ : ∀ μ α, dM μ (ε₁ α) = 0)
    (h₂ : ∀ μ α, dM μ (ε₂ α) = 0) :
    (∀ μ, (Φ.dsusy (gaugeConstants Λ₀ Λ₁ G) (Φ.susy (gaugeConstants Λ₀ Λ₁ G) ε₁) ε₂).A μ
        - (Φ.dsusy (gaugeConstants Λ₀ Λ₁ G) (Φ.susy (gaugeConstants Λ₀ Λ₁ G) ε₂) ε₁).A μ =
      (Φ.translation (Fields.xi ε₁ ε₂)).A μ
        + (Φ.gaugeVar (gaugeConstants Λ₀ Λ₁ G) (∑ σ, Fields.xi ε₁ ε₂ σ • Φ.A σ)).A μ) ∧
    (∀ α, (Φ.dsusy (gaugeConstants Λ₀ Λ₁ G) (Φ.susy (gaugeConstants Λ₀ Λ₁ G) ε₁) ε₂).lam α
        - (Φ.dsusy (gaugeConstants Λ₀ Λ₁ G) (Φ.susy (gaugeConstants Λ₀ Λ₁ G) ε₂) ε₁).lam α =
      (Φ.translation (Fields.xi ε₁ ε₂)).lam α
        + (Φ.gaugeVar (gaugeConstants Λ₀ Λ₁ G) (∑ σ, Fields.xi ε₁ ε₂ σ • Φ.A σ)).lam α) ∧
    (Φ.dsusy (gaugeConstants Λ₀ Λ₁ G) (Φ.susy (gaugeConstants Λ₀ Λ₁ G) ε₁) ε₂).D
        - (Φ.dsusy (gaugeConstants Λ₀ Λ₁ G) (Φ.susy (gaugeConstants Λ₀ Λ₁ G) ε₂) ε₁).D =
      (Φ.translation (Fields.xi ε₁ ε₂)).D
        + (Φ.gaugeVar (gaugeConstants Λ₀ Λ₁ G) (∑ σ, Fields.xi ε₁ ε₂ σ • Φ.A σ)).D :=
  Φ.closure (gaugeConstants Λ₀ Λ₁ G) ε₁ ε₂ h₁ h₂

/-- The Grassmann algebra with one odd generator `θ`: even part `ℝ`, odd part `ℝ θ`, and
`θ² = 0`. It shows that the hypotheses on a Grassmann algebra are consistent with a non-zero
odd part; in it every fermion bilinear vanishes. -/
@[reducible] def GrassmannAlgebra.oneGenerator : GrassmannAlgebra ℝ ℝ where
  mul := 0
  mul_smul a θ η := by simp
  mul_self θ := by simp
  mul_cyclic θ η ζ := by simp

end SYM
