import SYM.Color
import YM.Gauge.Casimir

/-!
# Structure constants of the gauge groups of the Yang–Mills formalization

For a gauge group `G : YM.Gauge` of the OpenAI Yang–Mills formalization, the bracket `G.ad` on
the trace-orthonormal colour coordinates `G.Color` gives totally antisymmetric structure
constants satisfying the Jacobi identity. They make every theorem of the abstract theory
available for `G`.

Reused from `ym_core`: `YM.Gauge`, `G.Color`, `G.ad`, `colorMat_ad`, `colorMat_injective`,
`ad_jacobi`, `ad_skew`.
-/

set_option autoImplicit false
noncomputable section
namespace SYM
open YM Finset SuperCalculus
open scoped InnerProductSpace

variable (G : YM.Gauge)

/-- The standard orthonormal basis of the colour coordinates. -/
abbrev colorBasis : OrthonormalBasis G.ColorIndex ℝ G.Color :=
  EuclideanSpace.basisFun G.ColorIndex ℝ

/-- The real structure constants `f_{abc} = ⟨e_a, [e_b, e_c]⟩` of `G`. -/
def structureConst (a b d : G.ColorIndex) : ℝ :=
  ⟪colorBasis G a, G.ad (colorBasis G b) (colorBasis G d)⟫_ℝ

theorem ad_antisymm (x y : G.Color) : G.ad x y = -G.ad y x := by
  apply G.colorMat_injective
  rw [Gauge.colorMat_ad, LinearMap.map_neg, Gauge.colorMat_ad, neg_sub]

theorem ad_jacobi_cyclic (x y z : G.Color) :
    G.ad x (G.ad y z) + G.ad y (G.ad z x) + G.ad z (G.ad x y) = 0 := by
  have hj := congrArg (fun L => L z) (Gauge.ad_jacobi x y)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at hj
  rw [ad_antisymm G z x, map_neg, ad_antisymm G z (G.ad x y), hj]
  abel

theorem structureConst_skew (a b d : G.ColorIndex) :
    structureConst G a b d = -structureConst G a d b := by
  rw [structureConst, structureConst, ad_antisymm, inner_neg_right]

theorem structureConst_cyc (a b d : G.ColorIndex) :
    structureConst G a b d = structureConst G b d a := by
  rw [structureConst, structureConst, ad_antisymm, inner_neg_right, real_inner_comm,
    Gauge.ad_skew, neg_neg, real_inner_comm]

theorem inner_ad_expand (a : G.ColorIndex) (x v : G.Color) :
    ⟪colorBasis G a, G.ad x v⟫_ℝ =
      ∑ e, ⟪colorBasis G e, v⟫_ℝ * ⟪colorBasis G a, G.ad x (colorBasis G e)⟫_ℝ := by
  conv_lhs => rw [← (colorBasis G).sum_repr' v]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right]

theorem structureConst_jacobi (a b d e : G.ColorIndex) :
    ∑ k, (structureConst G a b k * structureConst G k d e
      + structureConst G a d k * structureConst G k e b
      + structureConst G a e k * structureConst G k b d) = 0 := by
  have h := congrArg (fun v => ⟪colorBasis G a, v⟫_ℝ)
    (ad_jacobi_cyclic G (colorBasis G b) (colorBasis G d) (colorBasis G e))
  simp only [inner_add_right, inner_zero_right] at h
  rw [inner_ad_expand, inner_ad_expand, inner_ad_expand, ← sum_add_distrib,
    ← sum_add_distrib] at h
  rw [← h]
  refine sum_congr rfl fun k _ => ?_
  simp only [structureConst]; ring

/-- The structure constants of `G` in any Grassmann calculus over the reals. -/
def gaugeStructureConstants {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [SuperCalculus R M] [Algebra ℝ R]
    (hconst : ∀ μ (r : ℝ), dR (M := M) μ (algebraMap ℝ R r) = 0) :
    StructureConstants R M G.ColorIndex where
  f a b d := algebraMap ℝ R (structureConst G a b d)
  skew a b d := by rw [structureConst_skew, map_neg]
  cyc a b d := by rw [structureConst_cyc]
  jacobi a b d e := by
    simp only [← map_mul, ← map_add, ← map_sum]
    rw [structureConst_jacobi, map_zero]
  const μ a b d := hconst μ _

end SYM
