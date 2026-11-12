import SYM.Model

/-!
# Adjoining an odd generator to a Grassmann algebra

From a Grassmann algebra with even part `Λ₀` and odd part `Λ₁`, adjoining one more odd
generator `θ` gives the Grassmann algebra with

* even part `Λ₀ ⊕ Λ₁ θ`, elements `a + ψ θ`, which is the trivial square-zero extension
  `TrivSqZeroExt Λ₀ Λ₁` because `(ψ θ)(χ θ) = 0`;
* odd part `Λ₁ ⊕ Λ₀ θ`, elements `χ + b θ`.

The products are forced by `θ² = 0` and `θ χ = -χ θ`:

* `(a + ψθ)(χ + bθ) = aχ + (ab - ψχ) θ`,
* `(χ + bθ)(ζ + dθ) = χζ + (dχ - bζ) θ`.

Starting from one generator and applying the step three times gives the exterior algebra on
four generators, in which `θ₁ θ₂ θ₃ θ₄ ≠ 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace SYM
open TrivSqZeroExt

/-- The product of two odd elements has norm at most the product of the norms. This is what
makes the adjoining step preserve the normed structure. -/
class GrassmannAlgebra.Contractive (Λ₀ Λ₁ : Type) [NormedCommRing Λ₀] [NormedAlgebra ℝ Λ₀]
    [NormedAddCommGroup Λ₁] [NormedSpace ℝ Λ₁] [Module Λ₀ Λ₁] [IsBoundedSMul Λ₀ Λ₁]
    [IsScalarTower ℝ Λ₀ Λ₁] [GrassmannAlgebra Λ₀ Λ₁] : Prop where
  norm_mul_le : ∀ θ η : Λ₁, ‖GrassmannAlgebra.mul (Λ₀ := Λ₀) θ η‖ ≤ ‖θ‖ * ‖η‖

variable (Λ₀ Λ₁ : Type) [NormedCommRing Λ₀] [NormedAlgebra ℝ Λ₀]
  [NormedAddCommGroup Λ₁] [NormedSpace ℝ Λ₁] [Module Λ₀ Λ₁] [IsBoundedSMul Λ₀ Λ₁]
  [IsScalarTower ℝ Λ₀ Λ₁] [Module Λ₀ᵐᵒᵖ Λ₁] [IsCentralScalar Λ₀ Λ₁] [IsBoundedSMul Λ₀ᵐᵒᵖ Λ₁]

/-- The even part after adjoining a generator: `a + ψ θ`. -/
abbrev AdjEven := TrivSqZeroExt Λ₀ Λ₁

/-- The odd part after adjoining a generator: `χ + b θ`, stored as the pair `(b, χ)` with the
`L¹` norm. -/
def AdjOdd := TrivSqZeroExt Λ₀ Λ₁

instance : NormedAddCommGroup (AdjOdd Λ₀ Λ₁) :=
  inferInstanceAs (NormedAddCommGroup (TrivSqZeroExt Λ₀ Λ₁))

instance : NormedSpace ℝ (AdjOdd Λ₀ Λ₁) :=
  inferInstanceAs (NormedSpace ℝ (TrivSqZeroExt Λ₀ Λ₁))

variable {Λ₀ Λ₁}

namespace AdjOdd

/-- The element `χ + b θ`. -/
def mk (b : Λ₀) (χ : Λ₁) : AdjOdd Λ₀ Λ₁ := (inl b + inr χ : TrivSqZeroExt Λ₀ Λ₁)

/-- The coefficient `b` of `θ` in `χ + b θ`. -/
def coef (y : AdjOdd Λ₀ Λ₁) : Λ₀ := fst (R := Λ₀) (M := Λ₁) y

/-- The part `χ` of `χ + b θ` not involving `θ`. -/
def base (y : AdjOdd Λ₀ Λ₁) : Λ₁ := snd (R := Λ₀) (M := Λ₁) y

@[simp] theorem coef_mk (b : Λ₀) (χ : Λ₁) : coef (mk b χ) = b := by simp [coef, mk]
@[simp] theorem base_mk (b : Λ₀) (χ : Λ₁) : base (mk b χ) = χ := by simp [base, mk]

theorem ext {y z : AdjOdd Λ₀ Λ₁} (h₁ : coef y = coef z) (h₂ : base y = base z) : y = z :=
  TrivSqZeroExt.ext h₁ h₂

@[simp] theorem coef_add (y z : AdjOdd Λ₀ Λ₁) : coef (y + z) = coef y + coef z := rfl
@[simp] theorem base_add (y z : AdjOdd Λ₀ Λ₁) : base (y + z) = base y + base z := rfl
@[simp] theorem coef_zero : coef (0 : AdjOdd Λ₀ Λ₁) = 0 := rfl
@[simp] theorem base_zero : base (0 : AdjOdd Λ₀ Λ₁) = 0 := rfl
@[simp] theorem coef_rsmul (r : ℝ) (y : AdjOdd Λ₀ Λ₁) : coef (r • y) = r • coef y := rfl
@[simp] theorem base_rsmul (r : ℝ) (y : AdjOdd Λ₀ Λ₁) : base (r • y) = r • base y := rfl

theorem norm_def (y : AdjOdd Λ₀ Λ₁) : ‖y‖ = ‖coef y‖ + ‖base y‖ := TrivSqZeroExt.norm_def _

end AdjOdd

open AdjOdd

variable [GrassmannAlgebra Λ₀ Λ₁]

local notation "gm" => GrassmannAlgebra.mul (Λ₀ := Λ₀) (Λ₁ := Λ₁)

/-- `(a + ψθ)(χ + bθ) = aχ + (ab - ψχ) θ`. -/
instance : SMul (AdjEven Λ₀ Λ₁) (AdjOdd Λ₀ Λ₁) :=
  ⟨fun x y => mk (fst x * coef y - gm (snd x) (base y)) (fst x • base y)⟩

@[simp] theorem AdjOdd.coef_smul (x : AdjEven Λ₀ Λ₁) (y : AdjOdd Λ₀ Λ₁) :
    coef (x • y) = fst x * coef y - gm (snd x) (base y) := coef_mk _ _

@[simp] theorem AdjOdd.base_smul (x : AdjEven Λ₀ Λ₁) (y : AdjOdd Λ₀ Λ₁) :
    base (x • y) = fst x • base y := base_mk _ _

instance : Module (AdjEven Λ₀ Λ₁) (AdjOdd Λ₀ Λ₁) where
  one_smul y := by refine AdjOdd.ext ?_ ?_ <;> simp
  mul_smul x x' y := by
    refine AdjOdd.ext ?_ ?_
    · simp only [AdjOdd.coef_smul, AdjOdd.base_smul, fst_mul, snd_mul, op_smul_eq_smul, map_add,
        add_apply, GrassmannAlgebra.mul_smul,
        GrassmannAlgebra.mul_smul_right]
      ring
    · simp only [AdjOdd.base_smul, fst_mul, mul_smul]
  smul_zero x := by refine AdjOdd.ext ?_ ?_ <;> simp
  smul_add x y z := by
    refine AdjOdd.ext ?_ ?_
    · simp only [AdjOdd.coef_smul, coef_add, base_add, map_add]; ring
    · simp only [AdjOdd.base_smul, base_add, smul_add]
  add_smul x x' y := by
    refine AdjOdd.ext ?_ ?_
    · simp only [AdjOdd.coef_smul, coef_add, fst_add, snd_add, map_add,
        add_apply]
      ring
    · simp only [AdjOdd.base_smul, base_add, fst_add, add_smul]
  zero_smul y := by refine AdjOdd.ext ?_ ?_ <;> simp

/-- `(χ + bθ)(ζ + dθ) = χζ + (dχ - bζ) θ`, as a bilinear map. -/
def adjMulL : AdjOdd Λ₀ Λ₁ →ₗ[ℝ] AdjOdd Λ₀ Λ₁ →ₗ[ℝ] AdjEven Λ₀ Λ₁ :=
  LinearMap.mk₂ ℝ
    (fun y z => inl (gm (base y) (base z)) + inr (coef z • base y - coef y • base z))
    (fun y y' z => by
      refine TrivSqZeroExt.ext ?_ ?_
      · simp
      · simp only [snd_add, snd_inl, snd_inr, zero_add, base_add, coef_add, smul_add, add_smul]
        abel)
    (fun r y z => by
      refine TrivSqZeroExt.ext ?_ ?_
      · simp
      · simp only [snd_add, snd_inl, snd_inr, zero_add, base_rsmul, coef_rsmul, snd_smul,
          smul_sub, smul_assoc, smul_algebra_smul_comm])
    (fun y z z' => by
      refine TrivSqZeroExt.ext ?_ ?_
      · simp
      · simp only [snd_add, snd_inl, snd_inr, zero_add, base_add, coef_add, smul_add, add_smul]
        abel)
    (fun r y z => by
      refine TrivSqZeroExt.ext ?_ ?_
      · simp
      · simp only [snd_add, snd_inl, snd_inr, zero_add, base_rsmul, coef_rsmul, snd_smul,
          smul_sub, smul_assoc, smul_algebra_smul_comm])

theorem fst_adjMulL (y z : AdjOdd Λ₀ Λ₁) : fst (adjMulL y z) = gm (base y) (base z) := by
  simp [adjMulL]

theorem snd_adjMulL (y z : AdjOdd Λ₀ Λ₁) :
    snd (adjMulL y z) = coef z • base y - coef y • base z := by
  simp [adjMulL]

variable [GrassmannAlgebra.Contractive Λ₀ Λ₁]

theorem norm_adjMulL_le (y z : AdjOdd Λ₀ Λ₁) : ‖adjMulL y z‖ ≤ 1 * ‖y‖ * ‖z‖ := by
  rw [TrivSqZeroExt.norm_def, fst_adjMulL, snd_adjMulL, AdjOdd.norm_def, AdjOdd.norm_def]
  have h1 := GrassmannAlgebra.Contractive.norm_mul_le (Λ₀ := Λ₀) (base y) (base z)
  have h2 : ‖coef z • base y - coef y • base z‖ ≤
      ‖coef z‖ * ‖base y‖ + ‖coef y‖ * ‖base z‖ :=
    (norm_sub_le _ _).trans (add_le_add (norm_smul_le _ _) (norm_smul_le _ _))
  nlinarith [mul_nonneg (norm_nonneg (coef y)) (norm_nonneg (coef z))]

instance : IsBoundedSMul (AdjEven Λ₀ Λ₁) (AdjOdd Λ₀ Λ₁) :=
  IsBoundedSMul.of_norm_smul_le fun x y => by
    rw [AdjOdd.norm_def, AdjOdd.coef_smul, AdjOdd.base_smul, TrivSqZeroExt.norm_def,
      AdjOdd.norm_def]
    have h1 := GrassmannAlgebra.Contractive.norm_mul_le (Λ₀ := Λ₀) (snd x) (base y)
    have h2 : ‖fst x * coef y - gm (snd x) (base y)‖ ≤
        ‖fst x‖ * ‖coef y‖ + ‖gm (snd x) (base y)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) le_rfl)
    have h3 := norm_smul_le (fst x) (base y)
    nlinarith [mul_nonneg (norm_nonneg (snd x)) (norm_nonneg (coef y))]

instance : IsScalarTower ℝ (AdjEven Λ₀ Λ₁) (AdjOdd Λ₀ Λ₁) :=
  ⟨fun r x y => by
    refine AdjOdd.ext ?_ ?_
    · simp only [AdjOdd.coef_smul, coef_rsmul, fst_smul, snd_smul, map_smul,
        smul_apply, smul_mul_assoc, smul_sub]
    · simp only [AdjOdd.base_smul, base_rsmul, smul_assoc]⟩

/-- The product of two odd elements of the extended algebra, as a continuous bilinear map. -/
def adjMul : AdjOdd Λ₀ Λ₁ →L[ℝ] AdjOdd Λ₀ Λ₁ →L[ℝ] AdjEven Λ₀ Λ₁ :=
  adjMulL.mkContinuous₂ 1 (fun y z => by
    have h := norm_adjMulL_le y z
    convert h using 1)

theorem adjMul_apply (y z : AdjOdd Λ₀ Λ₁) : adjMul y z = adjMulL y z :=
  LinearMap.mkContinuous₂_apply _ _ _ _

/-- **Adjoining a generator** to a Grassmann algebra gives a Grassmann algebra. -/
instance adjoin : GrassmannAlgebra (AdjEven Λ₀ Λ₁) (AdjOdd Λ₀ Λ₁) where
  mul := adjMul
  mul_smul x y z := by
    rw [adjMul_apply, adjMul_apply]
    have hc := GrassmannAlgebra.mul_cyclic (Λ₀ := Λ₀) (snd x) (base y) (base z)
    refine TrivSqZeroExt.ext ?_ ?_
    · simp only [fst_adjMulL, fst_mul, AdjOdd.base_smul, GrassmannAlgebra.mul_smul]
    · simp only [snd_adjMulL, snd_mul, fst_adjMulL, AdjOdd.base_smul, AdjOdd.coef_smul,
        op_smul_eq_smul, sub_smul, smul_sub, mul_smul]
      rw [smul_comm (coef z) (fst x) (base y)]
      linear_combination (norm := module) hc
  mul_self y := by
    rw [adjMul_apply]
    refine TrivSqZeroExt.ext ?_ ?_
    · simp only [fst_adjMulL, GrassmannAlgebra.mul_self, fst_zero]
    · simp only [snd_adjMulL, sub_self, snd_zero]
  mul_cyclic y z w := by
    rw [adjMul_apply, adjMul_apply]
    have h1 := GrassmannAlgebra.mul_antisymm (Λ₀ := Λ₀) (base z) (base y)
    have h2 := GrassmannAlgebra.mul_antisymm (Λ₀ := Λ₀) (base w) (base y)
    refine AdjOdd.ext ?_ ?_
    · simp only [AdjOdd.coef_smul, fst_adjMulL, snd_adjMulL, map_sub,
        sub_apply, GrassmannAlgebra.mul_smul]
      linear_combination coef w * h1 - coef z * h2
    · simp only [AdjOdd.base_smul, fst_adjMulL]
      exact GrassmannAlgebra.mul_cyclic (Λ₀ := Λ₀) (base y) (base z) (base w)

instance : GrassmannAlgebra.Contractive (AdjEven Λ₀ Λ₁) (AdjOdd Λ₀ Λ₁) :=
  ⟨fun y z => by
    show ‖adjMul y z‖ ≤ _
    rw [adjMul_apply]
    simpa using norm_adjMulL_le y z⟩

/-! The right action, needed to adjoin a further generator. -/

instance : Module (AdjEven Λ₀ Λ₁)ᵐᵒᵖ (AdjOdd Λ₀ Λ₁) :=
  Module.compHom _ (RingHom.fromOpposite (RingHom.id (AdjEven Λ₀ Λ₁)) fun _ _ => Commute.all _ _)

instance : IsCentralScalar (AdjEven Λ₀ Λ₁) (AdjOdd Λ₀ Λ₁) := ⟨fun _ _ => rfl⟩

instance : IsBoundedSMul (AdjEven Λ₀ Λ₁)ᵐᵒᵖ (AdjOdd Λ₀ Λ₁) :=
  IsBoundedSMul.of_norm_smul_le fun x y => by
    show ‖x.unop • y‖ ≤ ‖x‖ * ‖y‖
    rw [← MulOpposite.norm_unop]
    exact norm_smul_le _ _

/-! ## Old and new generators -/

/-- An odd element of the original algebra, as an element of the extended one. -/
def AdjOdd.old (χ : Λ₁) : AdjOdd Λ₀ Λ₁ := mk 0 χ

/-- The adjoined generator `θ`. -/
def AdjOdd.gen : AdjOdd Λ₀ Λ₁ := mk 1 0

@[simp] theorem AdjOdd.coef_old (χ : Λ₁) : coef (old (Λ₀ := Λ₀) χ) = 0 :=
  coef_mk (0 : Λ₀) χ
@[simp] theorem AdjOdd.base_old (χ : Λ₁) : base (old (Λ₀ := Λ₀) χ) = χ :=
  base_mk (0 : Λ₀) χ
@[simp] theorem AdjOdd.coef_gen : coef (gen : AdjOdd Λ₀ Λ₁) = 1 :=
  coef_mk (1 : Λ₀) (0 : Λ₁)
@[simp] theorem AdjOdd.base_gen : base (gen : AdjOdd Λ₀ Λ₁) = 0 :=
  base_mk (1 : Λ₀) (0 : Λ₁)

theorem adjoin_mul_apply (y z : AdjOdd Λ₀ Λ₁) :
    GrassmannAlgebra.mul (Λ₀ := AdjEven Λ₀ Λ₁) y z = adjMulL y z :=
  adjMul_apply y z

/-- The product of two old odd elements is their old product. -/
theorem mul_old_old (χ ζ : Λ₁) :
    GrassmannAlgebra.mul (Λ₀ := AdjEven Λ₀ Λ₁) (old (Λ₀ := Λ₀) χ) (old (Λ₀ := Λ₀) ζ) =
      inl (gm χ ζ) := by
  rw [adjoin_mul_apply]
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [fst_adjMulL]
  · simp [snd_adjMulL]

/-- `χ θ`, for an old odd element `χ`. -/
theorem mul_old_gen (χ : Λ₁) :
    GrassmannAlgebra.mul (Λ₀ := AdjEven Λ₀ Λ₁) (old (Λ₀ := Λ₀) χ) (gen : AdjOdd Λ₀ Λ₁) =
      inr χ := by
  rw [adjoin_mul_apply]
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [fst_adjMulL]
  · simp [snd_adjMulL]

/-! ## Four generators -/

namespace FourGenerators

/-- One generator: the base of the tower. -/
instance : GrassmannAlgebra ℝ ℝ := GrassmannAlgebra.oneGenerator

instance : GrassmannAlgebra.Contractive ℝ ℝ :=
  ⟨fun θ η => by
    show ‖(0 : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) θ η‖ ≤ _
    simpa using mul_nonneg (norm_nonneg θ) (norm_nonneg η)⟩

/-- Even part of the exterior algebra on two generators. -/
abbrev E₂ := AdjEven ℝ ℝ
/-- Odd part of the exterior algebra on two generators. -/
abbrev O₂ := AdjOdd ℝ ℝ

set_option synthInstance.maxHeartbeats 400000

/-! Instances are recorded at each level so that the next level finds them directly. -/

instance : NormedCommRing E₂ := inferInstance
instance : NormedAlgebra ℝ E₂ := inferInstance
instance : NormedAddCommGroup O₂ := inferInstance
instance : NormedSpace ℝ O₂ := inferInstance
instance : Module E₂ O₂ := inferInstance
instance : IsBoundedSMul E₂ O₂ := inferInstance
instance : IsScalarTower ℝ E₂ O₂ := inferInstance
instance : Module E₂ᵐᵒᵖ O₂ := inferInstance
instance : IsCentralScalar E₂ O₂ := inferInstance
instance : IsBoundedSMul E₂ᵐᵒᵖ O₂ := inferInstance
instance : GrassmannAlgebra E₂ O₂ := inferInstance
instance : GrassmannAlgebra.Contractive E₂ O₂ := inferInstance

/-- Even part of the exterior algebra on three generators. -/
abbrev E₃ := AdjEven E₂ O₂
/-- Odd part of the exterior algebra on three generators. -/
abbrev O₃ := AdjOdd E₂ O₂

instance : NormedCommRing E₃ := inferInstance
instance : NormedAlgebra ℝ E₃ := inferInstance
instance : NormedAddCommGroup O₃ := inferInstance
instance : NormedSpace ℝ O₃ := inferInstance
instance : Module E₃ O₃ := inferInstance
instance : IsBoundedSMul E₃ O₃ := inferInstance
instance : IsScalarTower ℝ E₃ O₃ := inferInstance
instance : Module E₃ᵐᵒᵖ O₃ := inferInstance
instance : IsCentralScalar E₃ O₃ := inferInstance
instance : IsBoundedSMul E₃ᵐᵒᵖ O₃ := inferInstance
instance : GrassmannAlgebra E₃ O₃ := inferInstance
instance : GrassmannAlgebra.Contractive E₃ O₃ := inferInstance

/-- Even part of the exterior algebra on four generators. -/
abbrev E₄ := AdjEven E₃ O₃
/-- Odd part of the exterior algebra on four generators. -/
abbrev O₄ := AdjOdd E₃ O₃

instance : NormedCommRing E₄ := inferInstance
instance : NormedAlgebra ℝ E₄ := inferInstance
instance : NormedAddCommGroup O₄ := inferInstance
instance : NormedSpace ℝ O₄ := inferInstance
instance : Module E₄ O₄ := inferInstance
instance : IsBoundedSMul E₄ O₄ := inferInstance
instance : IsScalarTower ℝ E₄ O₄ := inferInstance
instance : Module E₄ᵐᵒᵖ O₄ := inferInstance
instance : IsCentralScalar E₄ O₄ := inferInstance
instance : IsBoundedSMul E₄ᵐᵒᵖ O₄ := inferInstance
instance : GrassmannAlgebra E₄ O₄ := inferInstance
instance : GrassmannAlgebra.Contractive E₄ O₄ := inferInstance

/-- **The exterior algebra on four generators is a Grassmann algebra.** -/
theorem grassmann : Nonempty (GrassmannAlgebra E₄ O₄) := ⟨inferInstance⟩

/-- The four generators. -/
def θ₁ : O₄ := old (old (old (1 : ℝ)))
/-- The second generator. -/
def θ₂ : O₄ := old (old gen)
/-- The third generator. -/
def θ₃ : O₄ := old gen
/-- The fourth generator. -/
def θ₄ : O₄ := gen

/-- **Quartic fermion terms do not vanish:** `(θ₁ θ₂)(θ₃ θ₄) ≠ 0`. -/
theorem quartic_ne_zero :
    GrassmannAlgebra.mul (Λ₀ := E₄) θ₁ θ₂ * GrassmannAlgebra.mul (Λ₀ := E₄) θ₃ θ₄ ≠ 0 := by
  unfold θ₁ θ₂ θ₃ θ₄
  rw [mul_old_old, mul_old_old, mul_old_gen, mul_old_gen, inl_mul_inr]
  intro h
  have h1 := congrArg (fun e : E₄ => snd (coef (snd e))) h
  simp at h1

/-- Fermion bilinears do not vanish: `θ₁ θ₂ ≠ 0`. -/
theorem bilinear_ne_zero : GrassmannAlgebra.mul (Λ₀ := E₄) θ₁ θ₂ ≠ 0 := fun h =>
  quartic_ne_zero (by rw [h, zero_mul])

/-- Smooth fields with values in the exterior algebra on four generators form a Grassmann
calculus. -/
example : SuperCalculus (smoothEven E₄) (smoothOdd E₄ O₄) := inferInstance

end FourGenerators
end SYM
