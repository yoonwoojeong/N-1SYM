import SYM.Calculus

/-!
# Adjoint-valued fields

Fields with values in a Lie algebra, in components with respect to a basis in which the
structure constants `f a b c` are totally antisymmetric (an orthonormal basis for an
invariant inner product).

* even adjoint fields are `I → R`, odd adjoint fields are `I → M`;
* `brk`, `act`: the bracket of an even field with an even or an odd field;
* `ip`, `opair`: the invariant inner product of two even or two odd fields;
* `sm`, `ms`: the product of an odd scalar with an odd or an even adjoint field;
* `covE`, `covO`: covariant derivatives, `fieldStrength`, and the Bianchi identity.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace SYM
open SuperCalculus Finset

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [SuperCalculus R M]
variable {I : Type*} [Fintype I]

/-! ## Relabelling triple sums -/

section sums
variable {P : Type*} [AddCommMonoid P] (g : I → I → I → P)

theorem sum_rot : ∑ a, ∑ b, ∑ c, g a b c = ∑ a, ∑ b, ∑ c, g c a b :=
  calc _ = ∑ b, ∑ a, ∑ c, g a b c := sum_comm
    _ = _ := sum_congr rfl fun _ _ => sum_comm

theorem sum_rot' : ∑ a, ∑ b, ∑ c, g a b c = ∑ a, ∑ b, ∑ c, g b c a :=
  calc _ = ∑ a, ∑ c, ∑ b, g a b c := sum_congr rfl fun _ _ => sum_comm
    _ = _ := sum_comm

theorem sum_swap13 : ∑ a, ∑ b, ∑ c, g a b c = ∑ a, ∑ b, ∑ c, g c b a :=
  calc _ = ∑ b, ∑ a, ∑ c, g a b c := sum_comm
    _ = ∑ b, ∑ c, ∑ a, g a b c := sum_congr rfl fun _ _ => sum_comm
    _ = _ := sum_comm

end sums

/-- Structure constants of a Lie algebra in an orthonormal basis: totally antisymmetric,
constant, and satisfying the Jacobi identity. -/
structure StructureConstants (R M I : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [SuperCalculus R M] [Fintype I] where
  f : I → I → I → R
  skew : ∀ a b c, f a b c = -f a c b
  cyc : ∀ a b c, f a b c = f b c a
  jacobi : ∀ a b c d, ∑ e, (f a b e * f e c d + f a c e * f e d b + f a d e * f e b c) = 0
  const : ∀ μ a b c, dR (M := M) μ (f a b c) = 0

namespace StructureConstants
variable (c : StructureConstants R M I)

theorem swap13 (a b d : I) : c.f d b a = -c.f a b d := by
  rw [c.cyc d b a, c.skew b a d, c.cyc b d a, c.cyc d a b]

end StructureConstants

/-! ## Bilinear operations -/

/-- Invariant inner product of two even adjoint fields. -/
def ip : (I → R) →ₗ[R] (I → R) →ₗ[R] R :=
  LinearMap.mk₂ R (fun X Y => ∑ a, X a * Y a)
    (fun X X' Y => by simp [add_mul, sum_add_distrib])
    (fun r X Y => by simp [mul_sum, mul_assoc])
    (fun X Y Y' => by simp [mul_add, sum_add_distrib])
    (fun r X Y => by simp [mul_sum, mul_left_comm])

theorem ip_apply (X Y : I → R) : ip X Y = ∑ a, X a * Y a := rfl

theorem ip_comm (X Y : I → R) : ip X Y = ip Y X := by
  simp only [ip_apply, mul_comm]

/-- Invariant inner product of two odd adjoint fields. -/
def opair : (I → M) →ₗ[R] (I → M) →ₗ[R] R :=
  LinearMap.mk₂ R (fun ψ χ => ∑ a, pair (ψ a) (χ a))
    (fun ψ ψ' χ => by simp [sum_add_distrib])
    (fun r ψ χ => by simp [mul_sum])
    (fun ψ χ χ' => by simp [sum_add_distrib])
    (fun r ψ χ => by simp [mul_sum])

theorem opair_apply (ψ χ : I → M) : opair ψ χ = ∑ a, pair (ψ a) (χ a) := rfl

theorem opair_antisymm (ψ χ : I → M) : opair ψ χ = -opair χ ψ := by
  simp only [opair_apply, ← sum_neg_distrib]
  exact sum_congr rfl fun a _ => pair_antisymm _ _

/-- Product of an odd scalar and an odd adjoint field. -/
def sm : M →ₗ[R] (I → M) →ₗ[R] (I → R) :=
  LinearMap.mk₂ R (fun θ ψ a => pair θ (ψ a))
    (fun θ θ' ψ => by funext a; simp)
    (fun r θ ψ => by funext a; simp)
    (fun θ ψ ψ' => by funext a; simp)
    (fun r θ ψ => by funext a; simp)

theorem sm_apply (θ : M) (ψ : I → M) (a : I) : sm θ ψ a = pair θ (ψ a) := rfl

/-- Product of an even adjoint field and an odd scalar. -/
def ms : (I → R) →ₗ[R] M →ₗ[R] (I → M) :=
  LinearMap.mk₂ R (fun X θ a => X a • θ)
    (fun X X' θ => by funext a; simp [add_smul])
    (fun r X θ => by funext a; simp [mul_smul])
    (fun X θ θ' => by funext a; simp)
    (fun r X θ => by funext a; exact smul_comm _ _ _)

theorem ms_apply (X : I → R) (θ : M) (a : I) : ms X θ a = X a • θ := rfl

variable (c : StructureConstants R M I)

/-- Bracket of two even adjoint fields. -/
def brk : (I → R) →ₗ[R] (I → R) →ₗ[R] (I → R) :=
  LinearMap.mk₂ R (fun X Y a => ∑ b, ∑ d, c.f a b d * (X b * Y d))
    (fun X X' Y => by
      funext a; simp only [Pi.add_apply, ← sum_add_distrib]
      exact sum_congr rfl fun b _ => sum_congr rfl fun d _ => by ring)
    (fun r X Y => by
      funext a; simp only [Pi.smul_apply, smul_eq_mul, mul_sum]
      exact sum_congr rfl fun b _ => sum_congr rfl fun d _ => by ring)
    (fun X Y Y' => by
      funext a; simp only [Pi.add_apply, ← sum_add_distrib]
      exact sum_congr rfl fun b _ => sum_congr rfl fun d _ => by ring)
    (fun r X Y => by
      funext a; simp only [Pi.smul_apply, smul_eq_mul, mul_sum]
      exact sum_congr rfl fun b _ => sum_congr rfl fun d _ => by ring)

theorem brk_apply (X Y : I → R) (a : I) :
    brk c X Y a = ∑ b, ∑ d, c.f a b d * (X b * Y d) := rfl

/-- Bracket of an even and an odd adjoint field. -/
def act : (I → R) →ₗ[R] (I → M) →ₗ[R] (I → M) :=
  LinearMap.mk₂ R (fun X ψ a => ∑ b, ∑ d, (c.f a b d * X b) • ψ d)
    (fun X X' ψ => by
      funext a; simp only [Pi.add_apply, ← sum_add_distrib]
      exact sum_congr rfl fun b _ => sum_congr rfl fun d _ => by rw [mul_add, add_smul])
    (fun r X ψ => by
      funext a; simp only [Pi.smul_apply, smul_eq_mul, smul_sum, smul_smul]
      exact sum_congr rfl fun b _ => sum_congr rfl fun d _ => by congr 1; ring)
    (fun X ψ ψ' => by
      funext a; simp only [Pi.add_apply, ← sum_add_distrib]
      exact sum_congr rfl fun b _ => sum_congr rfl fun d _ => by rw [smul_add])
    (fun r X ψ => by
      funext a; simp only [Pi.smul_apply, smul_sum, smul_smul]
      exact sum_congr rfl fun b _ => sum_congr rfl fun d _ => by congr 1; ring)

theorem act_apply (X : I → R) (ψ : I → M) (a : I) :
    act c X ψ a = ∑ b, ∑ d, (c.f a b d * X b) • ψ d := rfl

/-! ## Algebraic identities -/

theorem brk_antisymm (X Y : I → R) : brk c X Y = -brk c Y X := by
  funext a
  rw [Pi.neg_apply, brk_apply, brk_apply, sum_comm, ← sum_neg_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun d _ => ?_
  rw [c.skew a d b]; ring

theorem brk_self (X : I → R) : brk c X X = 0 := by
  funext a
  have h := congrFun (brk_antisymm c X X) a
  rw [Pi.neg_apply] at h
  exact two_torsion (M := M) _ (by rw [two_mul]; nth_rewrite 1 [h]; exact neg_add_cancel _)

/-- Invariance of the inner product. -/
theorem ip_brk (X Y Z : I → R) : ip (brk c X Y) Z = ip X (brk c Y Z) := by
  simp only [ip_apply, brk_apply, sum_mul, mul_sum]
  rw [sum_rot' fun a b d => X a * (c.f a b d * (Y b * Z d))]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun d _ => ?_
  rw [c.cyc a b d]; ring

theorem ip_brk_left (A X Y : I → R) : ip (brk c A X) Y + ip X (brk c A Y) = 0 := by
  rw [ip_brk, ip_comm X, ip_brk, brk_antisymm c Y X]; simp

theorem opair_act (X : I → R) (ψ χ : I → M) :
    opair (act c X ψ) χ + opair ψ (act c X χ) = 0 := by
  simp only [opair_apply, act_apply, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [sum_swap13 fun a b d => c.f a b d * X b * pair (ψ a) (χ d), ← sum_add_distrib]
  refine sum_eq_zero fun a _ => ?_
  rw [← sum_add_distrib]
  refine sum_eq_zero fun b _ => ?_
  rw [← sum_add_distrib]
  refine sum_eq_zero fun d _ => ?_
  rw [c.swap13 a b d]; ring

theorem sm_act (θ : M) (X : I → R) (ψ : I → M) : sm θ (act c X ψ) = brk c X (sm θ ψ) := by
  funext a
  simp only [sm_apply, act_apply, brk_apply, map_sum, map_smul, smul_eq_mul, mul_assoc]

theorem act_ms (X Y : I → R) (θ : M) : act c X (ms Y θ) = ms (brk c X Y) θ := by
  funext a
  simp only [ms_apply, act_apply, brk_apply, sum_smul, smul_smul, mul_assoc]

theorem opair_ms (X : I → R) (θ : M) (ψ : I → M) : opair (ms X θ) ψ = ip X (sm θ ψ) := by
  simp only [opair_apply, ms_apply, ip_apply, sm_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul]

theorem sm_ms (θ η : M) (X : I → R) : sm θ (ms X η) = pair θ η • X := by
  funext a
  simp only [sm_apply, ms_apply, map_smul, smul_eq_mul, Pi.smul_apply, mul_comm]

theorem ms_sm (θ η : M) (ψ : I → M) : ms (sm θ ψ) η = pair η θ • ψ := by
  funext a
  simp only [sm_apply, ms_apply, Pi.smul_apply]
  rw [pair_cyclic, pair_cyclic]

/-- `ψ₁ (θ ψ₂) ψ₃` contracted with the structure constants. -/
def T3 (ψ₁ : I → M) (θ : M) (ψ₂ ψ₃ : I → M) : R := opair ψ₁ (act c (sm θ ψ₂) ψ₃)

theorem T3_apply (ψ₁ : I → M) (θ : M) (ψ₂ ψ₃ : I → M) : T3 c ψ₁ θ ψ₂ ψ₃ =
    ∑ a, ∑ b, ∑ d, c.f a b d * pair θ (ψ₂ b) * pair (ψ₁ a) (ψ₃ d) := by
  simp only [T3, opair_apply, act_apply, sm_apply, map_sum, map_smul, smul_eq_mul]

theorem T3_swap13 (ψ₁ : I → M) (θ : M) (ψ₂ ψ₃ : I → M) :
    T3 c ψ₃ θ ψ₂ ψ₁ = T3 c ψ₁ θ ψ₂ ψ₃ := by
  rw [T3_apply, T3_apply, sum_swap13]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun d _ => ?_
  rw [c.swap13 a b d, pair_antisymm (ψ₃ d) (ψ₁ a)]; ring

theorem T3_swap23 (ψ₁ : I → M) (θ : M) (ψ₂ ψ₃ : I → M) :
    T3 c ψ₁ θ ψ₃ ψ₂ = T3 c ψ₁ θ ψ₂ ψ₃ := by
  rw [T3_apply, T3_apply]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun b _ => sum_congr rfl fun d _ => ?_
  have h := pair_mul_pair_swap θ (ψ₃ d) (ψ₁ a) (ψ₂ b)
  rw [c.skew a d b]
  linear_combination (-c.f a b d) * h

/-- `(θ₁ ψ₁)(θ₂ ψ₂)` contracted with the structure constants. -/
theorem sm_act_sm_apply (θ₁ θ₂ : M) (ψ₁ ψ₂ : I → M) (a : I) :
    sm θ₂ (act c (sm θ₁ ψ₁) ψ₂) a =
      ∑ b, ∑ d, c.f a b d * (pair θ₁ (ψ₁ b) * pair θ₂ (ψ₂ d)) := by
  simp only [sm_apply, act_apply, map_sum, map_smul, smul_eq_mul, mul_assoc]

theorem sm_act_sm_antisymm (θ₁ θ₂ : M) (ψ₁ ψ₂ : I → M) :
    sm θ₁ (act c (sm θ₂ ψ₂) ψ₁) = -sm θ₂ (act c (sm θ₁ ψ₁) ψ₂) := by
  funext a
  rw [Pi.neg_apply, sm_act_sm_apply, sm_act_sm_apply, sum_comm, ← sum_neg_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun d _ => ?_
  rw [c.skew a d b]; ring

theorem sm_act_sm_symm (θ₁ θ₂ : M) (ψ₁ ψ₂ : I → M) :
    sm θ₂ (act c (sm θ₁ ψ₂) ψ₁) = sm θ₂ (act c (sm θ₁ ψ₁) ψ₂) := by
  funext a
  rw [sm_act_sm_apply, sm_act_sm_apply, sum_comm]
  refine sum_congr rfl fun b _ => sum_congr rfl fun d _ => ?_
  rw [c.skew a d b, pair_mul_pair_swap θ₁ (ψ₂ d) θ₂ (ψ₁ b)]; ring

theorem brk_brk_apply (X Y Z : I → R) (a : I) : brk c X (brk c Y Z) a =
    ∑ b, ∑ d, ∑ e, (∑ k, c.f a b k * c.f k d e) * (X b * (Y d * Z e)) := by
  simp only [brk_apply, mul_sum, sum_mul]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun e _ => sum_congr rfl fun k _ => by ring

/-- The Jacobi identity. -/
theorem brk_jacobi (X Y Z : I → R) :
    brk c X (brk c Y Z) + brk c Y (brk c Z X) + brk c Z (brk c X Y) = 0 := by
  funext a
  simp only [Pi.add_apply, Pi.zero_apply, brk_brk_apply]
  rw [sum_rot' fun b d e => (∑ k, c.f a b k * c.f k d e) * (Y b * (Z d * X e)),
    sum_rot fun b d e => (∑ k, c.f a b k * c.f k d e) * (Z b * (X d * Y e)),
    ← sum_add_distrib, ← sum_add_distrib]
  refine sum_eq_zero fun b _ => ?_
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_eq_zero fun d _ => ?_
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_eq_zero fun e _ => ?_
  have h := c.jacobi a b d e
  simp only [sum_add_distrib] at h
  linear_combination (X b * Y d * Z e) * h

/-! ## Derivatives -/

/-- Coordinate derivative of an even adjoint field. -/
def dE (μ : Fin 4) : (I → R) →+ (I → R) := (dR (M := M) μ).compLeft I

/-- Coordinate derivative of an odd adjoint field. -/
def dO (μ : Fin 4) : (I → M) →+ (I → M) := (dM μ).compLeft I

local notation "∂E" => dE (R := R) (M := M) (I := I)
local notation "∂R" => dR (R := R) (M := M)

theorem dE_apply (μ : Fin 4) (X : I → R) (a : I) : ∂E μ X a = ∂R μ (X a) := rfl
theorem dO_apply (μ : Fin 4) (ψ : I → M) (a : I) : dO μ ψ a = dM μ (ψ a) := rfl

theorem dE_comm (μ ν : Fin 4) (X : I → R) : ∂E μ (∂E ν X) = ∂E ν (∂E μ X) := by
  funext a; simp only [dE_apply, dR_comm]

theorem dR_ip (μ : Fin 4) (X Y : I → R) :
    ∂R μ (ip X Y) = ip (∂E μ X) Y + ip X (∂E μ Y) := by
  simp only [ip_apply, map_sum, dR_mul, sum_add_distrib, dE_apply]

theorem dR_opair (μ : Fin 4) (ψ χ : I → M) :
    ∂R μ (opair ψ χ) = opair (dO μ ψ) χ + opair ψ (dO μ χ) := by
  simp only [opair_apply, map_sum, dR_pair, sum_add_distrib, dO_apply]

theorem dE_sm (μ : Fin 4) (θ : M) (ψ : I → M) :
    ∂E μ (sm θ ψ) = sm (dM μ θ) ψ + sm θ (dO μ ψ) := by
  funext a; simp only [dE_apply, sm_apply, dR_pair, Pi.add_apply, dO_apply]

theorem dO_ms (μ : Fin 4) (X : I → R) (θ : M) :
    dO μ (ms X θ) = ms (∂E μ X) θ + ms X (dM μ θ) := by
  funext a; simp only [dO_apply, ms_apply, dM_smul, Pi.add_apply, dE_apply]

theorem dE_brk (μ : Fin 4) (X Y : I → R) :
    ∂E μ (brk c X Y) = brk c (∂E μ X) Y + brk c X (∂E μ Y) := by
  funext a
  simp only [dE_apply, brk_apply, Pi.add_apply, map_sum, dR_mul, c.const, zero_mul, zero_add,
    mul_add, sum_add_distrib]

theorem dO_act (μ : Fin 4) (X : I → R) (ψ : I → M) :
    dO μ (act c X ψ) = act c (∂E μ X) ψ + act c X (dO μ ψ) := by
  funext a
  simp only [dO_apply, act_apply, Pi.add_apply, map_sum, dM_smul, dR_mul, c.const, zero_mul,
    zero_add, sum_add_distrib, dE_apply]

theorem dE_smul (μ : Fin 4) (r : R) (X : I → R) :
    ∂E μ (r • X) = ∂R μ r • X + r • ∂E μ X := by
  funext a; simp only [dE_apply, Pi.smul_apply, smul_eq_mul, dR_mul, Pi.add_apply]

theorem dO_smul (μ : Fin 4) (r : R) (ψ : I → M) :
    dO μ (r • ψ) = ∂R μ r • ψ + r • dO μ ψ := by
  funext a; simp only [dO_apply, Pi.smul_apply, dM_smul, Pi.add_apply]

/-! ## Covariant derivatives and field strength -/

/-- Covariant derivative of an even adjoint field, `D_μ X = ∂_μ X + [A_μ, X]`. -/
def covE (A : Fin 4 → I → R) (μ : Fin 4) (X : I → R) : I → R := ∂E μ X + brk c (A μ) X

/-- Covariant derivative of an odd adjoint field. -/
def covO (A : Fin 4 → I → R) (μ : Fin 4) (ψ : I → M) : I → M := dO μ ψ + act c (A μ) ψ

/-- Field strength `F_μν = ∂_μ A_ν - ∂_ν A_μ + [A_μ, A_ν]`. -/
def fieldStrength (A : Fin 4 → I → R) (μ ν : Fin 4) : I → R :=
  ∂E μ (A ν) - ∂E ν (A μ) + brk c (A μ) (A ν)

variable (A : Fin 4 → I → R)

theorem covE_add (μ : Fin 4) (X Y : I → R) : covE c A μ (X + Y) = covE c A μ X + covE c A μ Y := by
  simp only [covE, map_add]; abel

theorem covE_neg (μ : Fin 4) (X : I → R) : covE c A μ (-X) = -covE c A μ X := by
  simp only [covE, map_neg]; abel

theorem covE_sub (μ : Fin 4) (X Y : I → R) : covE c A μ (X - Y) = covE c A μ X - covE c A μ Y := by
  simp only [covE, map_sub]; abel

theorem covE_zsmul (μ : Fin 4) (n : ℤ) (X : I → R) : covE c A μ (n • X) = n • covE c A μ X := by
  simp only [covE, map_zsmul, smul_add]

theorem covE_sum {ι : Type*} (s : Finset ι) (μ : Fin 4) (X : ι → I → R) :
    covE c A μ (∑ i ∈ s, X i) = ∑ i ∈ s, covE c A μ (X i) := by
  simp only [covE, map_sum, sum_add_distrib]

theorem covO_add (μ : Fin 4) (ψ χ : I → M) : covO c A μ (ψ + χ) = covO c A μ ψ + covO c A μ χ := by
  simp only [covO, map_add]; abel

theorem covO_zsmul (μ : Fin 4) (n : ℤ) (ψ : I → M) : covO c A μ (n • ψ) = n • covO c A μ ψ := by
  simp only [covO, map_zsmul, smul_add]

theorem covO_sum {ι : Type*} (s : Finset ι) (μ : Fin 4) (ψ : ι → I → M) :
    covO c A μ (∑ i ∈ s, ψ i) = ∑ i ∈ s, covO c A μ (ψ i) := by
  simp only [covO, map_sum, sum_add_distrib]

/-- A constant even scalar passes through the covariant derivative. -/
theorem covE_smul (μ : Fin 4) {r : R} (hr : ∂R μ r = 0) (X : I → R) :
    covE c A μ (r • X) = r • covE c A μ X := by
  simp only [covE, dE_smul, hr, zero_smul, zero_add, map_smul, smul_add]

theorem covO_smul (μ : Fin 4) {r : R} (hr : ∂R μ r = 0) (ψ : I → M) :
    covO c A μ (r • ψ) = r • covO c A μ ψ := by
  simp only [covO, dO_smul, hr, zero_smul, zero_add, map_smul, smul_add]

/-- Covariant Leibniz rule for the inner product. -/
theorem dR_ip_cov (μ : Fin 4) (X Y : I → R) :
    ∂R μ (ip X Y) = ip (covE c A μ X) Y + ip X (covE c A μ Y) := by
  have h := ip_brk_left c (A μ) X Y
  simp only [covE, dR_ip, map_add, LinearMap.add_apply]
  linear_combination -h

theorem dR_opair_cov (μ : Fin 4) (ψ χ : I → M) :
    ∂R μ (opair ψ χ) = opair (covO c A μ ψ) χ + opair ψ (covO c A μ χ) := by
  have h := opair_act c (A μ) ψ χ
  simp only [covO, dR_opair, map_add, LinearMap.add_apply]
  linear_combination -h

/-- A constant odd scalar passes through the covariant derivative. -/
theorem covE_sm (μ : Fin 4) {θ : M} (hθ : dM μ θ = 0) (ψ : I → M) :
    covE c A μ (sm θ ψ) = sm θ (covO c A μ ψ) := by
  simp only [covE, covO, dE_sm, hθ, map_zero, LinearMap.zero_apply, zero_add, map_add, sm_act]

theorem covO_ms (μ : Fin 4) {θ : M} (hθ : dM μ θ = 0) (X : I → R) :
    covO c A μ (ms X θ) = ms (covE c A μ X) θ := by
  simp only [covE, covO, dO_ms, hθ, map_zero, add_zero, map_add, LinearMap.add_apply, act_ms]

theorem fieldStrength_antisymm (μ ν : Fin 4) :
    fieldStrength c A ν μ = -fieldStrength c A μ ν := by
  simp only [fieldStrength]
  rw [brk_antisymm c (A ν) (A μ)]; abel

theorem fieldStrength_self (μ : Fin 4) : fieldStrength c A μ μ = 0 := by
  simp only [fieldStrength, brk_self, sub_self, add_zero]

/-- The Bianchi identity `D_μ F_ρσ + D_ρ F_σμ + D_σ F_μρ = 0`. -/
theorem bianchi (μ ρ σ : Fin 4) :
    covE c A μ (fieldStrength c A ρ σ) + covE c A ρ (fieldStrength c A σ μ)
      + covE c A σ (fieldStrength c A μ ρ) = 0 := by
  have j := brk_jacobi c (A μ) (A ρ) (A σ)
  have e1 := brk_antisymm c (∂E μ (A ρ)) (A σ)
  have e2 := brk_antisymm c (∂E ρ (A σ)) (A μ)
  have e3 := brk_antisymm c (∂E σ (A μ)) (A ρ)
  have c1 := dE_comm (R := R) (M := M) μ ρ (A σ)
  have c2 := dE_comm (R := R) (M := M) ρ σ (A μ)
  have c3 := dE_comm (R := R) (M := M) σ μ (A ρ)
  simp only [covE, fieldStrength, map_add, map_sub, dE_brk]
  linear_combination (norm := abel) j + e1 + e2 + e3 + c1 + c2 + c3

/-! ## Exact expansions

These justify the first variations used later: `dF` and `dDlam` are the parts linear in the
variation `a`, `χ`. -/

/-- `F(A + a) = F(A) + (D_μ a_ν - D_ν a_μ) + [a_μ, a_ν]`. -/
theorem fieldStrength_add (a : Fin 4 → I → R) (μ ν : Fin 4) :
    fieldStrength c (fun μ => A μ + a μ) μ ν =
      fieldStrength c A μ ν + (covE c A μ (a ν) - covE c A ν (a μ)) + brk c (a μ) (a ν) := by
  simp only [fieldStrength, covE, map_add, LinearMap.add_apply]
  rw [brk_antisymm c (a μ) (A ν)]; abel

/-- `D^{A + a}_μ (ψ + χ) = D_μ ψ + (D_μ χ + [a_μ, ψ]) + [a_μ, χ]`. -/
theorem covO_add_gauge (a : Fin 4 → I → R) (μ : Fin 4) (ψ χ : I → M) :
    covO c (fun μ => A μ + a μ) μ (ψ + χ) =
      covO c A μ ψ + (covO c A μ χ + act c (a μ) ψ) + act c (a μ) χ := by
  simp only [covO, map_add, LinearMap.add_apply]; abel

end SYM
