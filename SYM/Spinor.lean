import SYM.Color
import SYM.Gamma

/-!
# Spinor bilinears

`sbil B N u v = ∑ N α β • B (u α) (v β)` is the bilinear `ū M v` of two four-component
spinors with `N = C M`, for any bilinear product `B` of the components. `mv P w` is the
action of an integer matrix on a spinor.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace SYM
open SuperCalculus Finset Matrix

variable {R : Type*} [CommRing R]
variable {U V W : Type*} [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

/-- Integer `4 × 4` matrices acting on spinor indices. -/
abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℤ

/-- The spinor bilinear with coefficient matrix `N`. -/
def sbil (B : U →ₗ[R] V →ₗ[R] W) (N : Mat4) (u : Fin 4 → U) (v : Fin 4 → V) : W :=
  ∑ α, ∑ β, N α β • B (u α) (v β)

/-- Action of a matrix on a spinor. -/
def mv (P : Mat4) (w : Fin 4 → V) : Fin 4 → V := fun α => ∑ β, P α β • w β

variable (B : U →ₗ[R] V →ₗ[R] W) (N N' : Mat4) (u u' : Fin 4 → U) (v v' : Fin 4 → V)

theorem sbil_add_mat : sbil B (N + N') u v = sbil B N u v + sbil B N' u v := by
  simp only [sbil, Matrix.add_apply, add_smul, sum_add_distrib]

theorem sbil_neg_mat : sbil B (-N) u v = -sbil B N u v := by
  simp only [sbil, Matrix.neg_apply, neg_smul, sum_neg_distrib]

theorem sbil_sub_mat : sbil B (N - N') u v = sbil B N u v - sbil B N' u v := by
  simp only [sbil, Matrix.sub_apply, sub_smul, sum_sub_distrib]

theorem sbil_zsmul_mat (n : ℤ) : sbil B (n • N) u v = n • sbil B N u v := by
  simp only [sbil, Matrix.smul_apply, smul_eq_mul, mul_smul, smul_sum]

theorem sbil_zero_mat : sbil B 0 u v = 0 := by
  simp only [sbil, Matrix.zero_apply, zero_smul, sum_const_zero]

theorem sbil_add_right :
    sbil B N u (fun β => v β + v' β) = sbil B N u v + sbil B N u v' := by
  simp only [sbil, map_add, smul_add, sum_add_distrib]

theorem sbil_add_left :
    sbil B N (fun α => u α + u' α) v = sbil B N u v + sbil B N u' v := by
  simp only [sbil, map_add, LinearMap.add_apply, smul_add, sum_add_distrib]

theorem sbil_zsmul_right (n : ℤ) : sbil B N u (fun β => n • v β) = n • sbil B N u v := by
  simp only [sbil, map_zsmul, smul_sum, smul_comm n]

theorem sbil_zsmul_left (n : ℤ) : sbil B N (fun α => n • u α) v = n • sbil B N u v := by
  simp only [sbil, map_zsmul, LinearMap.smul_apply, smul_sum, smul_comm n]

theorem sbil_neg_right : sbil B N u (fun β => -v β) = -sbil B N u v := by
  simp only [sbil, map_neg, smul_neg, sum_neg_distrib]

theorem sbil_smul_right (r : R) : sbil B N u (fun β => r • v β) = r • sbil B N u v := by
  simp only [sbil, map_smul, smul_sum, smul_comm r]

theorem sbil_sum_right {ι : Type*} (s : Finset ι) (w : ι → Fin 4 → V) :
    sbil B N u (fun β => ∑ i ∈ s, w i β) = ∑ i ∈ s, sbil B N u (w i) := by
  simp only [sbil, map_sum, smul_sum]
  exact (sum_congr rfl fun α _ => sum_comm).trans sum_comm

theorem sbil_sum_left {ι : Type*} (s : Finset ι) (w : ι → Fin 4 → U) :
    sbil B N (fun α => ∑ i ∈ s, w i α) v = ∑ i ∈ s, sbil B N (w i) v := by
  simp only [sbil, map_sum, LinearMap.sum_apply, smul_sum]
  exact (sum_congr rfl fun α _ => sum_comm).trans sum_comm

theorem sbil_mv_right (P : Mat4) (w : Fin 4 → V) :
    sbil B N u (mv P w) = sbil B (N * P) u w := by
  simp only [sbil, mv, map_sum, map_zsmul, smul_sum, smul_smul, Matrix.mul_apply, sum_smul]
  exact sum_congr rfl fun α _ => sum_comm

theorem sbil_mv_left (P : Mat4) (w : Fin 4 → U) :
    sbil B N (mv P w) v = sbil B (P.transpose * N) w v := by
  simp only [sbil, mv, map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, smul_sum,
    smul_smul, Matrix.mul_apply, Matrix.transpose_apply, sum_smul]
  refine (sum_swap13 _).trans ?_
  refine sum_congr rfl fun γ' _ => sum_congr rfl fun β _ => sum_congr rfl fun α _ => ?_
  rw [mul_comm]

/-- Exchanging the two spinors of a bilinear built from an antisymmetric product. -/
theorem sbil_flip (B' : V →ₗ[R] U →ₗ[R] W) (h : ∀ x y, B x y = -B' y x) :
    sbil B N u v = -sbil B' N.transpose v u := by
  simp only [sbil, Matrix.transpose_apply]
  rw [sum_comm, ← sum_neg_distrib]
  refine sum_congr rfl fun β _ => ?_
  rw [← sum_neg_distrib]
  exact sum_congr rfl fun α _ => by rw [h, smul_neg]

/-- Leibniz rule for a spinor bilinear. -/
theorem sbil_deriv {U₁ V₁ W₁ : Type*} [AddCommGroup U₁] [Module R U₁] [AddCommGroup V₁]
    [Module R V₁] [AddCommGroup W₁] [Module R W₁] (D : W →+ W₁) (B₁ : U₁ →ₗ[R] V →ₗ[R] W₁)
    (B₂ : U →ₗ[R] V₁ →ₗ[R] W₁) (dU : U → U₁) (dV : V → V₁)
    (h : ∀ x y, D (B x y) = B₁ (dU x) y + B₂ x (dV y)) :
    D (sbil B N u v) = sbil B₁ N (fun α => dU (u α)) v + sbil B₂ N u (fun β => dV (v β)) := by
  simp only [sbil, map_sum, map_zsmul, h, smul_add, sum_add_distrib]

section adjoint
variable {M : Type*} [AddCommGroup M] [Module R M] [SuperCalculus R M]
variable {I : Type*} [Fintype I] (c : StructureConstants R M I) (A : Fin 4 → I → R)

theorem covE_sbil_sm (μ : Fin 4) {ε : Fin 4 → M} (hε : ∀ α, dM μ (ε α) = 0)
    (ψ : Fin 4 → I → M) :
    covE c A μ (sbil sm N ε ψ) = sbil sm N ε (fun β => covO c A μ (ψ β)) := by
  simp only [sbil, covE_sum, covE_zsmul, covE_sm c A μ (hε _)]

theorem covO_mv (μ : Fin 4) (P : Mat4) (w : Fin 4 → I → M) (α : Fin 4) :
    covO c A μ (mv P w α) = mv P (fun β => covO c A μ (w β)) α := by
  simp only [mv, covO_sum, covO_zsmul]

theorem sbil_ms_left (X : I → R) (ε : Fin 4 → M) (ψ : Fin 4 → I → M) :
    sbil opair N (fun α => ms X (ε α)) ψ = ip X (sbil sm N ε ψ) := by
  simp only [sbil, opair_ms, map_sum, map_zsmul]

theorem sbil_ms_right (X : I → R) (ε₂ ε₁ : Fin 4 → M) :
    sbil sm N ε₂ (fun β => ms X (ε₁ β)) =
      sbil (pair : M →ₗ[R] M →ₗ[R] R) N ε₂ ε₁ • X := by
  simp only [sbil, sm_ms, sum_smul, smul_assoc]

end adjoint
end SYM
