import SYM.Closure

/-!
# The first variation, derived

`IsFirstVariation f v` says that `v` is the coefficient of `t` in a polynomial expansion
`f t = f 0 + t v + t² r₂ + t³ r₃ + t⁴ r₄` valid for every integer `t`. In a module without
2- and 3-torsion this coefficient is unique (`IsFirstVariation.unique`), so it is *the* first
variation of `f`.

The formulas `dLagrangian` and `dsusy`, which `SYM/Theory.lean` and `SYM/Closure.lean` write
down by the Leibniz rule, are proved here to be the first variations of the Lagrangian and of
the supersymmetry transformation along `t ↦ Φ + t Ψ`. The two main theorems are restated in
that form.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace SYM
open SuperCalculus Finset Matrix

/-- `v` is the first-order coefficient of `f` at `0`. -/
def IsFirstVariation {V : Type*} [AddCommGroup V] (f : ℤ → V) (v : V) : Prop :=
  ∃ r₂ r₃ r₄ : V, ∀ t : ℤ, f t = f 0 + t • v + t ^ 2 • r₂ + t ^ 3 • r₃ + t ^ 4 • r₄

/-- The first variation is unique in a module without 2- and 3-torsion. -/
theorem IsFirstVariation.unique {V : Type*} [AddCommGroup V] {f : ℤ → V} {v v' : V}
    (h2 : ∀ a : V, (2 : ℤ) • a = 0 → a = 0) (h3 : ∀ a : V, (3 : ℤ) • a = 0 → a = 0)
    (h : IsFirstVariation f v) (h' : IsFirstVariation f v') : v = v' := by
  obtain ⟨r₂, r₃, r₄, hr⟩ := h
  obtain ⟨s₂, s₃, s₄, hs⟩ := h'
  have e : ∀ t : ℤ, t • (v - v') + t ^ 2 • (r₂ - s₂) + t ^ 3 • (r₃ - s₃)
      + t ^ 4 • (r₄ - s₄) = 0 := fun t => by
    have := (hr t).symm.trans (hs t)
    linear_combination (norm := module) this
  have a1 := e 1
  have b1 := e (-1)
  have a2 := e 2
  have b2 := e (-2)
  have k1 : (2 : ℤ) • ((v - v') + (r₃ - s₃)) = 0 := by
    linear_combination (norm := module) a1 - b1
  have k1' := h2 _ k1
  have k2 : (2 : ℤ) • ((2 : ℤ) • (v - v') + (8 : ℤ) • (r₃ - s₃)) = 0 := by
    linear_combination (norm := module) a2 - b2
  have k2' := h2 _ k2
  have k3 : (2 : ℤ) • ((3 : ℤ) • (v - v')) = 0 := by
    linear_combination (norm := module) (8 : ℤ) • k1' - k2'
  exact sub_eq_zero.mp (h3 _ (h2 _ k3))

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [SuperCalculus R M]
variable {I : Type*} [Fintype I] (c : StructureConstants R M I)

local notation "dRM" => dR (R := R) (M := M)

/-- The dependence of the Lagrangian on the bilinears `F·F`, `λ̄ γ^μ D_μ λ`, `D·D`. -/
def lagShape (x : Fin 4 → Fin 4 → R) (y : Fin 4 → R) (z : R) : R :=
  -(∑ μ, ∑ ν, (η μ * η ν) • x μ ν) - (2 : ℤ) • ∑ μ, y μ + (2 : ℤ) • z

theorem lagShape_add (x x' : Fin 4 → Fin 4 → R) (y y' : Fin 4 → R) (z z' : R) :
    lagShape (fun μ ν => x μ ν + x' μ ν) (fun μ => y μ + y' μ) (z + z') =
      lagShape x y z + lagShape x' y' z' := by
  simp only [lagShape, smul_add, sum_add_distrib]; abel

theorem lagShape_zsmul (n : ℤ) (x : Fin 4 → Fin 4 → R) (y : Fin 4 → R) (z : R) :
    lagShape (fun μ ν => n • x μ ν) (fun μ => n • y μ) (n • z) = n • lagShape x y z := by
  have h : ∀ μ ν, (η μ * η ν) • n • x μ ν = n • ((η μ * η ν) • x μ ν) :=
    fun _ _ => smul_comm _ _ _
  simp only [lagShape, h, ← smul_sum]
  module

namespace Fields
variable (Φ Ψ : Fields R M I)

/-- The configuration `Φ + t Ψ`. -/
def shift (t : ℤ) : Fields R M I where
  A μ := Φ.A μ + t • Ψ.A μ
  lam α := Φ.lam α + t • Ψ.lam α
  D := Φ.D + t • Ψ.D

/-- `F(A + t a) = F + t δF + t² [a, a]`. -/
theorem F_shift (t : ℤ) (μ ν : Fin 4) : (Φ.shift Ψ t).F c μ ν =
    Φ.F c μ ν + t • Φ.dF c Ψ.A μ ν + t ^ 2 • brk c (Ψ.A μ) (Ψ.A ν) := by
  show fieldStrength c (fun μ => Φ.A μ + t • Ψ.A μ) μ ν = _
  rw [fieldStrength_add]
  simp only [covE_zsmul, map_zsmul, LinearMap.smul_apply, smul_smul, F, dF, ← smul_sub, ← sq]

/-- `D_μ λ` along `Φ + t Ψ`. -/
theorem Dlam_shift (t : ℤ) (μ β : Fin 4) : (Φ.shift Ψ t).Dlam c μ β =
    Φ.Dlam c μ β + t • Φ.dDlam c Ψ μ β + t ^ 2 • act c (Ψ.A μ) (Ψ.lam β) := by
  show covO c (fun μ => Φ.A μ + t • Ψ.A μ) μ (Φ.lam β + t • Ψ.lam β) = _
  rw [covO_add_gauge]
  simp only [covO_zsmul, map_zsmul, LinearMap.smul_apply, smul_smul, ← smul_add, ← sq]
  rfl

/-- The exact expansion of the Lagrangian along `Φ + t Ψ`. Its linear coefficient is
`dLagrangian`. -/
theorem lagrangian_shift (t : ℤ) : (Φ.shift Ψ t).lagrangian c =
    Φ.lagrangian c + t • Φ.dLagrangian c Ψ
      + t ^ 2 • lagShape
          (fun μ ν => ip (Φ.dF c Ψ.A μ ν) (Φ.dF c Ψ.A μ ν)
            + (2 : ℤ) • ip (Φ.F c μ ν) (brk c (Ψ.A μ) (Ψ.A ν)))
          (fun μ => sbil opair (Cγ μ) Ψ.lam (Φ.dDlam c Ψ μ)
            + sbil opair (Cγ μ) Φ.lam (fun β => act c (Ψ.A μ) (Ψ.lam β)))
          (ip Ψ.D Ψ.D)
      + t ^ 3 • lagShape
          (fun μ ν => (2 : ℤ) • ip (Φ.dF c Ψ.A μ ν) (brk c (Ψ.A μ) (Ψ.A ν)))
          (fun μ => sbil opair (Cγ μ) Ψ.lam (fun β => act c (Ψ.A μ) (Ψ.lam β))) 0
      + t ^ 4 • lagShape
          (fun μ ν => ip (brk c (Ψ.A μ) (Ψ.A ν)) (brk c (Ψ.A μ) (Ψ.A ν))) (fun _ => 0) 0 := by
  have hF : ∀ μ ν, ip ((Φ.shift Ψ t).F c μ ν) ((Φ.shift Ψ t).F c μ ν) =
      ip (Φ.F c μ ν) (Φ.F c μ ν) + t • ((2 : ℤ) • ip (Φ.F c μ ν) (Φ.dF c Ψ.A μ ν))
        + t ^ 2 • (ip (Φ.dF c Ψ.A μ ν) (Φ.dF c Ψ.A μ ν)
          + (2 : ℤ) • ip (Φ.F c μ ν) (brk c (Ψ.A μ) (Ψ.A ν)))
        + t ^ 3 • ((2 : ℤ) • ip (Φ.dF c Ψ.A μ ν) (brk c (Ψ.A μ) (Ψ.A ν)))
        + t ^ 4 • ip (brk c (Ψ.A μ) (Ψ.A ν)) (brk c (Ψ.A μ) (Ψ.A ν)) := by
    intro μ ν
    rw [F_shift]
    simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply]
    rw [ip_comm (Φ.dF c Ψ.A μ ν) (Φ.F c μ ν), ip_comm (brk c (Ψ.A μ) (Ψ.A ν)) (Φ.F c μ ν),
      ip_comm (brk c (Ψ.A μ) (Ψ.A ν)) (Φ.dF c Ψ.A μ ν)]
    module
  have hY : ∀ μ, sbil opair (Cγ μ) (Φ.shift Ψ t).lam ((Φ.shift Ψ t).Dlam c μ) =
      sbil opair (Cγ μ) Φ.lam (Φ.Dlam c μ)
        + t • (sbil opair (Cγ μ) Ψ.lam (Φ.Dlam c μ) + sbil opair (Cγ μ) Φ.lam (Φ.dDlam c Ψ μ))
        + t ^ 2 • (sbil opair (Cγ μ) Ψ.lam (Φ.dDlam c Ψ μ)
          + sbil opair (Cγ μ) Φ.lam (fun β => act c (Ψ.A μ) (Ψ.lam β)))
        + t ^ 3 • sbil opair (Cγ μ) Ψ.lam (fun β => act c (Ψ.A μ) (Ψ.lam β))
        + t ^ 4 • (0 : R) := by
    intro μ
    have h1 : (Φ.shift Ψ t).lam = fun α => Φ.lam α + t • Ψ.lam α := rfl
    have h2 : (Φ.shift Ψ t).Dlam c μ = fun β => Φ.Dlam c μ β + t • Φ.dDlam c Ψ μ β
        + t ^ 2 • act c (Ψ.A μ) (Ψ.lam β) := funext fun β => Dlam_shift c Φ Ψ t μ β
    rw [h1, h2]
    simp only [sbil_add_left, sbil_add_right, sbil_zsmul_left, sbil_zsmul_right]
    module
  have hZ : ip (Φ.shift Ψ t).D (Φ.shift Ψ t).D =
      ip Φ.D Φ.D + t • ((2 : ℤ) • ip Φ.D Ψ.D) + t ^ 2 • ip Ψ.D Ψ.D + t ^ 3 • (0 : R)
        + t ^ 4 • (0 : R) := by
    have h : (Φ.shift Ψ t).D = Φ.D + t • Ψ.D := rfl
    rw [h]
    simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply]
    rw [ip_comm Ψ.D Φ.D]
    module
  have hL : ∀ Φ' : Fields R M I, Φ'.lagrangian c = lagShape
      (fun μ ν => ip (Φ'.F c μ ν) (Φ'.F c μ ν))
      (fun μ => sbil opair (Cγ μ) Φ'.lam (Φ'.Dlam c μ)) (ip Φ'.D Φ'.D) := fun _ => rfl
  have hdL : Φ.dLagrangian c Ψ = lagShape
      (fun μ ν => (2 : ℤ) • ip (Φ.F c μ ν) (Φ.dF c Ψ.A μ ν))
      (fun μ => sbil opair (Cγ μ) Ψ.lam (Φ.Dlam c μ)
        + sbil opair (Cγ μ) Φ.lam (Φ.dDlam c Ψ μ)) ((2 : ℤ) • ip Φ.D Ψ.D) := by
    simp only [dLagrangian, lagShape, smul_smul]; norm_num
  rw [hL, hL Φ, hdL]
  simp only [hF, hY, hZ]
  rw [lagShape_add, lagShape_add, lagShape_add, lagShape_add, lagShape_zsmul, lagShape_zsmul,
    lagShape_zsmul, lagShape_zsmul]

/-- **The first variation of the Lagrangian is `dLagrangian`.** -/
theorem isFirstVariation_lagrangian :
    IsFirstVariation (fun t => (Φ.shift Ψ t).lagrangian c) (Φ.dLagrangian c Ψ) := by
  have h0 : (Φ.shift Ψ 0).lagrangian c = Φ.lagrangian c := by
    have := lagrangian_shift c Φ Ψ 0
    simpa using this
  refine ⟨?r₂, ?r₃, ?r₄, fun t => ?h⟩
  case h =>
    show (Φ.shift Ψ t).lagrangian c = (Φ.shift Ψ 0).lagrangian c + _ + _ + _ + _
    rw [h0]
    exact lagrangian_shift c Φ Ψ t

/-- **Supersymmetry of the Lagrangian, in derived form.** The first variation of the
Lagrangian along the supersymmetry transformation is a total derivative. -/
theorem susy_invariance_derived (ε : Fin 4 → M) (hε : ∀ μ α, dM μ (ε α) = 0) :
    IsFirstVariation (fun t => (Φ.shift (Φ.susy c ε) t).lagrangian c)
      (∑ μ, dRM μ (Φ.susyCurrent c ε μ)) := by
  rw [← susy_invariance c Φ ε hε]
  exact isFirstVariation_lagrangian c Φ (Φ.susy c ε)

/-! ## The supersymmetry transformation -/

theorem spinorOf_add' (X X' : Fin 4 → Fin 4 → I → R) (Y Y' : I → R) (ε : Fin 4 → M)
    (α : Fin 4) : spinorOf (fun ρ σ => X ρ σ + X' ρ σ) (Y + Y') ε α =
      spinorOf X Y ε α + spinorOf X' Y' ε α := by
  have h : ∀ (X : Fin 4 → Fin 4 → I → R) (Y : I → R), spinorOf X Y ε α =
      ∑ ρ, ∑ σ, mvms (γ2 ρ σ) ε α (X ρ σ) + (2 : ℤ) • mvms γ5 ε α Y := fun _ _ => rfl
  simp only [h, map_add, sum_add_distrib, smul_add]; abel

theorem spinorOf_zsmul' (n : ℤ) (X : Fin 4 → Fin 4 → I → R) (Y : I → R) (ε : Fin 4 → M)
    (α : Fin 4) : spinorOf (fun ρ σ => n • X ρ σ) (n • Y) ε α = n • spinorOf X Y ε α := by
  have h : ∀ (X : Fin 4 → Fin 4 → I → R) (Y : I → R), spinorOf X Y ε α =
      ∑ ρ, ∑ σ, mvms (γ2 ρ σ) ε α (X ρ σ) + (2 : ℤ) • mvms γ5 ε α Y := fun _ _ => rfl
  simp only [h, map_zsmul, ← smul_sum]; module

variable (ε : Fin 4 → M)

/-- `δA` is linear in the fields, so its expansion stops at first order. -/
theorem susy_shift_A (t : ℤ) (μ : Fin 4) :
    ((Φ.shift Ψ t).susy c ε).A μ = (Φ.susy c ε).A μ + t • (Φ.dsusy c Ψ ε).A μ := by
  have e1 : ((Φ.shift Ψ t).susy c ε).A μ =
      -((2 * η μ) • sbil sm (Cγ μ) ε (Φ.shift Ψ t).lam) := rfl
  have e2 : (Φ.shift Ψ t).lam = fun α => Φ.lam α + t • Ψ.lam α := rfl
  have e3 : (Φ.susy c ε).A μ = -((2 * η μ) • sbil sm (Cγ μ) ε Φ.lam) := rfl
  have e4 : (Φ.dsusy c Ψ ε).A μ = -((2 * η μ) • sbil sm (Cγ μ) ε Ψ.lam) := rfl
  rw [e1, e2, e3, e4, sbil_add_right, sbil_zsmul_right]; module

/-- The exact expansion of `δλ` along `Φ + t Ψ`. -/
theorem susy_shift_lam (t : ℤ) (α : Fin 4) :
    ((Φ.shift Ψ t).susy c ε).lam α = (Φ.susy c ε).lam α + t • (Φ.dsusy c Ψ ε).lam α
      + t ^ 2 • spinorOf (fun ρ σ => brk c (Ψ.A ρ) (Ψ.A σ)) 0 ε α := by
  have e2 : (Φ.shift Ψ t).D = Φ.D + t • Ψ.D := rfl
  have e4 : (Φ.dsusy c Ψ ε).lam = spinorOf (Φ.dF c Ψ.A) Ψ.D ε := rfl
  rw [susy_lam_eq, susy_lam_eq, e2, e4]
  have hF : (Φ.shift Ψ t).F c = fun ρ σ => Φ.F c ρ σ + t • Φ.dF c Ψ.A ρ σ
      + t ^ 2 • brk c (Ψ.A ρ) (Ψ.A σ) := funext fun ρ => funext fun σ => F_shift c Φ Ψ t ρ σ
  have hD : Φ.D + t • Ψ.D = Φ.D + t • Ψ.D + t ^ 2 • (0 : I → R) := by simp
  rw [hF, hD, spinorOf_add', spinorOf_add', spinorOf_zsmul', spinorOf_zsmul']

/-- The exact expansion of `δD` along `Φ + t Ψ`. -/
theorem susy_shift_D (t : ℤ) :
    ((Φ.shift Ψ t).susy c ε).D = (Φ.susy c ε).D + t • (Φ.dsusy c Ψ ε).D
      + t ^ 2 • ((2 : ℤ) • ∑ μ, sbil sm (chargeC * γ5 * γ μ) ε
          (fun β => act c (Ψ.A μ) (Ψ.lam β))) := by
  have e1 : ((Φ.shift Ψ t).susy c ε).D =
      (2 : ℤ) • ∑ μ, sbil sm (chargeC * γ5 * γ μ) ε ((Φ.shift Ψ t).Dlam c μ) := rfl
  have e3 : (Φ.susy c ε).D = (2 : ℤ) • ∑ μ, sbil sm (chargeC * γ5 * γ μ) ε (Φ.Dlam c μ) := rfl
  have e4 : (Φ.dsusy c Ψ ε).D =
      (2 : ℤ) • ∑ μ, sbil sm (chargeC * γ5 * γ μ) ε (Φ.dDlam c Ψ μ) := rfl
  rw [e1, e3, e4]
  have h : ∀ μ, (Φ.shift Ψ t).Dlam c μ = fun β => Φ.Dlam c μ β + t • Φ.dDlam c Ψ μ β
      + t ^ 2 • act c (Ψ.A μ) (Ψ.lam β) := fun μ => funext fun β => Dlam_shift c Φ Ψ t μ β
  simp only [h, sbil_add_right, sbil_zsmul_right, sum_add_distrib, ← smul_sum]
  module

/-- **The first variation of the supersymmetry transformation is `dsusy`**, on the gauge
field. -/
theorem isFirstVariation_susy_A (μ : Fin 4) :
    IsFirstVariation (fun t => ((Φ.shift Ψ t).susy c ε).A μ) ((Φ.dsusy c Ψ ε).A μ) := by
  have h0 : ((Φ.shift Ψ 0).susy c ε).A μ = (Φ.susy c ε).A μ := by
    simpa using susy_shift_A c Φ Ψ ε 0 μ
  refine ⟨0, 0, 0, fun t => ?_⟩
  show ((Φ.shift Ψ t).susy c ε).A μ = ((Φ.shift Ψ 0).susy c ε).A μ + _ + _ + _ + _
  rw [h0, susy_shift_A]; simp

/-- **The first variation of the supersymmetry transformation is `dsusy`**, on the gaugino. -/
theorem isFirstVariation_susy_lam (α : Fin 4) :
    IsFirstVariation (fun t => ((Φ.shift Ψ t).susy c ε).lam α) ((Φ.dsusy c Ψ ε).lam α) := by
  have h0 : ((Φ.shift Ψ 0).susy c ε).lam α = (Φ.susy c ε).lam α := by
    simpa using susy_shift_lam c Φ Ψ ε 0 α
  refine ⟨?r₂, 0, 0, fun t => ?h⟩
  case h =>
    show ((Φ.shift Ψ t).susy c ε).lam α = ((Φ.shift Ψ 0).susy c ε).lam α + _ + _ + _ + _
    rw [h0, smul_zero, smul_zero, add_zero, add_zero]
    exact susy_shift_lam c Φ Ψ ε t α

/-- **The first variation of the supersymmetry transformation is `dsusy`**, on the auxiliary
field. -/
theorem isFirstVariation_susy_D :
    IsFirstVariation (fun t => ((Φ.shift Ψ t).susy c ε).D) ((Φ.dsusy c Ψ ε).D) := by
  have h0 : ((Φ.shift Ψ 0).susy c ε).D = (Φ.susy c ε).D := by
    simpa using susy_shift_D c Φ Ψ ε 0
  refine ⟨?r₂, 0, 0, fun t => ?h⟩
  case h =>
    show ((Φ.shift Ψ t).susy c ε).D = ((Φ.shift Ψ 0).susy c ε).D + _ + _ + _ + _
    rw [h0, smul_zero, smul_zero, add_zero, add_zero]
    exact susy_shift_D c Φ Ψ ε t

end Fields
end SYM
