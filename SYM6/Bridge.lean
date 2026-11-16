import SYM6.Forms
import SYM.Calculus

/-!
# The four-dimensional calculus is a special case

The even part of a `SYM.SuperCalculus` is a `DiffRing` over `Fin 4`, so the forms of
`SYM6/Forms.lean` and `d² = 0` apply to the four-dimensional theory unchanged.
-/

set_option autoImplicit false
namespace SYM6

/-- The even fields of a four-dimensional Grassmann calculus form a `DiffRing`. -/
@[reducible] def diffRingOfSuperCalculus (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [SYM.SuperCalculus R M] : DiffRing (Fin 4) R where
  d := SYM.SuperCalculus.dR (M := M)
  d_mul := SYM.SuperCalculus.dR_mul
  d_comm := SYM.SuperCalculus.dR_comm
  two_torsion := SYM.SuperCalculus.two_torsion (M := M)

end SYM6
