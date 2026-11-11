# N = 1 SYM: a first step on top of the OpenAI Yang–Mills formalization

A small, verified Lean 4 extension of
[yang-mills-group/OpenAI-YM-20261028](https://github.com/yang-mills-group/OpenAI-YM-20261028)
toward classical four-dimensional `N = 1` super Yang–Mills theory.

The original project is not copied or modified. It is a Lake dependency pinned to commit
`3456e5e75cf8d4cd558955a5c7638fba2d68f464`; twelve of its modules are imported as they are.

## What is here

[`SYM/VectorMultiplet.lean`](SYM/VectorMultiplet.lean) defines the off-shell vector multiplet
and proves that it is locally gauge covariant.

| New definition | Meaning |
| --- | --- |
| `VectorMultiplet G` | gauge potential `A_μ`, four-component gaugino `λ_α`, auxiliary field `D`, all valued in `G.Color` |
| `covD` | `D_μ φ = ∂_μ φ + [A_μ, φ]` |
| `fieldStrength` | `F_μν = ∂_μ A_ν − ∂_ν A_μ + [A_μ, A_ν]` |
| `shiftGauge`, `shiftAdjoint`, `VectorMultiplet.shift` | the fields moved by `t` times `δA_μ = −D_μ ω`, `δλ = [ω, λ]`, `δD = [ω, D]` |
| `lagrangian Γ` | `¼ ⟪F_μν, F_μν⟫ + ½ Γ^μ_αβ ⟪λ_α, D_μ λ_β⟫ + ½ ⟪D, D⟫` |

| Theorem | Statement |
| --- | --- |
| `fieldStrength_shift` | `F(A + t δA) = F + t [ω, F] + t² [D_μ ω, D_ν ω]`, for `A` differentiable and `ω` of class `C²` at the point |
| `covD_shift` | `D^{A + t δA}(φ + t δφ) = Dφ + t [ω, Dφ] − t² [D_μ ω, [ω, φ]]` |
| `hasDerivAt_fieldStrength_shift`, `hasDerivAt_covD_shift` | the first-order forms `δF = [ω, F]`, `δ(Dφ) = [ω, Dφ]` |
| `lagrangian_gauge_invariant` | `d/dt` of the Lagrangian density along `Φ + t δ_ω Φ` vanishes at `t = 0` |
| `ad_antisymm`, `grad_ad`, `grad_covD`, `fieldStrength_antisymm` | supporting lemmas |

No `sorry`, no new axioms. [`Verify.lean`](Verify.lean) makes the build fail if any of the
five main theorems depends on anything beyond `propext`, `Classical.choice` and `Quot.sound`.

## What is reused from the original project

| Module | Used for |
| --- | --- |
| `YM.Gauge.MatrixGroup`, `YM.Gauge.Lie` | `Gauge`, its Lie algebra `G.lie`, closure under the bracket |
| `YM.Gauge.Colors` | `G.Color`, `G.colorMat`, the bracket `G.ad`, `colorMat_ad`, `colorMat_injective` |
| `YM.Gauge.Casimir` | `ad_jacobi` (Jacobi identity), `ad_skew` (invariance of the colour inner product) |
| `YM.Space.*` | `E4`, `Axis`, `basis` |
| `YM.Maxwell.Exterior`, `YM.Analysis.SmoothJets` | `grad`, `grad_smooth`, `grad_comm` (symmetry of second derivatives) |

## Scope, stated plainly

These are gauge-covariance theorems, not supersymmetry theorems. The gaugino kinetic term
carries an arbitrary coefficient tensor `Γ`, and the invariance theorem holds for every `Γ`,
so it uses neither a Clifford relation nor Grassmann parity. No supersymmetry transformation
is defined.

The original project has no spinors, gamma matrices, Grassmann-odd fields or continuum
non-abelian curvature; its continuum classical layer is abelian (Maxwell). Those are what a
supersymmetry identity needs, and they are not built here.

## Build

Requires Git and Lean 4.32.0 (or elan).

```sh
lake exe cache get
lake build
```

`lake build` compiles the twelve reused upstream modules from source, then `SYM` and `Verify`.

## What remains for a complete classical N = 1 SYM formalization

1. **Spinor algebra.** A real (Majorana) representation of the four-dimensional Clifford
   algebra, the charge-conjugation matrix, `γ⁵`, `γ^{μν}`, and the symmetry properties of
   the bilinears. This fixes `Γ`.
2. **Signature.** `E4` is Euclidean, where Majorana spinors do not exist. Either a Minkowski
   version of `grad`/`covD`/`fieldStrength`, or the Euclidean theory with doubled spinors.
3. **Grassmann-odd fields.** The gaugino and the supersymmetry parameter must anticommute;
   with commuting components the gaugino kinetic term is a total derivative and the
   supersymmetry commutator vanishes identically.
4. **Supersymmetry transformations.** `δA_μ = ε̄ γ_μ λ`, `δλ = (½ γ^{μν} F_μν + i γ⁵ D) ε`,
   `δD = i ε̄ γ⁵ γ^μ D_μ λ`, and their gauge covariance (which follows from the theorems here).
5. **Fierz identity.** The cubic gaugino term in `δL` cancels only by the four-dimensional
   Fierz identity together with total antisymmetry of the structure constants.
6. **Invariance of the action.** `δL` is a total derivative, which needs the Bianchi identity
   for `fieldStrength` and a notion of total derivative or integration by parts.
7. **Closure of the algebra.** `[δ₁, δ₂]` is a translation plus a field-dependent gauge
   transformation, off shell.
8. **Finite gauge transformations.** Covariance under `A ↦ u A u⁻¹ − (du) u⁻¹` for a
   group-valued `u`, using the existing `G.adjoint`.

## License

Apache-2.0, the same as the original project.
