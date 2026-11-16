# Classical N = 1 super Yang–Mills theory in Lean 4

A formalization of classical four-dimensional `N = 1` super Yang–Mills theory, built on the
[OpenAI Yang–Mills formalization](https://github.com/yang-mills-group/OpenAI-YM-20261028).

The two central theorems are proved, with no `sorry` and no new axioms:

- **Supersymmetry of the action.** The supersymmetry variation of the Lagrangian is a total
  derivative (`SYM.Fields.susy_invariance`).
- **Off-shell closure of the algebra.** On each of `A_μ`, `λ`, `D`, the commutator of two
  supersymmetry transformations is a translation plus a gauge transformation, without using
  the equations of motion (`SYM.Fields.closure`).

Built on them:

- **Equations of motion.** `first_variation` writes the first variation of the Lagrangian as
  the Euler–Lagrange expressions contracted with the variation, plus a divergence. The
  expressions are `4 D_μ F^{μν} − 2 λ̄ γ^ν [·, λ]`, `−4 C γ^μ D_μ λ` and `4 D`.
- **Supercurrent.** `noether_identity` gives the divergence of the supercurrent off shell,
  `supercurrent_conserved` its vanishing on shell, and `supercurrent_eq` its closed form
  `J^μ = −4 F_ρσ · ε̄ γ^{ρσ} γ^μ λ`.

Both main theorems are also stated for smooth Grassmann-valued fields on spacetime with an arbitrary gauge
group of the upstream project (`SYM.superYangMills_susy`, `SYM.superYangMills_closure`).

The original project is not copied or modified. It is a Lake dependency pinned to commit
`3456e5e75cf8d4cd558955a5c7638fba2d68f464`.

## The theory

Signature `(+,+,+,−)` with time last, real Majorana spinors, `λ̄ = λᵀ C`. Fields: a gauge
potential `A_μ`, a Grassmann-odd Majorana gaugino `λ`, an auxiliary field `D`, all valued in
the Lie algebra.

| | In this repository | Textbook form |
| --- | --- | --- |
| Lagrangian | `−F_μν F^μν − 2 λ̄ γ^μ D_μ λ + 2 D²` | `4 · (−¼ F² − ½ λ̄ γ^μ D_μ λ + ½ D²)` |
| `δA_μ` | `−2 ε̄ γ_μ λ` | `−½ ε̄' γ_μ λ` |
| `δλ` | `(γ^{ρσ} F_ρσ + 2 γ5 D) ε` | `(¼ γ^{ρσ} F_ρσ + ½ γ5 D) ε'` |
| `δD` | `2 ε̄ γ5 γ^μ D_μ λ` | `½ ε̄' γ5 γ^μ D_μ λ` |
| `[δ₁, δ₂]` | `ξ^σ ∂_σ + δ_gauge(ξ^σ A_σ)`, `ξ^σ = 8 ε̄₂ γ^σ ε₁` | `ξ^σ = ½ ε̄'₂ γ^σ ε'₁` |

The two columns agree for `ε' = 4 ε`. The rescaling keeps every coefficient an integer, so
no division is needed in the proofs. `γ5 = γ^0 γ^1 γ^2 γ^3` is real with `γ5² = −1`; it is
`i γ_*` in complex conventions.

## The framework

| Module | Content |
| --- | --- |
| [`SYM/Gamma.lean`](SYM/Gamma.lean) | Real Majorana gamma matrices as integer matrices. Clifford relation, symmetry of `C Γ`, and three Fierz identities, all by kernel evaluation. |
| [`SYM/Calculus.lean`](SYM/Calculus.lean) | `SuperCalculus R M`: a supercommutative differential algebra with even part `R`, odd part `M`, and four commuting derivations. |
| [`SYM/Color.lean`](SYM/Color.lean) | Adjoint-valued even and odd fields, structure constants, Jacobi identity, invariant inner product, covariant derivatives, field strength, **Bianchi identity**. |
| [`SYM/Spinor.lean`](SYM/Spinor.lean) | Spinor bilinears `ū M v` and their sign rules. |
| [`SYM/Theory.lean`](SYM/Theory.lean) | Fields, Lagrangian, first variation, supersymmetry transformation, conserved-current candidate, `susy_invariance`. |
| [`SYM/Closure.lean`](SYM/Closure.lean) | `closure_A`, `closure_lam`, `closure_D`, and `closure`. |
| [`SYM/Variation.lean`](SYM/Variation.lean) | The first variation as the linear coefficient of an exact expansion along `Φ + tΨ`; its uniqueness; proof that `dLagrangian` and `dsusy` are the first variations. |
| [`SYM/Noether.lean`](SYM/Noether.lean) | Equations of motion from the first-variation formula; Noether's identity; conservation and closed form of the supercurrent. |
| [`SYM/GaugeGroup.lean`](SYM/GaugeGroup.lean) | Structure constants of an upstream gauge group `G : YM.Gauge`, from `G.ad`. |
| [`SYM/Model.lean`](SYM/Model.lean) | Smooth fields on `YM.E4` with values in a Grassmann algebra form a `SuperCalculus`; the theory for gauge group `G`. |
| [`SYM/Exterior.lean`](SYM/Exterior.lean) | The exterior algebra `Λ(ℝ²)` as a Grassmann algebra, with `θ₁θ₂ ≠ 0`. |
| [`SYM/Adjoin.lean`](SYM/Adjoin.lean) | Adjoining one odd generator to any Grassmann algebra gives a Grassmann algebra (`adjoin`). Applied three times: the exterior algebra on four generators, with `(θ₁θ₂)(θ₃θ₄) ≠ 0`. |
| [`SYM/VectorMultiplet.lean`](SYM/VectorMultiplet.lean) | The earlier, conservative step: real-valued fields and infinitesimal local gauge invariance. |

Parity is carried by types. Even fields live in a commutative ring `R`, odd fields in an
`R`-module `M`, and the product of two odd fields is a map `M → M → R` that is alternating
and associative. Every sign rule is then a theorem instead of a side condition.

The first variation is derived, not postulated. `IsFirstVariation f v` says `v` is the
coefficient of `t` in an exact expansion `f t = f 0 + t v + t² r₂ + t³ r₃ + t⁴ r₄` over
integer `t`, and `IsFirstVariation.unique` shows this coefficient is unique when there is no
2- or 3-torsion. `lagrangian_shift` expands the Lagrangian along `Φ + tΨ` to all four orders,
which gives `isFirstVariation_lagrangian`; `susy_shift_A`, `susy_shift_lam`, `susy_shift_D`
do the same for the supersymmetry transformation. `susy_invariance_derived` restates the
first main theorem in this form.

## What is reused from the original project

| Upstream | Used for |
| --- | --- |
| `YM.Gauge`, `G.lie`, `G.Color`, `G.ad`, `colorMat_ad`, `colorMat_injective` | the gauge group and its Lie algebra in trace-orthonormal coordinates |
| `ad_jacobi`, `ad_skew` (`YM.Gauge.Casimir`) | Jacobi identity and total antisymmetry of the structure constants |
| `YM.E4`, `YM.Axis`, `YM.basis`, `YM.timeAxis` convention | spacetime; time is the last coordinate |
| `YM.Maxwell.grad`, `grad_smooth`, `grad_comm` | coordinate derivatives and their symmetry |

## Verification

Requires Git and Lean 4.32.0 (or elan).

```sh
lake exe cache get
lake build
```

`lake build` compiles the twelve reused upstream modules from source, then this project.
[`Verify.lean`](Verify.lean) makes the build fail if a main theorem depends on anything
beyond `propext`, `Classical.choice` and `Quot.sound`.

The original project's own full verification (about 9,500 modules and `VerifyJoint.lean`) is
not re-run here. Its sources are untouched and match its `SOURCES.sha256`.

## Limits

- **Variations are taken along straight lines with integer parameter.** `Φ + tΨ` for
  `t : ℤ`, which fits the algebraic setting; no derivative in a real parameter is used.
  Uniqueness of the first variation of the gaugino component needs the odd fields to have no
  2- or 3-torsion, which the calculus axioms assume only for even fields.
- **Minkowski signature is on the indices only.** The underlying space is the upstream
  `E4 = ℝ⁴`; nothing here uses its Euclidean norm beyond differentiation.
- **Grassmann algebras are built up to four generators.** `SYM.adjoin` adds one generator to
  any Grassmann algebra whose odd product is norm-contractive, and
  `SYM.FourGenerators.quartic_ne_zero` shows that quartic fermion terms are non-zero on four
  generators. Each further generator is one more application of `adjoin`; the tower is not
  packaged as a single family indexed by the number of generators.
- **Equations of motion are the Euler–Lagrange expressions.** They are read off from the
  first-variation formula. The converse, that a stationary action forces them to vanish,
  needs the fundamental lemma of the calculus of variations and is not proved.
- **Not included:** finite gauge transformations, gauge covariance of the supersymmetry
  transformations in the new framework, superspace, matter multiplets.

## License

Apache-2.0, the same as the original project.
