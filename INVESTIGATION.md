# Investigation log: a classical Lagrangian for the 6D (2,0) tensor multiplet

Lean is the referee. An entry is **proved** or **refuted** only if the deciding theorem is in
this repository and passes the axiom audit in `Verify.lean`. Everything else is **open**.

Status after tranche 4. Most of the programme is still open; see the last section.

## Conventions

Six dimensions, signature `(+,+,+,+,+,−)`, time is index 5. A form is a function on
`Finset (Fin 6)`; its value on `S` is the component with increasing indices in `S`.
Hodge star `(*ω)_S = κ(S) ω_{Sᶜ}`, `κ(S) = ε(S,Sᶜ) η(Sᶜ)`. Checked numerically before
proving: `** = +1` on 3-forms.

## What had to change in the framework

| 4D framework | 6D generalization |
| --- | --- |
| `SYM.SuperCalculus R M`, index type fixed to `Fin 4`, even and odd parts | `SYM6.DiffRing ι R`: commuting derivations over any index type, even part only. `SYM6.diffRingOfSuperCalculus` shows the 4D even part is the case `ι = Fin 4`. |
| Tensors with explicit index slots (`Fin 4 → Fin 4 → …`) and hand-written antisymmetry | Forms as functions on index sets; antisymmetry is built in, and one definition of `d` covers every degree. |
| Real `4 × 4` Majorana matrices | Real `16 × 16` matrices: `Cl(5,1) ≅ M₄(ℍ)` has no real `8 × 8` representation. The quaternionic structure replaces the complex `8 × 8` picture. |
| `SYM.SuperCalculus` with odd fields, four derivations | `SYM6.SuperCalc ι R M`: the same axioms with derivations indexed by any type. `superCalcOfSuperCalculus` shows the 4D calculus is the case `ι = Fin 4`; `SuperCalc.toDiffRing` gives the even part. |
| `SYM.sbil`, `SYM.mv` on `Fin 4` spinor indices | `SYM6.sbilG`, `SYM6.mvG` on any finite spinor index type, with the same lemmas. |

| `SYM/Color.lean`: adjoint-valued fields over four derivations | `SYM6/Color.lean`: the same file with derivations over any index type. Statements and proofs unchanged, including the Bianchi identity. |
| `SYM/Theory.lean`: 4D fields, Lagrangian, supersymmetry, with concrete Majorana matrices | `SYM6/Theory.lean`: the gamma matrices enter only through `GammaData` (five identities). One theorem, `GFields.susy_invariance`, for every dimension carrying such data. No auxiliary field. |

To make this work the dimension became an inferred parameter of `SuperCalc` (it is determined
by the module of odd fields), and the final index bookkeeping of the 4D proof, which expanded
sums over `Fin 4`, was redone symbolically.

Not ported: closure of the algebra, the derived first variation, and the equations of motion
and supercurrent (`SYM/Closure.lean`, `SYM/Variation.lean`, `SYM/Noether.lean`) are still
four-dimensional.

## Step 1. Foundations

| Item | Status | Deciding theorem |
| --- | --- | --- |
| `d² = 0`, every degree and dimension | proved | `SYM6.extD_extD` |
| Hodge star on 3-forms, `** = 1` | proved | `SYM6.star_star` |
| `div = * d *` on 3-forms | proved | `SYM6.star_extD_star` |
| Gamma matrices, Clifford relation, signature (5,1) | proved | `SYM6.clifford6` |
| Chirality `Γ7² = 1`, anticommutes with `Γ^a` | proved | `SYM6.Γ7_sq`, `Γ7_anticomm` |
| Quaternionic structure commuting with the Clifford algebra (symplectic Majorana) | proved | `SYM6.qI_sq`, `qI_mul_qJ`, `qI_comm`, `qJ_comm` |
| Bilinear symmetry, ranks 0 and 1, with and without a quaternion unit | proved | `C6_transpose`, `C6Γ_transpose`, `C6qI_transpose`, `C6qIΓ_transpose`, … |
| Bilinear symmetry, ranks 2–6 | open (numerics only) | table below |
| Chiral vector Fierz identity `(CΓ_a P)_{α(β}(CΓ^a P)_{γδ)} = 0` | proved | `SYM6.fierz6` (sixteen kernel evaluations; a single one runs out of memory) |
| Sign rules for exchanging odd spinors in `ψ̄χ`, `ψ̄Γ^aχ`, `ψ̄qχ`, `ψ̄qΓ^aχ` | proved | `bar6_one_symm`, `bar6_Γ_antisymm`, `bar6_qI_antisymm`, `bar6_qIΓ_symm` |
| Leibniz rule for 6D bilinears | proved | `dR_bar6` |
| (2,0) spinors as a pair of 16-component spinors; ten `Sp(4)` generators; invariant pairing; chirality preserved | proved | `sp4Gen`, `pairing20_sp4`, `rAct_chiral` |
| The ten generators close into the Lie algebra `sp(4)` | open | commutators not computed |
| Complete list of Fierz identities | open | not attempted |
| Bianchi identity for the non-abelian field strength, any dimension | proved | `SYM6.bianchi` |
| Super Yang–Mills is supersymmetric given `GammaData` | proved | `SYM6.GFields.susy_invariance` |
| `GammaData` in four dimensions | proved | `SYM6.gamma4`, `superYangMills4` |
| `GammaData` in six dimensions, chiral spinor | proved | `SYM6.gamma6`, `superYangMills6`; cyclicity of `Γ^{ρσμ}` in `SYM6/Chiral3.lean` (about twelve minutes of kernel evaluation) |

Numerical symmetry table of `C q Γ^{(p)}` (S symmetric, A antisymmetric), `p = 0…6`:

| `q` | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `1` | A | S | S | A | A | S | S |
| `I, J, K` | S | A | A | S | S | A | A |

## Step 2. Abelian candidates

| # | Candidate | Status | Deciding theorem |
| --- | --- | --- | --- |
| C1 | `L = H ∧ *H`, `H = dB` | **refuted** | `pairing3_selfDual`: the density vanishes identically on self-dual `H`. `pairing3_extD`: its field equation is `div H = 0`. `div_eq_zero_of_antiSelfDual`: every closed anti-self-dual `H` solves it too, so the field equation cannot impose self-duality. |
| C2 | Non-manifestly covariant: `L = −∑_{S spatial} H_S (H − *H)_S` | **partly proved** | `dLagNC_eq`: first-variation formula. `fieldEquation_iff`: the field equation is `d(D_el) = 0`, with `D_el` the electric part of `H − *H`. `fieldEquation_of_selfDual`: self-dual configurations solve it. `selfDual_of_exact`: if `D_el` is exact with a time-component potential, the field is a shift of a self-dual one. |
| C2a | C2: field equations ⇒ self-duality | open, with exact hypothesis | Needs "closed ⇒ exact" for `D_el` (a Poincaré lemma) and the shift symmetry of `B_{i5}`. Not provable in an abstract `DiffRing`, where it is false in general. |
| C2b | C2: Lorentz invariance of the action | open | not attempted |
| C2c | C2: supersymmetry up to a total derivative | open | needs 6D fermions |
| C3 | Auxiliary scalar making covariance manifest | open | not attempted |
| C4 | Doubled field / extra free field | open | not attempted |

Hypotheses of the C1 refutation: the Lagrangian is the quadratic density `⟨H, H⟩` of a
single 2-form potential, with no other fields; `R` has no 2-torsion.

## Step 3. Closure and supercurrent

Open: there is no supersymmetric survivor yet.

## Step 4. Non-abelian

A *deformation* here means: fields valued in an associative algebra with the commutator
bracket, a modified field strength `H`, and a modified tensor gauge transformation `δ_Λ B`,
both reducing to `dB` and `dΛ` when the bracket vanishes. Only the first one has been
examined; deformations have not been enumerated order by order.

| # | Deformation | Status | Deciding theorem |
| --- | --- | --- | --- |
| D1 | Minimal coupling: connection `C`, `H = D_C B`, `δ_Λ B = D_C Λ`, `δ_Λ C = 0` | **obstructed** | `covD_covD`: `2 D² = F ∧ ·`. `minimal_coupling_variation`: `2 δ_Λ H = F ∧ Λ`. The tensor gauge symmetry is broken by the curvature of `C`. |
| D1-flat | D1 with a flat connection | **consistent** | `covD_covD_of_flat`: `D² = 0`, so `δ_Λ H = 0`. A flat connection is locally pure gauge, so this is the abelian theory in disguise. |
| D2 | Accompanying 1-form transforming under `Λ` (`δ_Λ C ≠ 0`), with a constraint relating `F` and `B` | open | not attempted |
| D3 | Extra fields, higher algebraic structures, non-local terms | open | not attempted |
| — | Order-by-order enumeration of deformations | open | not attempted |

Hypotheses of the D1 obstruction: values in an associative algebra with the commutator as
bracket; the same connection in `H` and in `δ_Λ B`; `δ_Λ C = 0`; no further fields; no
2-torsion. The obstruction says nothing about deformations outside this ansatz.

## Step 5. Reduction to five dimensions

Open: 5D maximal SYM has not been derived from 10D, and no reduction has been checked.

## Plain summary

- **Constructed:** a dimension-independent calculus of forms and of odd fields; the 6D
  Hodge star; real `16 × 16` gamma matrices with their quaternionic structure; the 6D
  spinor bilinear calculus with the `Sp(4)` R-symmetry and the chiral Fierz identity; one candidate action (C2)
  whose field equation is the curl of the self-duality condition.
- **Proved impossible:** `H ∧ *H` as an action for a self-dual 3-form, and minimal coupling
  as a non-abelian deformation unless the connection is flat, each under the hypotheses
  stated above.
- **Open:** the tensor multiplet itself (its fields, supersymmetry transformations,
  closure, supercurrent), for which the fermion calculus is now in place, Lorentz invariance of C2, the covariant and doubled-field
  candidates, every non-abelian deformation beyond minimal coupling, and the reduction to
  five dimensions.
