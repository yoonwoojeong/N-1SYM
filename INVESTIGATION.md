# Investigation log: a classical Lagrangian for the 6D (2,0) tensor multiplet

Lean is the referee. An entry is **proved** or **refuted** only if the deciding theorem is in
this repository and passes the axiom audit in `Verify.lean`. Everything else is **open**.

Status after tranche 1. Most of the programme is still open; see the last section.

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

Not yet generalized: the odd part (fermions) over an arbitrary index type. The 6D spinor
bilinear calculus (`sbil`) is not ported.

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
| Chiral vector Fierz identity `(CΓ_a P)_{α(β}(CΓ^a P)_{γδ)} = 0` | open (numerics only) | holds numerically; the Lean proof is a 65,536-case evaluation not yet run |
| Explicit `Sp(4)` index and the (2,0) reality condition | open | only the `Sp(1)` quaternionic structure is constructed |
| Complete list of Fierz identities | open | not attempted |

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

## Steps 3–5

| Item | Status |
| --- | --- |
| Closure of the algebra and supercurrent for a survivor | open: no supersymmetric survivor yet |
| Definition and enumeration of non-abelian deformations | open: not attempted |
| Obstruction theorem with exact hypotheses, and its relaxations | open: not attempted |
| 5D maximal SYM from 10D, circle reduction check | open: not attempted |

## Plain summary

- **Constructed:** a dimension-independent calculus of forms; the 6D Hodge star; real
  `16 × 16` gamma matrices with their quaternionic structure; one candidate action (C2)
  whose field equation is the curl of the self-duality condition.
- **Proved impossible:** `H ∧ *H` as an action for a self-dual 3-form, under the hypotheses
  stated above.
- **Open:** everything involving fermions in six dimensions (the multiplet, supersymmetry,
  closure, supercurrent), Lorentz invariance of C2, the covariant and doubled-field
  candidates, the whole non-abelian question, and the reduction to five dimensions.
