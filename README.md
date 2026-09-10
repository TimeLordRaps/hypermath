# hypermath

A self-derivational mathematical framework built around the operation □, ordinal
structure, and reusable representations of derivations. Author: Tyler Roost /
The TimeLord.

The research objective is to derive the system's mathematical and semantic
structure from its stated ground, and investigate **Gödelian complete ordinal
arithmetic through fractal meta-representations**. Here a closed derivation may
become an atom for further derivation while retaining its formation path. The
completeness definition, preservation theorem, and arithmetic soundness bridge
are active research obligations.

## Current state

The repository contains four `.hm` specification layers and a Lean 4 translation.
The `.hm` files use `FORM` and `FRAME` as source-native closure labels. Those labels
record the proposed derivations; they do not by themselves establish successful
proof checking. The Lean translation contains explicit assumptions and unresolved
`sorry` proof obligations. A successful build can include such obligations.

The source does not yet establish an axiom-free executable kernel, a complete
arithmetic proof system, or a proof that its self-representation verifies every
arithmetic conclusion. The research goal remains in scope. See the
[proof audit](docs/research/PROOF_AUDIT.md) for concrete defects and dependencies,
and the [completeness target](docs/research/FRACTAL_COMPLETENESS.md) for the next
mathematical obligations.

The [finite-trace repair](docs/research/FINITE_TRACES.md) gives `D` actual finite
witnesses and proves self-read, composition, and recorded-step preservation.
It removes one admission and one unconstrained parameter. A checked countermodel
still separates an endpoint cycle from preservation throughout that cycle.

The [finite arithmetic bridge](docs/research/FINITE_ARITHMETIC.md) now proves
least finite closure and preservation of Form-valued length observations. It
also refutes the proposed universal ground-spanning claim under the existing
limit axiom. A separate interpretation satisfies all 38 declared logical
clauses while exposing their weaker treatment of limits and path endpoints.

## Ground and relations

`Form` names the source's forming structure, `ground` its distinguished base,
and `apply(x)` its □ operation. In the Lean translation these are explicit
uninterpreted assumptions. Lean's logic is the translation's ambient checker;
a correspondence with the source-native proposition and closure semantics is
not yet proved.

The specification distinguishes:

| Relation | Source notation | Intended meaning |
| --- | --- | --- |
| Similarity | `~~` | Nonempty overlap in continuation capacity |
| Congruence | `=~` | Coinciding continuation outcomes |
| Simulation | `==` | Mutual reproduction of derivation paths |

The declared filtration permits simulation to imply congruence and congruence
to imply similarity. It does not license either reverse implication. Source
`==` is not Lean's equality. The Lean notation for simulation is `≡`.

The four initial structural axiom clauses concern distinction from ground,
continuation from ground, double-application return, and ground's own
continuation. Additional relation, semantic, path, and ordinal assumptions
occur in later sections; the whole specification is not merely four axioms.

## Reading and source map

| Layer | Specification | Intended role |
| --- | --- | --- |
| L0: Ground | [L0_ground.hm](L0_ground.hm) | Primitives, structural relations, executive predicates |
| L1: Relations | [L1_relations.hm](L1_relations.hm) | Filtration, derivation matrix, semantic closes |
| L2: Operations | [L2_operations.hm](L2_operations.hm) | Composition and paths |
| L3: Ordinatics | [L3_ordinatics.hm](L3_ordinatics.hm) | Ordinal extension and proposed self-derivation |

The [Seed-ai source map](docs/research/SOURCE_MAP.md) connects the broader
hypergrammar and earlier hypermath specifications to these layers. Selected
source snapshots retain their original wording for comparison; they do not
replace the current specifications or become checked proofs through import.
The [term dictionary](docs/terms/Form.md) explains the project's vocabulary.

## Install and check the foundation

The Python distribution is `hypermath-foundations`; its import name is
`hypermath_foundations`. The unrelated package named `hypermath` on the Python
Package Index is not this project. From a checkout, with Python 3.10 or newer:

```console
python -m pip install '.[verification]'
python -u scripts/check_foundation.py --require-self-derivation
```

This runs fresh Lean checks and a Verifier Standard (VSTD) evidence session,
then applies the self-derivation gate. Unresolved claims remain `UNKNOWN`, and
the gate exits with status 2. Evidence is retained under `build/verification`.
The current package is prepared for source installation; an index release is
a separate publication step.

## Lean translation

The pinned toolchain is recorded in [lean4/lean-toolchain](lean4/lean-toolchain).
After installing that toolchain and the Python package, run from `lean4`:

```console
python -u audit.py
```

The bounded audit builds with visible output and records declaration counts and
axiom dependencies for selected claims. Proof holes remain explicit. It is an
audit of the current translation, not a theorem that the intended source system
is consistent, complete, or internally self-verifying. See
[lean4/README.md](lean4/README.md) for the proof gate and reproduction details.

## Relationship to Ordinatics

[Ordinatics](https://github.com/TimeLordRaps/ordinatics) is the Python companion
for exact ordinal operations, a rational-function value layer, and bounded
formula evaluation. Its present evaluator does not implement this repository's
fractal closure or prove the full completeness claim. The existing paper's
external truth hierarchy is background for the stronger research objective.
Ordinatics depends on a specific Hypermath commit and checks that its installed
foundation package matches that source before running verification. Its
publication gate also requires the source-to-arithmetic bridge and completeness
claim to be established. The current bridge remains unproved. See
[continuous integration and grounding](docs/verification.md) for the dependency
contract, evidence boundaries, and checks.

## License

Apache 2.0. See [LICENSE](LICENSE). Original source notices and provenance are
retained where applicable.
