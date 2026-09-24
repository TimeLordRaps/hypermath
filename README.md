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

Finite numeral addition and multiplication respect equality of ground-orbit
representations without assuming that distinct counts produce distinct Forms.
Every finite-orbit Form has a natural-number representative; if the numeral
encoding is injective, the checked encode/decode laws give a two-sided
correspondence with the natural numbers and equal numeral Forms induce equal
iterations from every starting Form. The conditional exact host action uses
classical choice; agreement with native `ordinalApply` remains separate. A
six-form countermodel satisfies all 38 clauses, with congruence
an equivalence relation, but prevents both exact and congruence-valued actions
of that kind. It also shows that the proposed zero, successor, and opaque
path-length laws do not follow from those clauses. Their statements remain
named propositions instead of admitted theorems. The translation now has
67 declared assumptions and 11 admissions; the audit binds 45 proved milestone
declarations. Removing those three admissions records non-entailment, not
three completed proofs. The model additionally satisfies the exact current
self-derivation target while those arithmetic bridges fail. This proves that
the current target is insufficient for an arithmetic interpretation; it does
not refute a stronger target with typed reification and transfinite semantics.
The model does not encode the stronger, unformalized native intent that all
Forms arise from the ground.

A second full-clause model refutes the two-step simulation cycle and nontrivial
simulation-pair claim. Their admitted proofs have been withdrawn, and
`selfDerivation` now names the unchanged, unproved proposition. Conditional
assembly shows that its first three conjuncts reduce the remaining obligation
exactly to the cycle. The [cycle boundary](docs/research/CYCLE_BOUNDARY.md)
records this proof-interface change and its counterexamples. Audit integrity
can pass for a faithfully reported definition; the strict proof gate cannot.

The [finite ground-syntax checker](docs/research/GROUND_SYNTAX.md) represents
instances of the four primitive ground rules as records built from `ground`
and `apply`. It proves decoding, exact conclusion checking, soundness under the
existing rules, and repeated argument reinstantiation. Semantic interpretation
can identify distinct records, so this syntax is not silently identified with
native `Form` values. The required audit checks 23 additional reports.

The [composed ground calculus](docs/research/COMPOSED_GROUND_DERIVATIONS.md)
adds typed rule trees, the three existing predicate closes, conjunction, and
checked projections. Every typed derivation has an accepted record, and typed
reconstruction preserves the entire accepted rule tree. Soundness uses the
existing source premises; the 26 additional reports introduce no admission or
native axiom.

The [record encoding](docs/research/RECORD_ENCODING.md) maps composed records and
formulas to single free ground terms, with proved recovery, preservation of all
record observations, and agreement with the composed checker. Its packed
numerical interface avoids expanding the enormous unary term. The 45 additional
dependency reports expose all host assumptions, including classical choice in
the size-bound proof. The existing model of all 38 clauses now supplies one
faithful semantic interpretation and exact checker correspondence. This is a
compatibility witness; source adequacy and internally derived acceptance
remain necessary before this realizes the ranked meta-surface.

The [native acceptance boundary](docs/research/NATIVE_ACCEPTANCE.md) checks why
executive closure cannot substitute for that missing acceptance construction.
A malformed projection has the same true conclusion as a valid primitive
record, and both encoded forms satisfy the model's executive and ground-anchoring
conditions. The checker distinguishes their formation trees. An internal
acceptance proof must bind those trees and their premises to the claimed result.

The [record execution machine](docs/research/RECORD_MACHINE.md) now performs
those finite rule checks instruction by instruction. It agrees with the
recursive checker on every record and verifies submitted execution traces
against the exact record and conclusion. Failed premises remain failed, even
through later projections or introductions. Its 40 mandatory dependency reports
contain no admissions or native assumptions. The machine still uses host
syntax and operations; their native realization and ranked acceptance remain
open.

The [substitution executor](docs/research/RULE_SUBSTITUTION.md) makes each
checking call's rule, indexed substitution, and exact premise stack explicit.
Every call has a recoverable free-ground representation; executing the packed
calls agrees with the original checker on every finite proof record. Its 47
additional mandatory reports preserve the distinction between represented
inputs and source-native execution or ranked acceptance.

The [finite layer-preservation construction](docs/research/LAYER_PRESERVATION.md)
encodes complete lower surfaces as next-layer atoms. Composition and any finite
number of lifts preserve exact recovery and checking outcomes, including
rejection; accepted claim lists retain order and repetitions. Upper-layer
composition forms a monoid modulo its declared checked-expansion relation.
The original 45 preservation reports contain no admissions or native assumptions.
This is a host construction toward the proposed fractal mechanism; native
generation, internal acceptance, and ordinal interpretation remain open.

The [contextual composition bridge](docs/research/CONTEXTUAL_COMPOSITION.md)
constructs joint premise availability by running the second derivation in the
context retained by the first. It connects the existing conjunction rule to
exact history recovery and checking through every finite number of lifts.
Its 17 additional reports check this connection and reject unsupported premise
claims and incompatible history splices. Native generation remains open.

The [operational correspondence criterion](docs/research/OPERATIONAL_CORRESPONDENCE.md)
states sufficient local laws for native execution and layer passage to preserve
complete checking frames. It proves their consequences for arbitrary finite
runs and exhibits failures of checking only newly encoded inputs. Its 18
additional required reports are conditional results and counterexamples; a
native instance of the interface remains to be constructed.

The [terminal-retention test](docs/research/TERMINAL_RETENTION.md) rules out one
candidate in the existing two-successor-chain model: primitive forming alone
cannot implement the total retained-frame protocol for any encoder and decoder.
Three accepted records suffice for the obstruction. A stopped or guarded
protocol, explicit layer information, and other carriers remain open choices
requiring their own native derivations.

The [retained-execution construction](docs/research/RETAINED_EXECUTION.md)
stores submitted execution frames, including their actual histories. Ordered
composition and every finite number of lifts preserve those frames exactly
and preserve rejection of erased histories, wrong endpoints, and incomplete
execution. The new Lean representation has a separate format from the existing
Python graph protocol. Native formation and ordinal interpretation remain open.

The [witnessed path layers](docs/research/PATH_LAYERS.md) specialize finite
composition and lifting to existing native derivation entries, preserving
their endpoints, edge witnesses, and exact expanded paths. A supplied stronger
cycle certificate also survives reification with its simulation closure intact.
Wrapping cannot supply missing base paths or cycle evidence; deriving native
generation and checking of these representations remains open.

The [path-transport construction](docs/research/PATH_TRANSPORT.md) conditionally
reproduces a path from a distinct, related starting point. It retains the
original, the copy, and correspondence at every vertex through composition
and finite lifting. The exact local law needed for one-for-one native
reproduction is identified but remains unproved.

The [native transport countermodel](docs/research/NATIVE_TRANSPORT_OBLIGATION.md)
satisfies all 38 declared clauses and an actual two-step simulation cycle,
yet related ground-generated forms fail finite continuation reproduction.
The formalization therefore needs operational reproduction evidence beyond
the existing closure and relation clauses.

The [finite layer graph adapter](docs/research/LAYER_GRAPH.md) executes the
record composition and lifting operations through Lean and earns exact transformation support in Verifier's
graph ledger. It binds ordered operands, repetitions, output encodings, and
the source inventory. Serialized support can be replayed through the same
checking mechanism; the stronger mathematical claims remain unresolved.

The [unary formation boundary](docs/research/UNARY_FORMATION.md) identifies
what that compositional layer must add: a fixed expression over ground and
unary application cannot combine two independent inputs. The checked
obstruction concerns fixed terms; a derived recursive or represented mechanism
still requires its own native construction and correspondence proof.

## Ground and relations

The [sequencing construction](docs/research/SEQUENCING_LAWS.md) follows the
author's clarification that sequencing provides a common abstraction for
associative composition, with commutativity as an optional property. One
operation is bound to its identity, associativity, and relation-preservation
laws. Instruction concatenation and natural-number addition instantiate it;
instruction length preserves composition but loses order information.
Inverses are separate, so the interface includes monoids as well as groups.
The audit also retains the obstruction to the older uniform noncommutation
clause. Native realization and ordinal interpretation remain open.

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
Package Index is not this project. From PyPI or a checkout, with Python 3.10 or newer:

```console
pip install hypermath-foundations
```

Or with verification dependencies from source:

```console
python -m pip install '.[verification]'
python -u scripts/check_foundation.py --require-self-derivation
```

This runs fresh Lean checks and a Verifier Standard (VSTD) evidence session,
then applies the self-derivation gate. Unresolved claims remain `UNKNOWN`, and
the gate exits with status 2. Evidence is retained under `build/verification`.

## Python Library Architecture and API

The `hypermath_foundations` package provides an executable foundation for formal
mathematical audits, fractal representations, non-well-founded set graphs, and
derivational bridges.

```python
import hypermath_foundations as hmf
```

### 1. Quadrilateral Filtration

`FiltrationTier` names the four nodes of the filtration diagram:

- **`SYNTAX`**: The written form of a derivation term.
- **`SUBSTANCE`**: What the term is made of, independent of its spelling.
- **`SEMANTICS`**: What the term denotes.
- **`ABSTRACTION`**: The schema the term instantiates.

`QuadrilateralFiltration` is the engine that moves between them. It takes no
constructor arguments; the terms are passed to its methods.

```python
from hypermath_foundations import FiltrationTier, FormTerm, QuadrilateralFiltration

term = FormTerm("apply", (FormTerm.ground(),))
assert str(term) == "apply(ground)"

filtration = QuadrilateralFiltration()
assert filtration.syntax_similarity(term, term)

proof = filtration.abstraction_reflexive(term)
assert proof.rule_name == "reflexive"

assert [tier.name for tier in FiltrationTier] == [
    "SYNTAX", "SUBSTANCE", "SEMANTICS", "ABSTRACTION",
]
```

### 2. Accessible Pointed Graphs and Quine Atoms

Constructs non-well-founded sets under Aczel's Anti-Foundation Axiom (AFA) and
computes bisimulation equivalence on membership graphs:

```python
from hypermath_foundations import AccessiblePointedGraph, QuineAtom

# A Quine atom satisfies Ω = {Ω} (a 1-cycle membership graph)
omega = QuineAtom()
assert omega.satisfies_self_membership()
assert str(omega.to_form()) == "quine_atom"

# 2-cycle graph x -> y -> x unwinds to the identical infinite tree
apg = AccessiblePointedGraph(
    nodes=frozenset({"x", "y"}),
    edges=frozenset({("x", "y"), ("y", "x")}),
    root="x",
)
assert apg.outgoing("x") == ["y"]
```

### 3. The Five Hypercalculi

Five peer bridges, each an independent calculus in
`hypermath_foundations.calculus_bridge`. None of them contains the others:

```python
from hypermath_foundations import (
    HyperCalculus,
    LanguageCalculus,
    MathCalculus,
    MetaCalculus,
    OrdinalCalculus,
)

math = MathCalculus()
assert math.verify_leibniz_rule(lambda x: x**2, lambda x: x + 1, 1.5)

meta = MetaCalculus()
meta.add_rewrite_rule("identity", lambda term: term)
assert "identity" in meta.rules

language = LanguageCalculus()
language.add_production("S", ["a", "S"])
assert len(language.productions) == 1

for calculus in (HyperCalculus(), OrdinalCalculus()):
    assert calculus.__class__.__module__.endswith("calculus_bridge")
```

### 4. Proof Trajectories and Homotopy

Tracks derivation trajectories through state spaces, establishing homotopy
equivalences between alternate proof paths:

```python
from hypermath_foundations import (
    FormTerm,
    ProofTrajectory,
    TrajectoryHomotopy,
    TrajectoryStep,
)

start = FormTerm.ground()
end = FormTerm("apply", (start,))
step = TrajectoryStep(step_index=0, source=start, target=end, rule="apply_rule")

trajectory = ProofTrajectory(start=start, end=end, steps=(step,))
assert trajectory.length() == 1

# are_homotopic is a static predicate over two trajectories sharing a boundary.
assert TrajectoryHomotopy.are_homotopic(trajectory, trajectory)

# The 2-cell itself records which rewrite rule relates the two paths.
homotopy = TrajectoryHomotopy(
    source_trajectory=trajectory,
    target_trajectory=trajectory,
    rewrite_rule="identity",
)
assert homotopy.certified
```

### 5. Bounded Evidence Audits (CLI and Python)

Audits formal Lean 4 declarations and exports Verifier Standard (VSTD) receipts:

```python
from hypermath_foundations import evaluate_gate, run_audit

# Runs bounded audit over checkout
report = run_audit(".", timeout=60, inventory_only=True)
passed = evaluate_gate(report)
```

CLI entry point:

```console
hypermath-foundations audit --inventory-only
```


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
