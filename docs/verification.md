# Continuous integration and the grounding dependency

Continuous integration (CI) checks the Python audit package on Linux and Windows,
checks the preserved source snapshots, and installs the built wheel in an isolated
environment. The separate `self-derivation gate` runs the pinned Lean toolchain,
records transitive assumptions, replays the audit through a Verifier Standard
(VSTD) mechanism, and retains its evidence even when the gate fails.

The package name is `hypermath-foundations`, with import name
`hypermath_foundations`. Both distinguish this repository from the unrelated
`hypermath` project on the Python Package Index. The optional `verification`
extra uses the released `verifier-standard==1.3.0` interface; it does not import
an adjacent development checkout.

## What the checks establish

| Surface | Evidence | Current interpretation |
| --- | --- | --- |
| Software | Unit tests, source hashes, built and installed wheels | The exercised software contracts hold in the tested environment |
| Lean elaboration | Fresh build and dependency output | The translation compiles; admitted proofs can still exist |
| Finite traces | Seven parameter-relative production proofs and 28 axiom-free generic/concrete checks | Constructive self-read, composition, endpoint iteration, and recorded-step preservation; no native arithmetic interpretation yet |
| Finite arithmetic observations | Thirteen parameter-only results and four source-relative results | Least finite closure, length interpretation and reuse preservation; universal ground-spanning is refuted |
| Observation boundary and full model | 24 observation reports: 22 axiom-free, two with classical choice; an interpretation of all 38 logical clauses | Decoder factorization and finite reuse preservation have explicit premises; the noncomputable existence result is not a native checker |
| Finite action | Eleven production milestone results and a six-form model of all 38 logical clauses | Finite-orbit operations descend, but preserving all standard numeral-equality queries requires injectivity; the countermodel refutes a decoder for those queries |
| Finite ground syntax | 23 exact dependency reports for primitive-rule records, their checker, and reuse | Four-rule checker soundness uses the existing source premises; native reification of acceptance and arithmetic interpretation remain open |
| Composed ground calculus | 26 exact dependency reports for typed derivations, complete record reconstruction, and premise checking | Soundness uses seven existing clauses; native encoding and internally derived acceptance remain open |
| Self-derivation | Target theorem, transitive assumptions, stable inputs, fresh replay, and a full-clause separation model | Conditional proof admissibility remains unresolved; even the exact target does not imply the tested finite-action or ordinal-computation bridges |
| Source adequacy | Required correspondence with native propositions and derivations | `UNKNOWN`; no checked correspondence theorem exists |
| Recursive arithmetic completeness | Required arithmetic interpretation, self-representation, and completeness proof | `UNKNOWN`; the dependency and receipt do not discharge these obligations |

The intended “recursively groundedly complete” arithmetic requires the last two
rows as well as self-derivation. It must specify the arithmetic sentences being
interpreted, the truth or derivability relation being preserved, the encoding of
the system's own syntax, and preservation under fractal meta-representations.
These remain mathematical obligations, not properties inferred from a dependency
graph. The [research target](research/FRACTAL_COMPLETENESS.md) and
[proof audit](research/PROOF_AUDIT.md) describe the unresolved mechanisms.

## Reproduce

Install the repository's pinned Lean toolchain with Elan, then run:

```console
python -m pip install '.[dev,verification]'
python -m pytest tests -vv -s --durations=10 --timeout=60
python -u scripts/check_reference_sources.py
python -u scripts/check_audit_models.py
python -u scripts/check_foundation.py --require-self-derivation --timeout 60
```

The final command retains `build/verification/audit.json` and its VSTD artifacts
before returning 2 for an unestablished self-derivation claim. Use
`--require-complete` to enforce the stronger arithmetic obligation. Without an
explicit mathematical requirement, completing an audit is a software operation;
it is not a proof-completion verdict. A source-only inventory cannot discharge a
proof gate.

A completed native execution requires all nine process checks:
`lean_build`, `dependency_output`, `countermodel`, `finite_trace`, `observation`,
`full_model`, `finite_action`, `ground_syntax`, and `ground_derivation`. The last
runs `lean4/GroundDerivationChecks.lean`; the preceding two run
`lean4/FiniteActionCountermodel.lean` and `lean4/GroundSyntaxChecks.lean`.
Omitting any process or supplying failed evidence
cannot satisfy the execution or replay gate.

For another run, select a fresh directory with `--output`; existing evidence
bundles are preserved rather than overwritten.

The evidence binds the source coordinate, actual input hashes, toolchain,
theorem target, declared assumptions, and observed outcomes. Input changes during
a run invalidate the result. A dirty checkout can be inspected, but is not
accepted as a clean pinned downstream foundation. Supplied JSON is not an
authenticated proof: the downstream integration checks the source and reruns the
mechanism.

The package also binds the exact self-derivation statement and the 67 reviewed
parameter/axiom declarations, finite construction and retained proposal definition
bodies, 35 proved milestone statements with their individually reviewed
dependencies, and trace, observation, finite-action, ground-syntax, composed-calculus,
and model sources.
The ground-syntax reporter separately binds 23 exact dependency reports,
including the four existing native rules used by its checker-soundness theorem.
The composed-calculus reporter binds 26 further exact dependency reports and
the three additional existing predicate-close clauses used by native soundness.
A new assumption,
weakened target or definition, or substituted reporter cannot pass by merely
removing `sorry`. These declaration identities
are a review baseline, not a consistency proof. Changing the mathematical basis
requires reviewing that policy along with the corresponding source changes.
The byte-bound Python package and Lean reporters use explicit line-feed endings
so Windows checkouts and Linux-built wheels share the same source identities.

The translation currently contains 16 admissions. The zero, successor, and
opaque path-length computation proposals are now named `Claim` definitions
because a model of the declared clauses refutes them. The decrease records
withdrawal of unsupported theorems, not completed proofs. The model does not
encode the stronger unformalized native generativity requirement. It also
satisfies the exact current self-derivation proposition while refuting the
finite-action criterion and all three computation claims, so self-derivation
alone cannot certify an arithmetic interpretation. The
conditional host-action construction does not establish native adequacy.

## VSTD boundary

The adapter uses the released VSTD proposition, evidence-store, and verification
session APIs. A mathematical claim supplied without a source checkout stays
`UNKNOWN`. With the checkout, the versioned `audit-replay-2` mechanism replays the
audit and checks its input bindings. Replay agreement compares the complete report,
including runner and before/after source coordinates, execution metadata, admissions,
every claim status and rationale, and every check payload. The verbose `lean_build`
transcript is the only normalized value: Lake's `Built`/`Replayed` step-state word and
the scheduling numerator on those build-progress lines are ignored because they record
cache use and parallel completion order rather than different module bytes. Complete
build-output lines are then compared as an order-independent multiset. The total job
count, marker, target, message, line ending, and multiplicity remain exact. The attempt
flag, status, exit code, and reasons also
remain exact, while dependency and probe transcripts are compared in their original
order. It keeps native-source adequacy and arithmetic completeness unresolved.
If a requested replay fails or disagrees with the supplied evidence, the adapter
retains the bundle and raises an error. Packaging cannot override that failure.

The generated VSTD-1 generic-run receipt records the evidence-packaging operation;
the domain verification-session records are bound artifacts within that receipt.
Receipt integrity is not arithmetic truth, and this integration does not claim
VSTD-4 conformance or independent verification of Lean's foundations. The execution
environment, pinned checker and stated assumptions remain part of the trust boundary.

## Workflow policy

Successful process execution and a matching replay can reproduce a failed
source-byte or assumption policy. The audit commands therefore require an
attempted, passing assumption policy before returning integrity success.
Failures retain their evidence and return exit code 1; unresolved mathematical
requirements return 2 only after the integrity check passes. Inventory-only
operation keeps its documented non-proof scope. Byte-bound Lean checker sources
have explicit line-feed checkout attributes, including the primitive source
syntax and reporter. A fresh-checkout regression exercises Git's automatic
Windows line-ending conversion without weakening the recorded byte digests.

The mathematical job intentionally fails while its obligation is unresolved;
there is no `continue-on-error` conversion to a passing result. Software jobs run
independently so repairs can still be tested. Ordinatics' publishing workflow
requires its entire checks workflow, including the foundation and completeness
gate, before requesting a publishing token.

Direct external actions are pinned to full commit identifiers and tokens have
read-only permissions for checks. The Linux toolchain bootstrap checks the Elan
release archive's digest before execution and installs `lean4/lean-toolchain`.
See GitHub's [workflow reuse documentation](https://docs.github.com/en/actions/concepts/workflows-and-actions/reusing-workflow-configurations).
Repository branch-protection settings are separate administrative configuration;
these workflows do not silently alter them.
