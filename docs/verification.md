# Continuous integration and the grounding dependency

Continuous integration (CI) checks the Python audit package on Linux and Windows,
checks the preserved source snapshots, and installs the built wheel in an isolated
environment. The separate `self-derivation gate` runs the pinned Lean toolchain,
records transitive assumptions, replays the audit through a Verifier Standard
(VSTD) mechanism, and retains its evidence even when the gate fails.

The package name is `hypermath-foundations`, with import name
`hypermath_foundations`. Both distinguish this repository from the unrelated
`hypermath` project on the Python Package Index. The optional `verification`
extra targets `verifier-standard==2.0.0`; it does not import an adjacent
development checkout. This target is locally candidate-qualified, not a statement
that 2.0.0 has been published. Until publication, install the reviewed wheel from
the release coordinator before resolving this extra.

The adapter preserves the legacy VSTD-1 generic-run packaging contract and real
`VerificationSession` replay dispatch. This is not a native VSTD-NAMESPACE
certificate, nor does receipt integrity resolve any mathematical proof obligation.
Candidate changes require requalification; equal version strings alone do not
identify equal implementation bytes.

## What the checks establish

| Surface | Evidence | Current interpretation |
| --- | --- | --- |
| Software | Unit tests, source hashes, built and installed wheels | The exercised software contracts hold in the tested environment |
| Lean elaboration | Fresh build and dependency output | The translation compiles; admitted proofs can still exist |
| Finite traces | Seven parameter-relative production proofs and 28 axiom-free generic/concrete checks | Constructive self-read, composition, endpoint iteration, and recorded-step preservation; no native arithmetic interpretation yet |
| Finite arithmetic observations | Thirteen parameter-only results and four source-relative results | Least finite closure, length interpretation and reuse preservation; universal ground-spanning is refuted |
| Observation boundary and full model | 24 observation reports: 22 axiom-free, two with classical choice; an interpretation of all 44 logical clauses | Decoder factorization and finite reuse preservation have explicit premises; the noncomputable existence result is not a native checker |
| Finite action | Eleven production milestone results (`FiniteAction.lean`) and a six-form model of all 44 logical clauses | Finite-orbit operations descend, but preserving all standard numeral-equality queries requires injectivity; the countermodel refutes a decoder for those queries |
| Finite ground syntax | 23 exact dependency reports for primitive-rule records, their checker, and reuse | Four-rule checker soundness uses the existing source premises; native reification of acceptance and arithmetic interpretation remain open |
| Composed ground calculus | 26 exact dependency reports for typed derivations, complete record reconstruction, and premise checking | Soundness uses seven existing clauses; native encoding and internally derived acceptance remain open |
| Self-derivation | Exact named target, conditional assembly, stable inputs, fresh replay, and two full-clause models | One model refutes the target; another satisfies it without the arithmetic bridges. The target is unproved and strict proof admissibility fails |
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

A completed native execution requires all fourteen process checks:
`lean_build`, `dependency_output`, `countermodel`, `finite_trace`, `observation`,
`full_model`, `finite_action`, `target_at_limit`, `ground_syntax`,
`ground_derivation`, `record_encoding`, `record_machine`, `layered_derivation`,
and `layer_consumption`. The final five run
`lean4/GroundDerivationChecks.lean`, `lean4/RecordEncodingChecks.lean`,
`lean4/RecordMachineChecks.lean`, `lean4/LayeredDerivationChecks.lean`, and
`lean4/LayerConsumptionChecks.lean`
respectively.
Omitting any process or supplying failed evidence
cannot satisfy the execution or replay gate.

The report carries two further checks, `assumption_policy` and
`proof_admissibility`, which the audit derives from what those reported rather
than running. Neither is in the conjunction above, so a report can say its
execution completed while a check in it fails --- and `proof_admissibility` is
the one expected to, because the target names an unproved proposition.

For another run, select a fresh directory with `--output`; existing evidence
bundles are preserved rather than overwritten.

The evidence binds the source coordinate, actual input hashes, toolchain,
target statement and declaration kind, declared assumptions, and observed outcomes. Input changes during
a run invalidate the result. A dirty checkout can be inspected, but is not
accepted as a clean pinned downstream foundation. Supplied JSON is not an
authenticated proof: the downstream integration checks the source and reruns the
mechanism.

The package also binds the exact self-derivation statement and the 66 reviewed
parameter/axiom declarations, finite construction and retained proposal definition
bodies, 76 proved milestone statements with their individually reviewed
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

Each required process binds a group of exact dependency reports, and the sizes
below are measured from `src/hypermath_foundations/_reports.py` rather than
written by hand. `tests/test_declared_counts.py` fails if this table and the
sources disagree, and also fails if a group is added and reported nowhere:

| Process | Bound reports |
| --- | --- |
| `layer_consumption` | 836 exact dependency reports |
| `layered_derivation` | 186 exact dependency reports |
| `full_model` | 98 exact dependency reports |
| `record_machine` | 87 exact dependency reports |
| `countermodel` | 225 exact dependency reports |
| `record_encoding` | 45 exact dependency reports |
| `finite_trace` | 28 exact dependency reports |
| `ground_derivation` | 26 exact dependency reports |
| `observation` | 24 exact dependency reports |
| `ground_syntax` | 23 exact dependency reports |
| `finite_action` | 23 exact dependency reports |
| `target_at_limit` | 22 exact dependency reports |

`layer_consumption` is the one group whose individual lists are not pinned.
It sweeps every public declaration in `lean4/Hypermath/`, and what is reviewed
is the shape the sweep has rather than the lists it produces: which layers'
declarations each file's content consumes, and which declared clauses nothing
consumes at all. A rewritten proof moves counts and leaves both alone; a new
declaration has to join the inventory before it can be reported, so it cannot
escape the measurement by being new.

Four of these were reported in no document at all until this table existed.
They were the four that had grown --- each research note states the size of the
group as it stood when that boundary was added, the group then grows past it,
and nothing revisits the sentence. A total no sentence reports is a total no
sentence can contradict, so the existing scan stayed green over an arbitrary
amount of drift.

The translation currently contains no admissions. The zero, successor, and
opaque path-length computation proposals are now named `Claim` definitions
because a model of the declared clauses refutes them. The decrease records
withdrawal of unsupported theorems, not completed proofs. The model does not
encode the stronger unformalized native generativity requirement. It also
satisfies the exact current self-derivation proposition while refuting the
finite-action criterion and all three computation claims, so self-derivation
alone cannot certify an arithmetic interpretation. The
conditional host-action construction does not establish native adequacy.

The [cycle boundary](research/CYCLE_BOUNDARY.md) adds the converse separation:
another full-clause model refutes the exact self-derivation target and the
nontrivial simulation-pair claim. The admitted cycle and pair theorems have
been withdrawn. `selfDerivation` now names its original proposition; it is
not an available proof. Conditional assembly proves that the missing cycle
is precisely the remaining conjunct. Integrity accepts this exact definition,
but proof admissibility fails and the mathematical claim stays `UNKNOWN`.
The strict gate continues to require a closed theorem, so removing admissions
or assuming the cycle in an implication cannot turn the gate green.

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
