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
| Self-derivation | Target theorem, transitive assumptions, stable inputs and fresh replay | Conditional proof admissibility under disclosed Lean assumptions; unresolved while admissions remain |
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

For another run, select a fresh directory with `--output`; existing evidence
bundles are preserved rather than overwritten.

The evidence binds the source coordinate, actual input hashes, toolchain,
theorem target, declared assumptions, and observed outcomes. Input changes during
a run invalidate the result. A dirty checkout can be inspected, but is not
accepted as a clean pinned downstream foundation. Supplied JSON is not an
authenticated proof: the downstream integration checks the source and reruns the
mechanism.

The package also binds the exact self-derivation statement and the 68 reviewed
parameter/axiom declarations, the new `D` definition bodies, seven constructive
milestone statements, and the generic trace and probe sources. A new assumption,
weakened target or definition, or substituted reporter cannot pass by merely
removing `sorry`. These declaration identities
are a review baseline, not a consistency proof. Changing the mathematical basis
requires reviewing that policy along with the corresponding source changes.
The byte-bound Python package and Lean reporters use explicit line-feed endings
so Windows checkouts and Linux-built wheels share the same source identities.

## VSTD boundary

The adapter uses the released VSTD proposition, evidence-store, and verification
session APIs. A mathematical claim supplied without a source checkout stays
`UNKNOWN`. With the checkout, the mechanism replays the audit and checks its input
bindings. It keeps native-source adequacy and arithmetic completeness unresolved.
If a requested replay fails or disagrees with the supplied evidence, the adapter
retains the bundle and raises an error. Packaging cannot override that failure.

The generated VSTD-1 generic-run receipt records the evidence-packaging operation;
the domain verification-session records are bound artifacts within that receipt.
Receipt integrity is not arithmetic truth, and this integration does not claim
VSTD-4 conformance or independent verification of Lean's foundations. The execution
environment, pinned checker and stated assumptions remain part of the trust boundary.

## Workflow policy

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
