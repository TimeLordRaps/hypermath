# Composition from retained derivation context

The author's proposal places composition at layer `n+1` relative to a
self-derivation kernel at layer `n`. Self-derivation supplies the verification
geometry; composition then develops further logical surfaces. The new
[`ContextualComposition.lean`](../../lean4/Hypermath/ContextualComposition.lean)
connects three existing finite constructions: ground derivations, executable
rule/substitution calls, and recoverable representation layers. It provides
a concrete operational candidate for the missing composition step. It does
not prove that the native kernel generates that step.

## How both premises become available

Let `p` and `q` be complete finite derivation records, with checked conclusions
`A` and `B`. Let `P(p)` be the existing instruction program compiled from `p`.
The machine context is an ordered stack of formulas, with its top on the left.
For any initial context `Γ`, execution has the following shape:

```text
Γ  --P(p)-->  A :: Γ  --P(q)-->  B :: A :: Γ  --join-->  both(A,B) :: Γ
```

`::` means prepend one formula to the stack. `both(A,B)` is the ground
calculus's conjunction constructor. The `joint_state` theorem proves the
first two transitions' combined result for every pair of records and every
context, including failure if either record is invalid. `checked_context`
also verifies that the supplied claims equal the records' actual conclusions.
For a derivation with no externally assumed premises, execution starts at the
empty context `[]`.

The second program runs with the first conclusion still present. This follows
from the existing exact stack-effect theorem for compiled records; it is not
a new assumption granting joint availability. The complete first and second
records remain the children of the joined record.

The join invocation carries the rule, the substitution `[A,B]`, and the input
state `some (B :: A :: Γ)` in one encoded call. `join_call_runs` proves that
evaluating this single encoded input produces the joined stack. This is a
unary function on a structured configuration. Encoding the configuration as
one value does not establish that the native unary forming operation can
construct or evaluate it.

## Histories must meet at the actual intermediate context

`trace_append` proves that the history for two programs consists of the first
history followed by the second history run from the first program's final
state. `join_history` adds the final join transition and retains every
intermediate state, including failure states.

Consequently, two histories checked independently from `[]` cannot generally
be concatenated unchanged. The second history must be constructed in the
context left by the first. An executable counterexample rejects such an
isolated-history splice and accepts the properly contextualized history.

A separate counterexample shows why the retained context needs provenance:
a join call can execute with an arbitrary caller-asserted premise. Local
transition success establishes only what follows from that input context.
The joined-record checker instead starts from `[]`, executes both derivations,
and rejects a premise paired with an unsupported claim. The rejection persists
through every finite number of representation lifts.

## Preservation through successive layers

Write `J((p,A),(q,B)) = (join(p,q), both(A,B))` for `compose`. Its conclusion
uses the submitted claims, so a wrong claim cannot silently become the record's
actual conclusion. `check_compose` proves the exact Boolean equality

\[
\operatorname{check}(J(a,b))
=\operatorname{check}(a)\land\operatorname{check}(b).
\]

Let `L^k` denote `k` applications of the existing representation lift, beginning
at layer zero. Here `k` is a dimensionless natural number counting finite
representation boundaries. It is not an ordinal value or an arithmetic truth
rank. `lifted_check` proves the same checking equality after every such lift.
`lifted_recovery` recovers the exact joined record and both submitted claims.
`lifted_history` reconstructs the complete canonical execution history from
that recovered record. `joined_trace_check` proves that transition replay and
final-conclusion checking agree with both premise checks.

The trace is reconstructed from the retained record. No claim is made to
retain arbitrary annotations or an independently submitted execution log.
Conditional semantic soundness is inherited from the existing ground-calculus
checker in any supplied model of that calculus.

## Which composition this establishes

There are two operations with different purposes:

| Operation | Result | Established role |
| --- | --- | --- |
| `LayeredDerivation.Expression.seq` | Ordered list of checked evidence | Associative sequencing with an identity, modulo checked expansion |
| `ContextualComposition.compose` | A record deriving `both(A,B)` | Existing conjunction inference with both premises and their histories retained |

The joined record is a binary tree. Rebracketing changes its syntax and the
syntax of its conjunction conclusion. The monoid law for evidence sequencing
does not assert literal associativity or a unit for this inference constructor.
The self-derivation kernel is not identified with either operation's unit.

The existing Python graph adapter exposes primitive records, lifting, and
evidence sequencing. This extension is available in the Lean library and its
required audit; a new conjunction operation is not exposed by that adapter.

## Evidence and remaining mathematical obligation

The required layer audit now includes 17 additional dependency reports:
11 construction theorems and six premise/trace checks. Together with the
previous 45 reports, this stage accounts for 62 exact reports. The subsequent
[operational correspondence criterion](OPERATIONAL_CORRESPONDENCE.md) adds
18 reports, bringing the required layer audit to 80. Their only axiom dependencies
are Lean's propositional extensionality and quotient soundness where used.
No new native axiom or admitted proof was added.

Run the existing bounded audit and focused software regressions from the
repository root:

```console
python -u -m hypermath_foundations audit --root . --timeout 60 --output build/contextual-audit.json
python -u -m pytest tests/test_audit.py tests/test_integrity_commands.py -vv -s --durations=10 --timeout=60
```

The [fixed unary-term obstruction](UNARY_FORMATION.md) remains intact. The
construction here uses recursive execution, a structured context, and a
decoder. It supplies a precise candidate to compare with native forming,
but does not derive those operations from `Form` and `f2f`.

The next native adequacy obligation is to construct a representation of these
configurations and prove that native transitions preserve their observations
and realize the checked context transition. Further obligations concern
internally represented acceptance, ordinal interpretation, limit stages,
and the intended arithmetic truth property. This finite construction does
not discharge them or establish the proposed novelty.
