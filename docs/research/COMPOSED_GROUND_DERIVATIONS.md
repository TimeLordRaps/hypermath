# Composed ground derivations with retained rule records

`lean4/Hypermath/GroundDerivation.lean` extends the
[primitive ground fragment](GROUND_SYNTAX.md) to a finite typed calculus.
The checker accepts a structured rule record and a claimed conclusion. Every
premise is checked recursively; no external derivation or truth oracle is an
input. This advances the representation obligation in the
[fractal completeness target](FRACTAL_COMPLETENESS.md).

## Source correspondence and host logic

| Constructor | Source or logical premise | Exact conclusion |
| --- | --- | --- |
| `primitive` | The four primitive schemata in `L0_ground.hm`, Section III | The original structural assertion |
| `closeContinues` | `L0_ground.hm`, Section VI, `close struct-continues` | Similarity to ground, only from continuation to ground |
| `closeDistinct` | Section VI, `close struct-distinct` | Failure of simulation for the same ordered pair |
| `closeOrbits` | Section VI, `close struct-orbits` | Similarity of the twice-applied term to its original argument |
| `join` | Conjunction as used in L0 Section IV and L1's `ax-diff-in-relation-language` | Both checked conclusions |
| `projectLeft`, `projectRight` | Conjunction elimination in the existing host interpretation of source propositions | The indicated component of a checked conjunction |

Similarity, simulation, and structural predicates remain distinct. The calculus
does not infer symmetry, transitivity, equality, or congruence from a similarly
named predicate. It does not use admitted relation theorems. It only uses the
forward direction of the three declared predicate closes; it is not presented
as a complete calculus for all consequences of the source axioms.

The source already uses conjunction, and the existing Lean translation reads
it as Lean's logical conjunction. This module makes that same translation
explicit; it does not prove its adequacy for the source-native `Prop` or
discharge semantics. Inductive data, recursion, equality, and logical proof
rules remain host infrastructure.

## Typed derivations and untrusted records

`Formula` contains structural assertions, similarity, negated simulation, and
conjunction. `Derivation conclusion` retains a rule tree whose premises have the
types required by each rule. `Record` is untyped input data: a close or projection
can contain wrong annotations or a false premise claim.

`Record.valid` checks the entire tree. `check` additionally compares its
conclusion with the requested formula. Selecting a good component of a
conjunction does not bypass checking its other component. The negative probes
include a projection whose outer annotations match while its unused branch
contains a wrong primitive premise. That record is rejected.

`Record.derive` reconstructs a typed derivation after Boolean acceptance.
`reconstruct` performs the Boolean check and returns that derivation or no
result. Its only input is the record. `quote` maps a typed derivation back to
the same record grammar; it retains the rule tree and annotations.

## Checked results

For a record `r`, formula `s`, and typed derivation `d`:

- `check_quote`: checking `quote(d)` against its conclusion succeeds.
- `quote_derive`: quoting the reconstruction of an accepted record returns
  exactly `r`, not merely another proof with the same conclusion.
- `observe_derive`: consequently every observation of the retained record is
  preserved by reconstruction and quotation.
- `reconstruct_retains_record`: the executable reconstruction entry point has
  that same record-preservation property for accepted input.
- `represented_iff_derivable`: a formula has an accepted record exactly when
  it has a derivation in this specified finite calculus.
- `check_join_iff`: joining records succeeds exactly when both constituent
  records are valid.
- `derivation_sound` and `check_sound`: typed derivations and accepted records
  have true conclusions in every model satisfying the explicit rule premises.

The representability equivalence is a completeness statement for the checker
relative to its declared calculus. It is not semantic completeness for all
models, negation-completeness, or coverage of arithmetic truth.

The native soundness specialization uses eight existing source parameters,
the four primitive clauses, the three predicate-close clauses, and Lean's
propositional extensionality. It adds no native axiom, admission, or classical
choice. The `separation` example constructs the source's conjunction of
similarity to ground and failure of simulation with ground for an applied term.

## Audit and remaining native realization

The mandatory `ground_derivation` process runs `GroundDerivationChecks.lean`.
Its 26 exact dependency reports comprise 11 with no axioms, 14 with
propositional extensionality, and the native specialization just described.
The audit binds the calculus and reporter bytes and rejects omitted reports,
hidden assumptions, admissions, or failed execution. The primitive fragment's
23 reports remain a separate group. The broader translation still has
67 declared assumptions and 16 admissions.

The [record encoding](RECORD_ENCODING.md) now represents these finite rule
trees and formulas as single free ground terms, with packed numerical inputs
for execution and checked full recovery. Interpretation as semantic `Form`
still requires a proved recovery condition. The predicates and checker are not
internally reified, and there is no native derivation of a ranked acceptance
statement. Repetition of a record inside a tree makes no sharing or compression
claim. There is no arithmetic interpretation, transfinite generation rule, or
coverage theorem here.

The next realization step is faithful interpretation of the encoded records
and internal representation of their statement/checking operations.
It must retain the evidenced rule tree or prove the exact weaker observation
criterion it needs. A separate source-derived acceptance construction must
then satisfy the ranked interface; host-level reconstruction does not supply it.
