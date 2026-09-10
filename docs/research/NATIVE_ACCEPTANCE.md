# Native closure and acceptance of a represented derivation

This note records a checked boundary in the existing faithful model. It does
not add native axioms, redefine the source's closure predicates, or provide the
missing internal checker. The objective remains a source-adequate ranked
self-representation and arithmetic interpretation.

## Source correspondence

The current [ground specification](../../L0_ground.hm), Section I, distinguishes
`Form`, a structural entity, from its first-class proposition type `Prop`.
Section VIII declares syntax, substance, semantics, and form closure as claims
about forms. [Layer 1](../../L1_relations.hm), Section IV, gives the executive
closes and ground anchoring. The Lean translation reads these propositions in
Lean's host proposition sort; adequacy for the source's own proposition type
remains open.

The earlier [frame kernel](../../references/seed-ai/hypermath_frame/spec/kernel.hm),
Section 2, specifies parsing, relation-stratum checks, import and name resolution,
and propagation of unresolved steps. Its minimum-stratum rule presupposes
justified step relations. These comments do not give a formal substitution
and premise-matching judgment for every derivation step. A comparison of
declared labels alone would not supply that judgment. This earlier kernel's
relations also differ from the current specification; their names do not
establish a translation.

The [composed calculus](COMPOSED_GROUND_DERIVATIONS.md) gives a precise finite
instance of premise checking. Its [encoding](RECORD_ENCODING.md) retains every
rule, argument, annotation, and premise. `FullAxiomModel.lean` supplies a model
of all 38 current logical clauses with exact recovery of those records after
interpretation. The following result uses that same model and unchanged clauses.

## A closed representation can contain an invalid inference

Let `c` be the formula saying that ground structurally continues from itself.
Consider two raw records:

```text
good = primitive groundSelf
bad  = projectLeft c c good
```

Both records claim conclusion `c`. The first is an instance of the primitive
ground-self rule. The second falsely annotates its premise as proving `c and c`,
although that premise proves only `c`. Projection requires the conjunction
premise, so the exact record checker accepts `good` and rejects `bad`.
The conclusion itself is true in the model and has a valid derivation.

`NativeRecordReady(r)` is a conjunction of existing interpreted predicates:

- syntax, substance, semantics, and form closure of `recordValue(r)`;
- derivation from ground to that value;
- definition of that value anchored at ground;
- discharge to that value with ground as its evidence argument, in the current
  translated `Discharge(conclusion,evidence)` convention.

This is a named host conjunction for the test, not a new native predicate.
In the model, every raw record satisfies it. The four unary predicates are
true on all forms. `recordValue(r)=(recordCode(r),false)` is reached from
ground by exactly `recordCode(r)` applications. The existing definition and
discharge clauses give the remaining two components. Consequently these
conditions hold for `bad`, despite its invalid projection.

| Checked declaration | Proposition established |
| --- | --- |
| `record_native_ready` | Every encoded raw record satisfies the stated native executive and anchoring conditions in this model |
| `same_conclusion_opposite_acceptance` | `good` and `bad` have the same conclusion and opposite checker results |
| `rejected_record_has_native_closure` | `bad` satisfies those conditions and has a true, derivable conclusion, yet its encoded record is rejected |
| `no_conclusion_only_record_checker` | No Boolean function of just the computed conclusion and claimed formula can agree with this record checker on every record |
| `native_closure_is_not_record_acceptance` | The stated native conditions are not equivalent to acceptance of each record against its own conclusion |
| `full_clauses_with_rejected_closed_record` | All 38 clauses hold together with the closed but rejected record |

The failure concerns validity of this exact inference tree. It is not a false
arithmetic conclusion, an inconsistency, a failure of faithful storage, or a
proof that every possible native acceptance construction fails. In particular,
another relation may inspect the retained tree; the construction must derive
its operation and correspondence instead of inheriting correctness from closure.

## What the next native construction must establish

The existing host checker has explicit obligations at every constructor:

| Record constructor | Required acceptance evidence |
| --- | --- |
| Primitive rule instance | Correct rule tag and its instantiated conclusion |
| Continuation, distinctness, or orbit close | An accepted premise with exactly the source predicate and arguments required by that close |
| Conjunction introduction | Acceptance of both complete premise records |
| Left or right projection | Acceptance of the entire premise and equality of its conclusion with the annotated conjunction |
| Encoded input | Successful, sort-correct decoding without trailing or malformed data, followed by the corresponding rule checks |

A native implementation needs represented rules performing these checks, a
derivation connecting their execution to the existing record checker, and
acceptance formulas bound to the exact record and conclusion. Its proof must
cover the rejected projection above. Concluding that `c` is derivable from a
different valid record does not certify `bad`.

For the ranked self-closing target, that execution must itself yield a
derivation of the acceptance claim at the next rank. Repeating the same rule
must represent that acceptance derivation while preserving the needed
observations. The current formula grammar has no acceptance constructor and
no native execution semantics for the host checker. Adding such a constructor
as an assumption would not derive it from the source.

The distinction also prevents a false shortcut through the executive closes:
they certify structural conditions on the represented entity. They do not
currently bind every inference step, its premises, and its claimed result.
Neither this missing bridge nor a successful finite bridge settles transfinite
generation, arithmetic soundness, coverage, or novelty.

## Audit boundary

The six new declarations are part of the mandatory `full_model` process.
Two have no axiom dependencies; one uses propositional extensionality; two
use propositional extensionality and quotient soundness; and the combined
full-clause statement additionally uses classical choice through the existing
model proof. None uses an admission or a native axiom. The full-model group
contains 26 exact reports, with source bytes and dependency sets enforced by
the audit policy. This does not remove the foundation's 16 admission sites.
