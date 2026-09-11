# Retaining the rule, substitution, and premises of a checking step

The finite checker now has an explicit schema executor in
[`RuleSubstitution.lean`](../../lean4/Hypermath/RuleSubstitution.lean).
It substitutes finite variable positions, matches each resulting premise, and
performs every instruction of the existing record machine. A complete checking
call retains the rule identifier, both substitution lists, and the exact input
stack in one free ground term. Executing the packed representation agrees with
the existing checker for every finite record, including invalid records.

This supplies a concrete finite substitution mechanism and represented checking
inputs. Execution still uses Lean's recursion, pattern matching, equality, and
list operations. Deriving their execution and acceptance within the source's
own forms and ranks remains open. The original 38 logical clauses and the
unchanged self-derivation target are not strengthened by this construction.

## Correspondence with the retained source

The retained [form kernel](../../references/seed-ai/hypermath_form/kernel.hm)
describes substitution as an ordinal-indexed mapping from variables to forms.
Its `metamath-step-is-apply` proposal, steps 1–2, retains the rule, substitution,
and substituted hypotheses and conclusion. Steps 3–6 then identify that
operation with `apply(rule)`. An actual input encoding and operational
correspondence are needed for that identification: a rule identifier alone
cannot determine which substitution was applied.

`no_rule_only_instantiation` proves this last distinction using the existing
`ax-diff` rule. Substituting ground and substituting apply(ground) produce
different structural conclusions. No function of just the rule identifier
can return both instantiated results. The new `Application` retains the
substitution instead of dropping it.

The source's `ordinal_wrap` correspondence is not assumed or established here.
Finite variable indices are natural numbers starting at zero; they identify
positions in explicit lists and have no physical unit. They do not assert
arbitrary ordinal indexing or validate an ordinal notation. Term patterns and
formula patterns have separate variable constructors and separate substitution
lists. This typing is an explicit finite refinement of the source description;
it is not claimed to follow from the opaque native `Form` parameter alone.

The executable rule table is restricted to the existing finite calculus:

| Rule family | Instances | Source or interpretation |
| --- | --- | --- |
| Primitive ground rules | ground-self, difference, continuation, orbit | `L0_ground.hm`, section III |
| Predicate closes | continuation, distinctness, orbit | `L0_ground.hm`, section VI |
| Conjunction | introduction and the two projections | The existing host-logical interpretation in `GroundDerivation.lean` |

These ten schemas cover all seven instruction constructors because the
primitive instruction itself has four rule variants. This is not an
implementation of unrestricted Metamath, capture-avoiding quantifier
substitution, or a native transfinite inference calculus.

## How a checking call operates

1. `Application.instantiate` checks the exact term and formula arities, then
   substitutes the indexed variables throughout the premises and conclusion.
   Missing, surplus, incorrectly sorted, and unbound arguments are rejected.
2. `consume` matches every substituted premise against the actual stack, in
   order. It returns the untouched remainder only after all premises match.
3. `Application.run` puts the instantiated conclusion onto that remainder.
   A failed state stays failed. It does not call the old `Record.valid`,
   `GroundDerivation.check`, or `RecordMachine.step` functions.
4. `compile` constructs the required application for an existing instruction.
   Conjunction introduction takes its two substitutions from the actual top
   two premises; those formulas are retained in the application.
5. `Call` combines that application with the complete input state. Its encoding
   preserves the difference between failure and a successful empty stack.
   `runCallNumber` receives only the encoded call, with no external premise
   stack or hidden derivation argument.

An individual call operates on a supplied premise stack. Its successful local
stack transformation does not prove that those premises were derived.
`encodedExecute_program` covers the entire compiled record, and
`encodedCheck_sound` starts execution with the empty stack. That whole-record
construction is what supports soundness of an accepted conclusion under the
existing finite ground-model assumptions.

## Checked correspondence and representation

| Declaration | Exact scope |
| --- | --- |
| `step_agrees` | The schema executor and old machine step agree for every instruction and every input state |
| `execute_program` | The schema executor has the exact old stack effect on every valid or invalid record, in every stack context |
| `readApplication_tree`, `decode_toTerm` | Applications retain their rule and both substitution lists through encoding and decoding |
| `readCall_tree`, `decodeCall_toTerm`, `call_toTerm_injective` | Complete calls retain the application and exact input state; equal encoded terms imply equal calls |
| `runCallTerm_toTerm` | Executing a represented call recovers the same local transformation without a separate stack argument |
| `encodedStep_agrees`, `encodedExecute_program` | Serializing and decoding every checking invocation preserves all instruction and record results |
| `encodedCheck_agrees`, `encodedCheck_sound`, `encodedCheck_quote` | Whole-record acceptance agrees with the original checker, is sound in the stated models, and accepts quoted derivations |

Applications use outer encoding tag 10; complete calls use tag 11. Existing
proof-record and formula encodings keep tags 8 and 9. The existing binary-tree
parser consumes its entire input, and the new typed decoders reject wrong-sort
records, malformed states, and unknown rule identifiers.

This is exact representation, not a compression result. The executable example
of a retained projection call has 119 prefix bits. Its corresponding unary
ground term has at least `2^119 - 1` applications by the existing `pack_bounds`
theorem. Execution uses the packed natural-number code; it does not expand that
unary term. No storage, runtime, or native-generativity claim follows from
writing the compact code as a single term.

## Adversarial checks and audit

The retained-call probe executes the same projection with a genuine conjunction
premise and with a forged non-conjunction premise. The first transforms the
stack; the second fails. Their complete encoded calls are provably different.
Other probes check substitution arities and sorts, unbound variables, reversed
premise order, retained stack context, failed states, wrong encoding sorts,
and a projection hiding a failed branch in the full proof record.

The mandatory record-machine process now reports its original 40 declarations
plus 47 substitution and call declarations. The new declarations depend either
on no axioms or on exactly Lean's propositional extensionality (`propext`) and
quotient soundness (`Quot.sound`). None uses classical choice, an admitted
proof, or a native logical clause. Source hashes bind the construction and
reporter; missing reports, altered dependencies, and replaced source fail the
audit. The foundation still has 67 declared assumptions and 11 admission sites.

## Remaining native obligation

The encoded objects are free ground syntax. Interpreting them as the source's
semantic `Form` values can still identify different codes unless a faithful
interpretation is established for the chosen realization. The schema executor
does not itself derive its pattern matching, equality tests, decoding, and
recursive control from native source rules, nor produce an acceptance formula
at a higher rank. Its rule table also remains part of the checking mechanism
rather than a self-interpreted native program.

The [finite-successor obstruction](CYCLE_WITNESSES.md) therefore still applies:
equating these checking transitions with simulation-preserving `f2f` steps on
finite ground forms requires a correspondence incompatible with the stated
successor agreement and strictness. A source-adequate typed execution and
rank-changing construction must resolve that issue explicitly. This finite
refinement neither assumes that resolution nor establishes arithmetic truth
coverage or novelty.
