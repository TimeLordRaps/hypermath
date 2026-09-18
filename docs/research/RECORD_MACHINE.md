# Rule-by-rule execution of represented derivations

[`RecordMachine.lean`](../../lean4/Hypermath/RecordMachine.lean) gives an explicit
execution model for the [composed finite calculus](COMPOSED_GROUND_DERIVATIONS.md).
It compiles each retained inference into an instruction, checks each premise
as that instruction executes, and checks submitted traces against those exact
transitions. The input protocol also accepts the existing packed record and
formula codes. This supplies a concrete computation to internalize in the
ranked construction; it does not yet derive execution from native Hypermath.

## Instruction semantics

A state is either a stack of syntactic formulas or failure. An empty stack is
distinct from failure. Instructions have the following effects:

| Instruction | Required stack and effect |
| --- | --- |
| Primitive | Push the instantiated conclusion of the selected primitive rule |
| Continuation close | Require the top formula to be the exact structural continuation premise; replace it with the corresponding similarity conclusion |
| Distinctness close | Require the exact structural distinctness premise; replace it with the corresponding absence-of-simulation conclusion |
| Orbit close | Require the exact structural orbit premise, including its two applications; replace it with the corresponding similarity conclusion |
| Join | Pop the right and left premises and push their conjunction, preserving operand order |
| Left or right projection | Require the whole annotated conjunction at the top; replace it with the selected side |

Underflow and mismatched premises produce failure. Failure is permanent: a
later primitive cannot restore a successful state. The compiler emits premise
instructions before the instruction consuming them, including both branches
of every conjunction. Projection therefore cannot skip a failed unselected
branch. `step` does not invoke the old checker or receive a typed proof.

## Checked correspondence

For every raw record `r` and starting formula stack `s`, `execute_program` proves

```text
execute(program(r), some(s)) =
  if r.valid then some(r.conclusion :: s) else failure.
```

This covers invalid as well as valid records and arbitrary surrounding stacks.
`check_agrees` then proves that checking for exactly one final formula from an
empty stack agrees with the existing composed checker. The compiled checker's
relative soundness follows for every model satisfying that calculus's stated
premises. `check_quote` proves acceptance of every quoted typed derivation.

`checkNumbers_agrees` proves the same correspondence for **all** packed inputs,
including malformed and wrong-sort inputs, using the existing exact decoders.
The numerical interface never expands the exponentially large unary term.
The decoder remains host infrastructure; this theorem does not internalize it.

## Replay is bound to the record and claim

`trace` retains one resulting state after every instruction. `replay` accepts a
submitted trace exactly when every state equals the result of the corresponding
instruction and the lengths agree. `replay_iff` proves that this is exactly the
generated trace, and `replay_unique` proves uniqueness for a fixed program and
initial state.

`checkTrace` binds replay to `program(r)`, the empty initial stack, and a final
stack containing exactly the claimed formula. Its characterization theorem is

```text
checkTrace(r, claim, states) = true  iff
  states = trace(program(r), some([])) and composedCheck(r, claim) = true.
```

Thus a submitted trace cannot certify a record with an invalid inference even
when the claim has a different valid derivation. A faithful trace of failure
passes replay but fails acceptance. The record, claim, and states are data;
an additional hidden proof object is not an input to this check.

The trace uses host lists and formula values. Its native representation and
the derivation of its checking operations remain to be constructed.

## Resource statement and validation

The compiler emits exactly one instruction per record node. A complete trace
has the same number of recorded states. `program_length` and
`compiled_trace_length` prove these counts. This is **not** a running-time,
bit-size, or compression bound: formula equality, encoded-data parsing,
program construction, and the size of retained stack states have additional
costs. Repeated subrecords remain repeated.

[`RecordMachineChecks.lean`](../../lean4/RecordMachineChecks.lean) checks
acceptance, invalid projection, wrong predicates and arguments, underflow,
failure propagation, malformed input, omitted and extra trace steps, forged
states, wrong claims, and reuse of a trace for a different record. The source's
separation example executes five instructions. A packed-input example and
rejection examples also execute as part of the mandatory audit process.

The `record_machine` audit requires 40 exact dependency reports: 20 without
axioms, 14 with propositional extensionality, and six additionally with Lean's
quotient equality principle. No report uses classical choice, an admission,
or a native Hypermath axiom or parameter. Source digests, missing reports,
unexpected or hidden dependencies, and unsuccessful execution are enforced.
Admissions elsewhere in the imported foundation remain separate.

## Next native construction

The required native implementation must represent instruction tags, arguments,
formula comparisons, stack operations, and the packed decoding procedure, then
prove that its transitions realize `step` on those representations. It must
also prove that native acceptance checks the entire execution and its exact
claim. The model's existing congruence-preserving path relation has not acquired
these operations merely because the host machine exists.

The ranked target additionally requires a derivation of that acceptance claim
at the next rank, and representation of that derivation for further reuse.
None of the seven instructions asserts its own soundness or introduces a truth
or reflection principle. Arithmetic interpretation, transfinite generation,
coverage, and novelty remain separate proof obligations.
