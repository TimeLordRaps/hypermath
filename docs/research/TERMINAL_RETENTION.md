# Testing primitive forming as the retained-record evaluator

The [operational correspondence criterion](OPERATIONAL_CORRESPONDENCE.md)
gives sufficient conditions for repeated checking and layer passage. This
result tests one specific realization: use the primitive forming operation
itself as the concrete step, in the existing model of all 38 declared logical
clauses. That realization is impossible under the criterion's total execution
protocol, regardless of the encoder and decoder chosen.

The result is proved in [`FullAxiomModel.lean`](../../lean4/FullAxiomModel.lean)
using the generic [`TerminalRetention.lean`](../../lean4/Hypermath/TerminalRetention.lean).
It does not refute other models, the intended native theory, or a protocol with
different stopping, guarding, or layer-transition rules.

## The precise candidate

In this already checked model, a `Form` is a pair `(n,b)`, where `n` is a
dimensionless natural-number position and `b` selects one of two successor
chains. Primitive forming is defined by

\[
f(n,b)=(n+1,b).
\]

The candidate consists of any `Representation Frame Form`, together with
`Respects view Frame.advance f2f`. Its encoder and decoder are not fixed to a
particular numeric coding scheme. The `Frame` retains the original derivation
record, its claim, the remaining program, current machine state, and complete
canonical execution history.

The protocol has a material condition: when a frame finishes its program,
`Frame.advance` leaves it unchanged. The total correspondence law therefore
requires every further primitive step on its concrete representation to keep
decoding as that same finished frame. This condition models continued concrete
execution while retaining the finished abstract result. A protocol that stops
concrete execution at completion has a different obligation.

## Why the candidate fails

Two positions on the same successor chain have forward runs that meet. From
`(a,b)`, take `c` steps; from `(c,b)`, take `a` steps. Both reach `(a+c,b)`.
These are finite execution counts, not ordinal values or arithmetic truth ranks.

`merged_fixed_states` proves the general consequence: if two represented
abstract states are fixed by their abstract step, and their concrete runs meet,
then those abstract states are equal. At the meeting point a single decoder
has a single value. The earlier correspondence theorem and fixed-state
preservation require that value to equal each of the two retained results.

Apply this to three different accepted ground-calculus records:

- the primitive ground self-continuation record;
- the primitive distinctness record at ground;
- the primitive continuation record at ground.

Their original records differ, and each complete execution is accepted by the
existing checker. The proof encodes their **initial frames**, runs them through
the proposed correspondence, and obtains their completed representations.
It does not assume that these reached representations are canonical encodings.

Different completed records would have to occupy different successor chains:
otherwise their forward runs meet and force the retained records to be equal.
There are three distinct records and only two chains. This is the contradiction
proved by `no_primitive_frame_checker`.

The executable probe independently checks acceptance of all three records and
an example of the orbit meeting. These finite examples supplement the theorem,
which quantifies over all encoders and decoders satisfying the stated interface.

## What this establishes about the source clauses

`full_clauses_without_primitive_frame_checker` combines the obstruction with
the existing proof that the model satisfies every one of the 38 logical
clauses. Consequently, those clauses alone do not entail existence of this
particular primitive-step realization of the total retained-frame protocol.

This is stronger than failure of one proposed numeric encoding. It is narrower
than impossibility of a native checker. The source model already refutes the
proposed self-derivation cycle; this result does not turn it into a model of
that stronger, currently unproved premise.

The following alternatives are **not settled** by this theorem:

- A protocol that stops primitive execution at completion, with a proved
  stopping condition and preservation of the completed artifact.
- A guarded or multi-step concrete operation separately derived from the
  native rules, with its own correspondence proof.
- A new carrier at layer `n+1`, or an explicitly retained layer index used by
  its representation and decoder.
- Another model or a source refinement that actually derives the required
  formation and execution behavior.

Adding an unproved guard or changing a definition to contain the host checker
would not establish native adequacy. These alternatives require constructions,
including rejection behavior and the exact record/claim binding.

## Audit scope

The model audit includes 11 new exact dependency reports: five generic
terminal-retention results and six model-specific results. It now requires 74
reports; the separate layer audit retains its existing 80 reports. Three of
the new reports have no axiom dependencies, seven use only propositional
extensionality, and the combined full-clause statement also inherits classical
choice and quotient soundness from the existing model proof. No native
assumptions or admitted proofs were added.

The original model definitions, all 38 clause types, and their proofs are
preserved. The new module is in the default library, with its bytes and
dependency reports required by audit policy.

```console
python -u -m hypermath_foundations audit --root . --timeout 60 --output build/terminal-audit.json
python -u -m pytest tests/test_audit.py tests/test_integrity_commands.py -vv -s --durations=10 --timeout=60
```

The next native candidate must specify its execution and completion protocol
and the representation carried across a layer boundary. The finite host
preservation results remain intact. Native realization, ordinal interpretation,
arithmetic completeness, and the proposed novelty remain unresolved.
