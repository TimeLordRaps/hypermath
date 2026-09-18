# Submitted execution frames across finite layers

The [record-layer construction](LAYER_PRESERVATION.md) retains records and
claims, from which a canonical execution can be reconstructed. This extension
retains the **submitted execution frame itself**. Its record, claim, remaining
instructions, current state, and recorded history survive composition and
every finite number of layer passages.

The implementation and proofs are in
[`RetainedExecution.lean`](../../lean4/Hypermath/RetainedExecution.lean).
This is an executable host construction. Native formation of the new atoms,
native checking, and ordinal interpretation still require separate proofs.

## Why the submitted frame matters

Consider a valid ground self-continuation record whose completed history has
been erased. Its record and claim still pass the record checker. Its submitted
frame fails execution checking because the history no longer demonstrates
the required transitions. Reconstructing a canonical history from the record
would replace the submitted evidence and lose that failure.

Here `readFrame (frameTree frame) = some frame` holds for every frame, including
erased histories, wrong states, and incomplete executions. The decoder reads
the submitted fields; it does not run the record to repair them.

`inspect` returns the ordered list of retained frames. Malformed encodings
produce `none`; a well-formed representation of a rejected frame still returns
that frame. `check` applies `Frame.accept` to every inspected frame. Acceptance
requires completion, replay of the submitted history, the claimed conclusion,
and agreement between the retained state and the history endpoint.

The checked example establishes all three facts together:

- the record in the erased-history frame remains a valid record;
- the erased history is recovered exactly after any finite number of lifts;
- checking that representation still returns `false` after those lifts and
  when it is composed with an accepted frame.

Thus retention of an artifact and acceptance of its evidence are distinct
operations, with rejection preserved throughout the construction.

## Composition and passage

Layer zero contains frames. At layer `n+1`, expressions have an empty value,
atoms containing encoded complete lower surfaces, and ordered composition.
The existing expression grammar and composition algebra are reused. The layer
index is a dimensionless natural-number count; no limit-ordinal stage is
defined here.

`composition_lift_preserves` proves, for any finite lift count, that:

1. lowering recovers the exact composed expression, including both operands
   and their grouping;
2. inspection yields the concatenation of the original inspected frame lists,
   preserving order and repeated occurrences;
3. acceptance is exactly the conjunction of the two original acceptance
   results, with no premise that either input was accepted.

The common `Sequential.Sequencing` interface supplies associativity and an
identity under equality of inspected frame lists. `liftMap` preserves this
composition across adjacent layers. The empty expression is this host
sequencing identity; it is not identified with the kernel's self-derivation.
Equality of inspected lists is not identified with native similarity,
congruence, or simulation. Exact recovery retains grouping that this list
observation does not distinguish.

This composition sequences retained execution evidence. It does not by itself
create a new logical inference or splice two histories into one run. The
separate [contextual-composition construction](CONTEXTUAL_COMPOSITION.md)
addresses the premise context needed for the logical join rule.

`checked_surface_sound` gives model-relative soundness: given a model of the
ground calculus, every claim in an inspected and accepted frame list holds in
that model. It neither postulates the existence of the intended native model
nor asserts arithmetic truth coverage.

## Completion and representation format

`finished_frame_check` connects actual completed host execution to the new
layers: after any finite number of lifts, checking its retained frame gives
exactly the original record check, including rejection. Creating the next
atom does not require continued lower execution after completion. This avoids
imposing the total post-completion protocol tested in
[the two-chain obstruction](TERMINAL_RETENTION.md); it does not construct a
native stopping rule or refute that obstruction.

Frame encoding uses envelope `13`; its layer protocol uses envelope `14` and
an explicit layer tag. The earlier record-only layer protocol uses envelope
`12`. The new decoder rejects the earlier protocol and rejects a different
stated layer. These are local syntax-format identifiers, not ordinal values.
The existing Python graph adapter continues to use the earlier protocol;
these new frames are currently exposed through the Lean library and required
audit, without a new Python graph operation.

## Proof and audit scope

The default library and required layer reporter include the module. Its 36
new dependency reports comprise 23 general theorems, two law-carrying
constructions, and 11 regression results. Five have no axiom dependencies,
five use only propositional extensionality, and 26 also use quotient soundness.
No native assumptions, admitted proofs, or arithmetic axioms are added.

The finite preservation theorem is an implemented result at the host level.
Deriving these constructors, encodings, and checking operations from native
verification geometry remains the next mathematical obligation. Transfinite
reuse, ordinal arithmetic, internal truth coverage, and novelty remain open.

```console
python -u -m hypermath_foundations audit --root . --timeout 60 --output build/retained-execution-audit.json
python -u -m pytest tests/test_audit.py tests/test_integrity_commands.py -vv -s --durations=10 --timeout=60
```
