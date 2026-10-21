# From local correspondence to repeated checking and layer passage

The [contextual composition construction](CONTEXTUAL_COMPOSITION.md) provides
an executable finite operation with retained premises and history. The native
bridge still needs an actual representation and a derivation showing how the
kernel realizes its checking transitions. The new
[`OperationalCorrespondence.lean`](../../lean4/Hypermath/OperationalCorrespondence.lean)
states sufficient local laws and proves what they would establish globally.
It also gives a checked counterexample to a weaker, tempting specification.

These are conditional correspondence theorems. No realization of the opaque
native `Form` or `f2f` is supplied, and no source axiom is added.

## Why checking only newly encoded inputs is insufficient

A canonical representation is a value produced directly by the encoder.
Different native values may decode to the same abstract configuration; call
them aliases. Native execution may reach an alias that the encoder never
produces directly.

The checked example uses Boolean abstract configurations, with the abstract
step always producing `true`. Its native values are natural-number labels,
not ordinal values or truth ranks. The encoder sends `false` to `0` and `true`
to `1`. The relevant decoder and step values are:

| Native label | Decoded configuration | Next native label |
| --- | --- | --- |
| `0` | `false` | `2` |
| `1` | `true` | `1` |
| `2` | `true` | `3` |
| `3` | `false` | `3` |

Every freshly encoded input passes the one-step comparison. Nevertheless,
the native run from `0` follows `0 → 2 → 3`, decoding to
`false → true → false`. The abstract run is `false → true → true`.
The second native step fails to preserve the interpretation of the reached
alias `2`. Exhaustively checking the two canonical inputs missed this error.

Layer passage has the same problem. A candidate lift that returns `true` only
for native label `1` agrees with the decoder on both canonical inputs. It
returns `false` for the reached alias `2`, losing information at the boundary.
Both failures are proved and reproduced by the required Lean checks. They
refute these weakened correspondence laws, not the author's native theory.

## Sufficient local laws

Let `C` be a type of abstract configurations and `N` a type of candidate native
representations. A `Representation C N` contains an encoder `e`, a partial
decoder `d`, and a proof that `d(e(c)) = some(c)` for every configuration `c`.
The tag `some` denotes successful decoding; `none` denotes failure to decode.

Let `A : C → C` be the abstract step and `T : N → N` a candidate concrete step.
The `Respects` predicate requires

\[
d(x)=\operatorname{some}(c)
\quad\Longrightarrow\quad
d(T(x))=\operatorname{some}(A(c)).
\]

This law applies to **every state that decodes**, including noncanonical states
reached during execution. Nothing is required of states outside the decoder's
domain. It is a sufficient law, stronger than restricting the condition to a
separately specified reachable invariant. Such a weaker invariant formulation
would also need proofs of initialization and closure under the concrete step.

`run_decodes` proves the correspondence after any finite number `k` of steps,
where `k` is a dimensionless natural-number count. Its induction applies the
local law to the output reached at each preceding step. `run_append` relates
a combined execution length to consecutive execution segments.

For a passage `L` to another representation with decoder `d'`, `LiftRespects`
requires `d(x) = some(c)` to imply `d'(L(x)) = some(c)`, again throughout the
decoder's domain. `lift_compose` proves that adjacent passages satisfying the
law can be composed. `lift_run_decodes` preserves a completed execution across
one such passage. If the lower and upper concrete steps both represent the
same abstract step, `run_lift_commutes` proves that running before or after the
passage gives the same decoded configuration. Equality of native encodings
is not required.

The candidate concrete step is one logical step in this interface. If the
kernel needs several forming steps to realize it, those steps must separately
be constructed and proved to implement the candidate operation. This theorem
does not assert one kernel application per instruction or justify a macro
operation merely because it has been named.

## Connection to complete derivation records and checking

The executable `Frame` retains five pieces of data:

- the original ground-calculus derivation record;
- its submitted claim;
- the remaining instruction program;
- the current premise stack or failed state;
- the full sequence of intermediate states.

`Frame.initial` compiles the retained record and supplies the empty initial
stack. `Frame.advance` executes the next existing machine instruction, records
the new state, and preserves the original record and claim. A finished frame
stays fixed. `run_frame` proves the exact resulting frame after all instructions,
including its canonical history and the original record and claim.

`Frame.accept` requires an empty remaining program, replays the retained
history against the original record and claim, and compares the retained final
state with the replay endpoint. `accept_run_initial` proves agreement with the
existing ground checker for every raw record and submitted claim. A separate
check rejects a tampered endpoint even when the recorded history is valid.

For **any supplied representation and concrete step satisfying the local
laws**, `represented_run` recovers that complete final frame after concrete
execution. `represented_check` proves that observing its acceptance returns
`some(check(record, claim))`. Rejection is retained as `some(false)`; it is not
replaced by failed decoding. `represented_composition_check` specializes this
result to the existing joined record, obtaining precisely the conjunction of
the two premise checks.

These conclusions preserve the data needed to check again after a valid layer
passage. The final Boolean observation remains a host calculation on decoded
data. The theorem does not provide a native acceptance formula, an arithmetic
truth predicate, or a proof that a kernel verifies its own soundness.

## Audit and remaining construction

The required layer audit includes 18 new dependency reports: 11 correspondence
and execution theorems, plus seven checks. It now requires 80 reports in total.
Twelve of the new reports have no axiom dependencies; six use only Lean's
propositional extensionality. The earlier report allowances remain unchanged.
The default library includes the module, and audit policy binds its exact bytes.

```console
python -u -m hypermath_foundations audit --root . --timeout 60 --output build/operational-audit.json
python -u -m pytest tests/test_audit.py tests/test_integrity_commands.py -vv -s --durations=10 --timeout=60
```

The source's whole-trajectory atom proposal motivates retaining the full frame.
The source descriptions inspected so far do not provide the encoder, decoder,
concrete execution, or layer-passage correspondence required here. Supplying
an actual native instance remains the next mathematical construction. The
existing fixed-unary-term, relation, and finite-successor obstructions still
apply to candidate instances. Ordinal interpretation and the intended
arithmetic completeness and novelty claims remain unresolved.

The subsequent [terminal-retention test](TERMINAL_RETENTION.md) evaluates one
actual model-specific candidate. In the existing two-successor-chain model,
primitive `f2f` cannot satisfy this total retained-frame correspondence for
any encoder and decoder. The obstruction uses three accepted records and
continued concrete execution after abstract completion. It leaves stopped
and guarded protocols, explicit layer information, and other carriers open.
