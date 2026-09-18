# Constructive finite derivation witnesses

This repair closes one concrete gap in the Lean translation: `D` previously was
an unconstrained predicate, while `L1_relations.hm` defines its entries by finite
traces preserving congruence or a stronger relation. `D` is now defined by such
witnesses. This is a partial correspondence with that source clause, not a proof
of the adequacy of the entire native language.

## Construction

`Trace Step x y` records a finite sequence from `x` to `y`, carrying evidence for
every `Step` edge. It has a zero-step constructor and a constructor that prepends
one justified edge. Intermediate endpoints must match by type. Its natural-number
length is computed from the constructors, rather than attached as an asserted
label. Length counts edges and has no physical unit.

The relation-specific construction in `Hypermath/L1Relations.lean` is:

```lean
def DStep (x y : Form) : Prop := y = f2f x ∧ Congruent y x
abbrev DEntry (x y : Form) := Trace DStep x y
def D (x y : Form) : Prop := Nonempty (DEntry x y)
```

`selfRead x` supplies a zero-step witness. `dEntryStep x h` needs actual evidence
`h : Congruent (f2f x) x`; similarity alone does not provide it. Composition
preserves every edge and requires the shared endpoint. The existing `reflexion`
proposition remains available, with `reflexionTrace` exposing its witness.

The checked finite statements include:

- self-read and one-step lengths are respectively zero and one;
- the endpoint of a witness `p : DEntry x y` is exactly
  `Nat.repeat f2f p.length x = y`;
- `D` is reflexive and transitive;
- self-read is a two-sided composition identity;
- if no congruent application edge exists, every witness has length zero and
  equal endpoints.

These seven production theorem reports depend only on the existing parameters
`Form`, `f2f`, and `Congruent`. They do not depend on an admitted proof or a logical
axiom clause. The subsequent [finite arithmetic repair](FINITE_ARITHMETIC.md)
closes the finite ground predicate and refutes universal ground-spanning.
The overall translation now has 11 admissions and 67 declared assumptions:
29 source parameters and 38 logical clauses. The remaining `selfDerivation`
target is unproved. Admissions for ordinal computation, nontrivial simulation,
and the deriver cycle were withdrawn after full-clause counterexamples; their
statements remain named claims, not completed proofs. See the
[cycle boundary](CYCLE_BOUNDARY.md) for the exact remaining conjunct.

## Reuse and preservation

`TraceExpr` has existing-trace atoms, self-read, and typed sequencing. Expansion
recovers an evidenced trace. Composition, vertex mapping, and expression expansion
preserve computed length and the recorded sequence of edge endpoints as specified
by their respective theorems. Mapping additionally requires a function that
transports each edge's evidence.

The 17 generic construction theorems and 11 concrete checks in `TraceChecks.lean`
have no axiom dependencies. The checks include composition, mapping, repeated use
of a retained trace, absent-edge rejection, and the impossibility of a return
under strictly increasing natural-number steps.

This is an initial finite mechanism for evidence-preserving reuse. An atom keeps
its trace; there is no compression ratio or reduced storage claim. `TraceExpr`
is not yet a native `Form`, a representation of its own checking procedure, or
a finite encoding of an accepted infinite derivation.

## The counterexample that survives the repair

The obsolete example choosing `D` false everywhere has been removed, because it
does not interpret the new definition. Its replacement uses three forms, ground
`0`, application `0 ↦ 1`, `1 ↦ 2`, `2 ↦ 1`, universal similarity, and equality
for congruence and simulation. `Derives` uses its specified finite endpoint
reachability interpretation.

Lean checks all 24 selected ground/relation axiom clauses in this model. The
deriver `1` returns exactly after two applications, but neither step preserves
congruence. Consequently every `DEntry` has zero length, and `D 0 1` fails.

Thus neither endpoint return nor the selected prefix establishes universal
ground-spanning. The [finite arithmetic repair](FINITE_ARITHMETIC.md) goes
further: the L3 limit axiom implies its negation, so the admitted `dSpansGround`
theorem has been withdrawn and the exact proposition retained as a claim.

## Remaining correspondence obligations

Lean's inductive types, natural numbers, equality, and logic are host proof
infrastructure. Their derivation from the native ground operation is not supplied
by these definitions. `Form`, `f2f`, and `Congruent` remain abstract parameters.

The opaque L2 `DerivationPath` also carries stronger intended requirements:
nondecreasing relation annotations, steps allowing endpoints merely similar to
an application, and a path-length operation valued in `Form`. The finite trace's
edge count is not silently equated with those path lengths or source quanta.
Its congruence floor does not prove congruent-index substitution, nor endpoint
congruence without additional relation laws. A bridge must state these differences.

The finite continuation `E(n) = f2f^n(ground)` now respects addition on its
represented ground-orbit values without assuming numeral injectivity.
Extending these values to an exact action on every Form requires the separate
compatibility condition in [finite arithmetic](FINITE_ARITHMETIC.md).
A six-form model satisfies all 38 current logical clauses, with Congruent an
equivalence relation, yet admits neither an exact nor a congruence-valued
action agreeing with all finite iteration counts on every Form. It does not
formalize the stronger native generativity intent.

Agreement with `ordinalApply`, opaque `pathLength`, and Ordinatics' ordinal
values remains a correspondence obligation. The former admitted
`ordinalZeroIdentity`, `ordinalSuccApplies`, and `pathLengthArithmetic` are now
retained as proposition definitions with a `Claim` suffix. No observation may
silently discard the path evidence or assume the remaining numeral distinctions.

Full self-representation, arithmetic soundness, the selected completeness
statement, and its effectiveness boundary remain open. See
[the governing research target](FRACTAL_COMPLETENESS.md).

## Reproduction and regression policy

Run the bounded audit as described in [the verification guide](../verification.md).
It builds the library and independently runs `Audit.lean`, `Countermodels.lean`,
`TraceChecks.lean`, `ObservationChecks.lean`, `FullAxiomModel.lean`, and
`FiniteActionCountermodel.lean` (the required `finite_action` process). The
expected strict mathematical gate still exits 2.

The policy binds the definition bodies, milestone statements, exact per-theorem
dependencies, generic trace source, and reporting/probe sources. Weakening `D`
to an always-true predicate, reinstating an admission, substituting the generic
trace, or skipping the new probes does not satisfy the updated policy. Report
consistency remains distinct from authentication; downstream consumers rerun
the checks against their pinned source and installed package.
