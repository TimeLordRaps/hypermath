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
axiom clause. The overall translation still has 20 admissions and 68 declared
assumptions: 30 source parameters and 38 logical clauses. The remaining
`selfDerivation` components have not all been proved.

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

Thus neither endpoint return nor the selected prefix establishes the advertised
`dSpansGround` theorem. This does not refute all later assumptions or every possible
completion of Hypermath. It identifies the precise missing implication that a
repair must address without assuming the desired conclusion.

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

The next arithmetic obligation is to connect a native finite continuation
`E(n) = f2f^n(ground)` and native `ordinalApply` to Ordinatics' finite ordinals.
It requires a justified arithmetic observation and a preservation theorem, not
an integer label added to a form. In particular, if the observation factors
through congruence, distinguishability of the required numerals must be proved.

Full self-representation, arithmetic soundness, the selected completeness
statement, and its effectiveness boundary remain open. See
[the governing research target](FRACTAL_COMPLETENESS.md).

## Reproduction and regression policy

Run the bounded audit as described in [the verification guide](../verification.md).
It builds the library and independently runs `Audit.lean`, `Countermodels.lean`,
and `TraceChecks.lean`. The expected strict mathematical gate still exits 2.

The policy binds the definition bodies, seven milestone statements, allowed
dependencies, generic trace source, and reporting/probe sources. Weakening `D`
to an always-true predicate, reinstating an admission, substituting the generic
trace, or skipping the new probes does not satisfy the updated policy. Report
consistency remains distinct from authentication; downstream consumers rerun
the checks against their pinned source and installed package.
