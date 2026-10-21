# Lean translation and proof audit

This directory is an incomplete Lean 4 translation of the native `.hm` files.
The pinned toolchain is Lean 4.14.0. A successful compilation accepts declarations
containing `sorry`; it does not establish their conclusions. Native `FORM` labels
in source comments record the `.hm` classification, not completed Lean proofs.

From this directory, run:

```console
python -u audit.py
```

The command prints source counts, performs a verbose build, reports the transitive
axiom dependencies of selected central declarations, checks independent finite
countermodels, finite traces, observations, and models of all logical clauses,
including the required finite-action countermodel. Each subprocess
has a 60-second timeout, output streams as
it arrives, and a silent subprocess receives a progress observation after 40 seconds.
Use `--timeout 90` to adjust the bound or `--lake PATH` to select the Lake executable.
`--inventory-only --details` lists every declared assumption without running Lean.

Exit meanings:

- `0`: the audited checks passed and no admitted proof was found in those surfaces.
- `1`: a build, tool, dependency report, or countermodel check failed.
- `2`: admitted theorem proofs remain; this is the current expected proof-gate result.
- `124`: a subprocess exceeded its time bound.

Even exit zero would not prove the consistency or arithmetic completeness of the
declared axioms, the soundness of the native language, or fidelity of every translation.

## Mechanical corrections and explicit assumptions

The original checkout failed to compile. Bodyless Lean `opaque` declarations
requested `Inhabited` defaults; they were replaced by explicit axiom declarations
for the source's uninterpreted type, function, and predicate parameters. This
exposes their assumed status. No admitted theorem was changed into a new axiom.

At that repair the original 29 parameter declarations became explicit
assumptions. Two further
source-backed projections, `pathStart` and `pathEnd`, express the actual endpoint
clause of `L3_ordinatics.hm:123–125`; the earlier translation confused path objects
with Forms and path length with the endpoint. No endpoint equations were invented.
The remaining 38 declarations were the translation's logical axiom clauses at
that point. Both numbers have since changed; the current inventory is the one
given below, and `tests/test_declared_counts.py` measures it.

The transfinite declarations were then moved out of this translation entirely.
The ordinal limit, successor and application, and the four laws over them, are
no longer stated here: they are fields of `Ordinatics.Transfinite`, a structure
parameterised over an abstract forming substrate and owned by the
[ordinatics](https://github.com/TimeLordRaps/ordinatics) repository. Hypermath
assumes one instance of it, `Hypermath.ordinatics`, and recovers every previous
name and type as a projection, so seven assumptions became one. The structure
carries a fifth field, `deriverAtLimit`, which declares that `deriver` is the
limit. L1 declares `deriver` as a Form and says nothing about where it sits;
that silence is what left every deriver question open, and the declaration is a
declaration, not a derivation. Its consequences are collected in
`Hypermath/L3Ordinatics.lean` §VIII.a.

The [finite-trace repair](../docs/research/FINITE_TRACES.md) subsequently replaces
the `D` parameter with its finite congruence-preserving witness definition.
It constructively proves `dIsReflexive` without changing its proposition-level API.
The subsequent [finite arithmetic repair](../docs/research/FINITE_ARITHMETIC.md)
defines the finite ground closure and refutes the universal ground-spanning
claim. There are now 26 source parameters, 40 logical axioms, and no admissions.
One of those axioms, `ordinatics`, is a structure carrying five clauses; the
models check 44 clauses, and the five closing clauses of L0 §VIII.b and L2 §II
are among them.
The latest three admissions were withdrawn after a full-clause countermodel
refuted their entailment. Their original propositions remain as
`ordinalZeroIdentityClaim`, `ordinalSuccAppliesClaim`, and
`pathLengthArithmeticClaim`; they were not proved or replaced by new axioms.

Missing external `ℕ`/iteration notation was replaced by Lean core `Nat` and
`Nat.repeat`. `orbitStructure` now uses the already declared `traceLevels` axiom
for its third pair, rather than applying symmetry to a proposition with the wrong
endpoints. The attempted reverse-filtration argument in
`plusAndAdditionallyAreDistinct` remains an explicit open proof premise, and is
now known to be independent of the 39 pre-closure clauses rather than unfinished:
`HypermathTransportCountermodel.no_incongruence_is_derivable` certifies every
clause in a model whose `Congruent` is total, so no two Forms are incongruent
there and the statement is false, while
`HypermathFullAxiomModel.full_clauses_with_distinct_operations` makes it true.

## What the independent countermodel establishes

`Countermodels.lean` imports only the generic, axiom-free `Hypermath.Trace` module
and declares no custom axiom or admitted proof. It constructs a Boolean model
of all 24 logical L0/L1 axiom clauses:
similarity and congruence are universal, simulation is equality, application maps
every element to `true`, and ground is `false`. In that model:

- non-simulation does not imply non-congruence;
- `Derives` is symmetric, contradicting the advertised directionality consequence;
- the promised simulation cycle is not a consequence of that axiom prefix.

A second model uses three forms, equality for congruence and simulation, and
application `0 ↦ 1`, `1 ↦ 2`, `2 ↦ 1`. It satisfies the same prefix but has no
congruence-preserving application edge. Its trace-defined `D` is equality, so
ground does not reach every form even though the deriver `1` returns after two
applications. The earlier unconstrained-`D` reflexivity probe has been replaced;
it would no longer model the current definition.

These are missing-implication witnesses for the stated prefix. They are not models
of all later L2/L3 assumptions and do not refute every possible completion of the
intended theory. Future changes to those axiom clauses require updating and reviewing
the countermodel correspondence.

`FullAxiomModel.lean` separately checks all 39 declared logical clauses in an
explicit two-chain interpretation. It excludes admitted theorems and stronger
prose glosses; its vacuous upper-bound implication and opaque path endpoints
make the remaining specification gaps visible. `ObservationChecks.lean` checks
that endpoint-only observations can lose path length while retained traces keep it.

`Hypermath/FiniteAction.lean` proves that finite addition and multiplication
respect equality of ground-orbit numeral representations without an injectivity
assumption. It also gives a surjective encoding of the witnessed finite orbit;
an explicit numeral-injectivity premise yields checked two-sided encode/decode
laws and implies the global compatibility condition. Its stronger exact-action
criterion concerns every starting Form: equal numeral
Forms must induce equal iterates on all of them. The existence direction uses
classical choice, is noncomputable, and remains conditional on that criterion.
Agreement through a relation requires the corresponding compatibility; the
generic necessity theorem takes symmetry and transitivity as explicit premises.

`FiniteActionCountermodel.lean` checks all 44 clauses on six Forms. Ground enters
a two-cycle while the limit lies in a separate three-cycle. Congruent is an
explicit equivalence relation. The first and third numeral Forms coincide,
yet their actions on the other cycle differ even modulo Congruent. Thus neither
an exact nor a congruence-valued action can agree with every finite iteration
on every Form in this model. The same model refutes the three retained
computation claims. Since the deriver was declared at the ordinal limit, the
limit's three-cycle refutes the `selfDerivation` target in this model instead of
satisfying it. The model therefore shows that the clause set alone entails
neither those arithmetic bridges nor the target; it no longer shows that the
target fails to entail the bridges, and no single model now witnesses that.
It does not encode the stronger unformalized native intent
that all Forms arise from ground, and does not refute finite-orbit addition or
multiplication.

**On Windows, a `lean/` subdirectory under the ordinatics build tree breaks this
build.** `lakefile.toml` requires `Ordinatics` from `../../ordinatics/lean4`, so
that package's `.lake/build/lib` becomes the first `LEAN_PATH` root here.
`Hypermath/GroundCode.lean` imports `Lean.Elab.Tactic.Omega`, and the filesystem
answers `Lean/` with a `lean/` directory, so a stray one in that root captures
the whole `Lean` namespace: the import resolves there, finds no object file, and
fails rather than falling through to the toolchain. The error reads

    object file '<ordinatics>/.lake/build/lib/Lean/Elab/Tactic/Omega.olean'
    of module Lean.Elab.Tactic.Omega does not exist

and the module does exist, in the toolchain. It surfaces at whichever file is
first to be recompiled rather than at `GroundCode`, so it reads as a failure of
something unrelated. Delete the directory in the ordinatics checkout; `lake
build` there does not recreate it.

**`lake build` does not compile this directory's top-level files.** The
library target is `Hypermath`, which is `Hypermath.lean` and `Hypermath/`. The
countermodels, the models, the reporter and the check files sit beside it and
are compiled only by name, which the audit does and `lake build` does not. A
green build is therefore not evidence about any of them, including evidence that
they are free of `sorry`; the audit's dependency check is what establishes that,
and it rejects `sorryAx` because it is not a reviewed builtin.

The audit binds 76 proved production milestone declarations and their reviewed
dependencies; that set is `PROVED_DECLARATIONS` in
`src/hypermath_foundations/_baseline.py`, and
`tests/test_declared_counts.py` fails if the prose and the baseline disagree.
It runs fourteen process checks: `lean_build`, `dependency_output`,
`countermodel`, `finite_trace`, `observation`, `full_model`, `finite_action`,
`target_at_limit`, `ground_syntax`, `ground_derivation`, `record_encoding`,
`record_machine`, `layered_derivation`, and `layer_consumption`.
A completed execution is those passing and nothing else.
It then derives two further checks from what they reported:
`assumption_policy` and `proof_admissibility`. Both sit in the report beside the
others and neither is in that conjunction, which is how a report can say its
execution completed while a check in it fails --- and `proof_admissibility` is
the one expected to, because the target names an unproved proposition.
`finite_action` runs the six-form model and its failure witnesses.

`Audit.lean` prints dependencies without exporting its report as library theorems.
In particular, `Hypermath.selfDerivation` currently depends on `sorryAx` through
its admitted components. The file does not remove, discharge, or hide those gaps.
