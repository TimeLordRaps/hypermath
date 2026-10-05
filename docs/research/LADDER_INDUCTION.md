# Transfinite form, ladder induction, rank order below ω^ω, and the counterexample rescue

This page records six standalone Lean 4 files, what each proves, what it only models on
a finite or toy carrier, and what stays open. It also records the maintainer's own
statements of the idea, verbatim and dated, so the checked mathematics can be read next to
the intent it responds to. Nothing here changes a `.hm` tag, adds an axiom, or modifies a
reviewed Lean file.

Labels used on this page.

- **FORM**: a Lean 4.14.0 kernel-checked theorem in this repository, or an exact computation
  whose statement is given. This is a stronger test than the source-native `.hm` closure
  label of the same name, which by itself does not establish proof checking.
- **FRAME**: a deferred dependency with a named missing piece.
- **OPEN**: a question or obligation with no result here.
- **HYPER**: an informal mapping to established mathematics, stated from memory and not
  checked in this repository.
- **UNKNOWN**: not established either way.

The existing boundary stays in force: source adequacy connecting the `.hm` files to the
Lean translation is UNKNOWN, and recursive arithmetic completeness is UNKNOWN
([`GOVERNANCE.md`](../../GOVERNANCE.md), [proof audit](PROOF_AUDIT.md)). Every result below
is relative to the finite or toy carrier it names.

## Where the files are and how they are checked

| File | Namespace | Role |
|---|---|---|
| [`TransfiniteForm.lean`](../../lean4/TransfiniteForm.lean) | `HypermathTransfinite` | form as a transfinite least fixed point |
| [`RecursionRescue.lean`](../../lean4/RecursionRescue.lean) | `HypermathRecursionRescue` | the finite countermodel also satisfies the three L3 computation claims |
| [`ConatTop.lean`](../../lean4/ConatTop.lean) | `HypermathTop` | the ladder and a self-containing top (conatural numbers) |
| [`SurrealFiltration.lean`](../../lean4/SurrealFiltration.lean) | `HypermathSurreal` | a toy normal-form model of the relation filtration |
| [`LadderInduction.lean`](../../lean4/LadderInduction.lean) | `HypermathLadder` | induction below ω^k from k nested ordinary inductions |
| [`RankOrder.lean`](../../lean4/RankOrder.lean) | `HypermathRank` | the omegas rank-order inside the tower below ω^ω |

None of the six declares an `axiom`, `opaque`, `sorry` or `admit`. They import no
Hypermath module, so they are independent of the 18-axiom kernel inventory in
`src/hypermath_foundations/_baseline.py`, which is unchanged. Each is run by
`lean4/audit.py` as its own bounded process (`transfinite_form`, `recursion_rescue`,
`conat_top`, `surreal_filtration`, `ladder_induction`, `rank_order`). The audit requires
the exact `#print axioms` records listed in `EXTENSION_PROBES` in
`src/hypermath_foundations/_reports.py` and the recorded SHA-256 of each file. Those
records are the only Lean-reported axiom dependencies:

- no axioms: `HypermathTransfinite.*`, `HypermathLadder.*`, the `rec_zero_identity` and
  `rec_succ_applies` theorems, `HypermathRank.lt_trichotomy` and `HypermathRank.lt_trans`;
- `propext` and `Quot.sound`: the remaining printed theorems of `RecursionRescue`,
  `ConatTop`, `SurrealFiltration` and `RankOrder`, except as follows;
- `propext` only: `HypermathRank.omega_cofinal`;
- `Classical.choice`, `propext`, `Quot.sound`: `HypermathTop.finite_or_top`, the one
  classical step in `ConatTop`.

Only the theorems named in `#print axioms` lines are audited for axiom use. The
files contain more theorems than are printed; they compile, but their individual axiom
dependencies are not bound by the audit.

These checks bind Lean acceptance of the stated propositions. They do not bind that a
proposition means what the maintainer's statement means.

## The maintainer's statements

The statements below are recorded as given, with dates. They are **USER-STATED**: they
state intent and are not evidence for any claim on this page.

**Purpose of the program (USER-STATED, 2026-10-04).**

> hypermath is the underlying complete structure that contains itself and allows the other hypers to exist, and ordinatics, it all stems from me doubting godelian completeness of arithmetic and designing transfinite arithmetic ordinatics so that I could define a self-closing system which is complete and explains arithmetic with yes a system outside of arithmetic ordinatics but ordinatics contains its own design within itself from hypermaths self-closure. So if we can derive arithmetic from transfinite representations like work backwards through the condition of being beyond infinite then we can complete arithmetic so to speak

**Form and the `.hm` files (USER-STATED, 2026-10-04).**

> **USER-STATED, 2026-10-04.** "A form is a reachable closed derivation chain from the ground L0", and the purpose of `.hm` files is that "they are translatable to any language".

**Towers, collapse and the average fold.**

> **Owner's statements (USER-STATED, 2026-10-04).** A finite looping operation like □ "can be applied in place in infinitum", so the □-tower should give cyclic proofs of non-contradiction and compress transfinite representations "along compressible dimensions". The operations are "always identity", like 1×1×1×1, and ω-towers can be decomposed "into rank ordered omegas" with the smallest at the bottom. Infinities can be treated as pseudounits, "equatable in their continuation aspect, sort of like they are vectors". Decision: **ℕ is definable only at `==`.** Open question raised: the average as "a fold that is fractally occurring up the tower".

**The extrapolatable top.**

> **Owner's statement (USER-STATED, 2026-10-04).** "The highest top is the extrapolatable top that would have to be the top given the descriptions of all of the runs below where you currently are." From a rung "you cant know how high you are or what determines that this run is this rung, you just know that the ordinals below you are smaller infinities than you and the ones above you are larger". Sometimes, from yourself and the neighbouring infinities, "can you determine a boundedness of your tower otherwise its undecidable".

**The request for ladder induction.**

> **Owner's statements (USER-STATED, 2026-10-04).** □ is "the ground while simultaneously being our first ordinal and the top ordinal and all rungs up the ordinal"; the omegas must be rank ordered; ω^ω is "equivalent to maximum omega^minimum omega"; and "we need to invent transfinite induction proofs" that "work backwards through infinities into natural and reals".

**Ranking the omegas.**

> **Owner's statements (USER-STATED, 2026-10-04).** Ordinals "have a real component and an imaginary component, both working backwards reach either normals imaginary or normals normal"; imaginary ordinals work backwards to form the reals, ω^ω forms "a third form like a primal backwards down the transfinites into irrational and surreals", with imaginary ω^ω for surreals, real ω^ω for irrationals, and normal ω^ω backwards "might be unsolvable ... harder to prove because of discrete omega^k jumps". Requirement: "prove that omegas naturally rank order in the tower of omega^omega".

**The classification of ω^ω representations.**

> **Owner's statements (USER-STATED, 2026-10-04), verbatim.**
>
> exponent axis of normal representations of omega^omega is unsolvable due to discontinuities
> exponent axis of real representations of omega^omega is surreal omega
> exponent axis of irrational representations of omega^omega is irrational omega
> exponent axis of imaginary normal representations of omega^omega is normal omega (I think we can prove finite imaginary exponents of omega^omega solvability into a normal pre omega^omega class)
> exponent of imaginary rational is rational omega
> exponent of imaginary irrational is primal omega (infers new math about primes through prime localized ordinals)
> exponent of surreal omega^omega is real omega^omega
> exponent of imaginary surreal omega^omega is surreal omega^omega * imaginary omega^omega think like the complex numbers but with multiplication between the surreal component and the imaginary component so omega^omega is separatable in this regime and may be composable though a dont know if it works bidirectionally like that, we would need to prove a bijection which is difficult because here the imaginary omega^omega is the class of normal, rational, and irrational
>
> coefficient of normal representations of omega^omega is normal finite
> coefficient of real rational representations of omega^omega is rational finite
> coefficient of real irrational representations of omega^omega is irrational finite
> coefficient of imaginary normal representations of omega^omega is imaginary finite
> coefficient of imaginary irrational omega^omega is irrational omega^omega
> coefficient of surreal omega^omega is surreal omega
> coefficient of imaginary surreal omega^omega is the additive equivalent of the multiplicative complex number analog of the exponent of this class ie surreal omega^omega + imaginary omega^omega allowing you to fully separate this class into seperable components which then allow working like I said backwards to find I believe all classes and having the closure unsolvability of the normal omega^omega is the base meta-induction which allows a full proof of the existence of omega and finites from omega^omega class

None of the classification statements is formalized in this repository. Section
"What is open" returns to them.

## 1. Form as a transfinite least fixed point

FORM, in `TransfiniteForm.lean`.

1. `finite_reachability_contradicts_limit`: for any carrier `F` with a point `ground`, a
   map `f`, a limit point `L` and a relation `Sim` that is reflexive at `L`, it is
   contradictory to have both "every element is `f^n ground` for some `n`" and "no
   `f^n ground` is `Sim`-related to `L`". The Lean translation's `axLimitNotFinite` has
   that shape. This says one carrier cannot have both properties. It does not by itself
   settle which reading of "reachable" the native `.hm` text intends.
2. A concrete carrier `Form` (Brouwer-style trees with constructors `ground`, `f2f` and an
   ω-limit `lim`) has `minimality` (the recursor), an injective `f2f` that never returns to
   `ground`, a limit outside every finite stage, and `ordinalApply` defined by recursion
   on its first argument.
3. On that carrier `ordinal_zero_identity`, `ordinal_succ_applies` and
   `path_length_arithmetic` hold with equality, which is stronger than the source's
   `Congruent`. `omega_plus_one` is the equation
   `ordinalApply (f2f ground) ordinalLimit = f2f ordinalLimit`.

Limits. `lim` takes an arbitrary sequence and sequences are not identified up to
extensionality, so this carrier is a syntactic model, not a quotient that matches ordinal
arithmetic. It does not interpret `Similar`, `Congruent` or `Simulation`. That it satisfies
every clause of the 38-clause `FullAxioms` is not attempted (OPEN). The three equalities
hold because `ordinalApply` was defined by the recursion equations; that is the point of
the next section, not independent support for the claims.

## 2. Counterexample rescue

The repository's [`FiniteActionCountermodel.lean`](../../lean4/FiniteActionCountermodel.lean)
gives a six-element model of all 38 logical clauses in which the three L3 derives
`ordinal-zero-identity`, `ordinal-succ-applies` and `path-length-arithmetic`
([`L3_ordinatics.hm`](../../L3_ordinatics.hm), lines 138, 149 and 158) fail, because there
`ordinalApply` is a constant and the clauses give the opaque `ordinal-apply` no
computation laws. Those three derives keep their `FORM` tags in the `.hm` file. A drift
report (`hypermath-foundations translate --drift lean4 ...`) flags exactly those three as
tagged `FORM` while the repository's own Lean refutes them as consequences of the clauses.
See the [translator page](HM_TRANSLATOR.md).

`RecursionRescue.lean` is self-contained. It reproduces that file's model and its
`full_axioms_hold` proof verbatim, omits the constant `ordinalApply` and the trace-defined
`D` (neither appears in `FullAxioms`), and adds a defined table `ordinalApplyRec`. The table was found
by exhaustive search over the finite model. It proves, with `propext` and `Quot.sound` only:

- `clauses_and_computation_laws_consistent`: all 38 clauses and the three computation
  claims hold together in one model, with the claims stated up to the model's `Congruent`.

What this shows (FORM): the finite countermodel refutes "the three claims follow from the
38 clauses as formalized". It does not refute "the claims are consistent with the clauses".
In this finite model, adding recursion equations to the clauses is consistent.

What it does not show. The table is a witness chosen so the equations hold; it is not
evidence that it is the intended meaning of ordinal application. A six-element model says
nothing about the infinite or transfinite case. The 38 Lean clauses only approximate the
native `.hm` semantics, and source adequacy is UNKNOWN. The copy of the model in
`RecursionRescue.lean` is not mechanically tied to `FiniteActionCountermodel.lean`; if
that file changes, the copy must be re-synchronised by hand.

**Owner decision pending.** The three derives remain tagged `FORM` in the `.hm` files, and
this change leaves them so. Two honest ways to resolve the mismatch exist, and choosing is
the maintainer's call: add recursion equations for `ordinal-apply` to L3 (which would
change the reviewed assumption surface and requires the review described in
[`AGENTS.md`](../../AGENTS.md)), or retag the three derives. Until then the status of
those three claims, relative to the Lean clauses, is: not derivable, and consistent with
the clauses once the equations are added in the finite model.

## 3. The extrapolatable top

FORM, in `ConatTop.lean`. Conatural numbers are represented as decreasing Boolean streams
(Lean core only, no Mathlib). The file proves `succ_top` (`□ top = top`), an injective
embedding `rung` of the natural-number ladder that commutes with `□`, that `□` never lands
on `ground`, `top_not_rung`, and `extrapolated_top_unique`: anything above every rung is
the top. It also proves that a decision procedure for "is `x` the top?" would decide
whether an arbitrary Boolean stream is all false (the limited principle of omniscience).
`finite_or_top` (every element is a rung or the top) uses `Classical.choice`.

Reading. This realizes, on one carrier, the idea that the top is determined by the
descriptions of the runs below it. It is a statement about conatural numbers, not about
the `Form` of the `.hm` files. Whether hypermath's `Form` has such a top is OPEN. The
connection to the maintainer's statement is interpretive.

## 4. A toy model of the relation filtration

FORM, in `SurrealFiltration.lean`. The carrier is finite sums of `c · ω^e` with integer
exponent `e` and non-zero integer coefficient `c`; this is a fragment of normal form,
enough to separate orders of infinity. With `==` equality, `=~` same leading term and
`~~` same leading exponent, the file proves the filtration clauses
`filtration_sim_cong` and `filtration_cong_sim`, `trace_levels`, and for doubling as `□`:
`ax_diff`, injectivity, that `□` is the identity at `~~` and not at `==`, that the `□`
tower is a single point at `~~` (`similar_invariants_cannot_count`) and injective at `==`
(`tower_injective_at_simulation`), and that distinct rungs never meet at `~~`.

This realizes the maintainer's decision recorded above that the natural numbers are
definable only at `==`, in this toy. Not shown: every `FullAxioms` clause in this model;
rational or real coefficients; the fold at limit stages. The numerical fold check that
accompanied the model was not migrated.

## 5. Ladder induction and rank order below ω^ω

FORM, in `LadderInduction.lean` and `RankOrder.lean`. `Tower k` is a vector of `k` natural
coefficients, leading rank first, with the lexicographic order `lt`. The intended reading
is the ordinals below ω^k in Cantor normal form; that reading is not itself formalized
(there is no ordinal library here), so what is proved is stated for the lexicographic order.

- `ladder_induction`: for every `k`, if a property holds of `x` whenever it holds of
  everything below `x`, it holds of every element of `Tower k`. The proof nests one
  ordinary strong induction per rank, with `k` as the outer induction; it uses no
  `WellFounded` or `Acc` library and no axioms.
- `no_infinite_descent`: no infinite strictly descending sequence in any `Tower k`.
- `omega_mult_ladder` and `band_below_omega_squared`: ω < ω·2 < ω·3 < ... below ω² in `Tower 2`.
- `descent_terminates`: a two-component rewrite game, in which the second component may be
  reset to any value when the first drops, terminates for every adversary. No single natural
  number measure bounds it. This is a termination proof, not a bound on run length.
- `RankOrder.lean`: `lt` is irreflexive, transitive and trichotomous on every `Tower k`
  (a strict total order); `omegaPow_strictMono` (ω^j < ω^j' for j < j'); `band_upper` and
  `band_lower` (an element lies below ω^k exactly when its rank-k coefficient is zero, so
  every element lies in exactly one band [ω^k, ω^(k+1))); `lift_mono` and `lift_omegaPow`
  (the embedding of `Tower k` into `Tower (k+1)` preserves order and fixes the omega
  powers); and `omega_cofinal` (every element is below some omega power, so ω^ω is the
  supremum of the omegas and none of them).

Limits. These are Lean theorems about lexicographic order on finite vectors of natural
numbers, proved in a foundation far stronger than the systems whose strength is usually
discussed with ω^ω. They carry no proof-theoretic claim about which arithmetic proves
induction up to ω^ω. Towers of towers (ω^ω^ω and up to ε₀) are not covered; there the outer
induction on `k` would itself have to be nested, which is where Gentzen's wall sits (OPEN).
The statement `ladder_induction` is uniform in `k`; whether that uniformity is the induction
the maintainer's request calls for is interpretive.

HYPER, from memory and unchecked here: the Hardy and fundamental-sequence descents from
ω^ω (ω^ω[n] = ω^n and so on down to the naturals) terminate by exactly this induction while
their length grows without bound, and termination of the analogous descent for towers of
towers is not provable in Peano arithmetic. The Python computations behind those
numbers were not migrated.

## What is proved, what is only a finite model, what is open

| Item | Status | Carrier or scope |
|---|---|---|
| Finite reachability and a non-finite limit cannot hold together | FORM | any carrier, with `Sim` reflexive at the limit |
| `minimality`, injective `f2f`, limit outside finite stages, three L3 claims by equality | FORM | the tree carrier `Form`, with `ordinalApply` defined by recursion |
| All 38 clauses and the three L3 claims together | FORM | one six-element finite model only |
| Same, in the tree carrier | OPEN | not attempted |
| Recursion equations for `ordinal-apply` added to L3, or the three derives retagged | OPEN | maintainer decision; neither is done here |
| Top determined from below; testing for the top implies LPO | FORM | conatural numbers only |
| Hypermath's `Form` has such a top | OPEN | |
| `==` / `=~` / `~~` filtration clauses, `□` as doubling, counting only at `==` | FORM | toy integer-exponent carrier |
| Same carrier satisfies every `FullAxioms` clause | OPEN | not attempted |
| Ladder induction, no infinite descent, rewrite-game termination | FORM | lexicographic order on `Tower k` |
| Strict total order, bands, cofinality of the omegas | FORM | `Tower k`, every `k` |
| Identification of `Tower k` with ordinals below ω^k | OPEN | not formalized |
| Towers of towers (ε₀) | OPEN | |
| Real and surreal direction from the ω^ω classification | OPEN | no formalization |
| The classification statements about exponent and coefficient axes | UNKNOWN | recorded only; none is proved or refuted here |
| Source adequacy of `.hm` against Lean | UNKNOWN | unchanged |
| Recursive arithmetic completeness | UNKNOWN | unchanged |

Falsification conditions. A change to any of the six files that makes an audited theorem
depend on a different axiom set, or on `sorryAx`, fails the audit. A clause of `FullAxioms`
that fails in a model with the recorded `ordinalApplyRec` table would be a counterexample to
the finite result only if it changed the model of `FiniteActionCountermodel.lean`, which the
audit pins; the finite result is therefore exact for that model and silent about any other.
