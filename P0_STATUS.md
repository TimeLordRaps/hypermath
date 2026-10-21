# P0: status, and why there is no P0 layer in this repository

Written 2026-09-21.

Every other foundational field in this family now carries either a P0 layer or a
written refusal. This repository is where the P0 idea was invented, and it has
had neither. This note is the refusal, with the measurement behind it.

## What P0 was meant to be

A layer below L0 — the "shadow ground" — whose objects are the field's own
oppositions: pairs that are similar and not identical, taken as generators
rather than as errors. A draft of it exists in an unpublished precursor tree
that forked from this repository at `819f685` on 2026-04-16. It declares a
`P0Form` kind, a `ParadoxHole` kind, a `pigeonhole(x, y)` primitive with the
precondition `x ~~ y AND NOT (x == y)`, a self-competing fixed point
`MetaParadox`, and a one-way gate `ax-no-return`.

It was never committed here, on any branch. It is untracked in the tree that
holds it. Nothing was removed from this repository to produce its absence.

## Why it is not being ported

Its separation of P0 from L0–L3 rests on one claim: that **period 1 is
arithmetically forbidden in the L-layers**, so a period-1 fixed point cannot
live in them and needs a layer of its own. The claim cites
`return-length-semigroup-is-omega`, which proves that return-lengths at `==`
form the numerical semigroup ⟨2,3⟩ = ℕ\\{1}.

Checked against this repository on 2026-09-21. The argument does not survive,
and the failures are independent of one another.

**1. The cited result is not here and never has been.** `semigroup` has zero
occurrences across every `.hm`, `.lean`, `.md` and `.py` file, and zero commits
on any branch. The word *period* appears nowhere in `L0_ground.hm` through
`L3_ordinatics.hm` or in any Lean module. This repository has no period concept
at all. The result lives only in the precursor's uncommitted working tree, where
its section — L3 "RETURN-PATH STRUCTURE AT ==" — has no counterpart here.

**2. Both of its generators are gone, and one is machine-refuted.**
`trinity-simulation-exists` (the 3-generator) has zero occurrences here.
`simulation-pair-exists-strong` (the 2-generator) likewise, and its content is
refuted: `lean4/FullAxiomModel.lean:528` proves
`nontrivial_simulation_claim_fails` inside a model satisfying all 44 clauses,
and `lean4/Hypermath/L3Ordinatics.lean:335` keeps the statement only as
`simulationPairExistsClaim : Prop`, recording that the admitted theorem is
withdrawn.

**3. Period 1 is not forbidden here. It is the easy case.** `trace-levels`
states a disjunction whose first case is `apply(x) == x` — a period-1 `==`
orbit, admitted by the very axiom the draft cites one step before its exclusion
claim. And `lean4/Hypermath/L3Ordinatics.lean:603`,
`driverCycleWitness_of_fixed_deriver`, is docstringed *"A fixed point makes the
certificate free"*, noting that this development's only inhabited certificate,
for most of its life, had `f2f deriver = deriver`. The structural asymmetry the
draft needs is not merely unsupported here. It is reversed.

**4. The exhaustion premise reverses the result it cites.** The draft says the
semigroup result characterises *finitely many* orbit classes. The result
concludes ℕ\\{1}, which is infinite — its own name says so, `-is-omega` — and it
never mentions orbit classes or finiteness. Its stated purpose is to be a
prerequisite for L4 chain-replacement. Worse, the supply of oppositions is
provably unbounded on this repository's own clauses:
`axDiffInRelationLanguage` gives `(f2f x ~~ ground) ∧ ¬(f2f x ≡ ground)` for
**every** `x`, so every form yields an opposition pair and nothing ever
exhausts. `docs/research/PROOF_AUDIT.md` (M6) says the same unprompted:
similarity return does not prove a finite universe, and the cited laws retain
infinitely many distinct forms.

**5. The entry witness does not instantiate as written.** The draft takes
`x := ground, y := apply(ground)`. `L1_relations.hm:94` proves the facts in the
other order — `apply(ground) ~~ ground` and `¬(apply(ground) == ground)`.
Flipping them needs symmetry of `~~`, which is a `sorry` at
`lean4/Hypermath/L1Relations.lean:58` and is independently refuted in
`Countermodels`, or symmetry of `==`, which `L3_ordinatics.hm:405` denies
outright. This one is repairable by rewriting the witness in the proved order;
the other four are not repairable by editing the draft.

## What a real P0 here would need

Not a port. A barrier argued from this field's own clauses, and the four
failures above say what it must supply:

1. **A genuine exclusion, not a guarantee.** `ax-box` gives
   `struct-orbits(apply(apply(x)), x)` — it guarantees return at two and forbids
   nothing at one. An exclusion needs a negation somewhere, and this repository
   currently has none about orbits.
2. **An exhaustion fact compatible with `axDiffInRelationLanguage`.** As long as
   every form yields an opposition pair, no chain of oppositions terminates, and
   a fixed point reached "when the supply is exhausted" does not exist.
3. **A witness in the order the repository proves.** See failure 5.
4. **Not to depend on `deriver-cycle-is-closed`.** `L3_ordinatics.hm:347`
   declares it FORM; `lean4/Hypermath/L1Relations.lean:555` keeps it as an
   unproved `driverCycleClaim` and records the admitted theorem as withdrawn,
   and `FullAxiomModel.lean:523` refutes it. `docs/research/PROOF_AUDIT.md` (M2)
   independently flags it. Anything built on it inherits that.

## What the sibling fields did instead

`hyperlogic` now carries a `P0_shadow_ground.hm` whose barrier is **not**
arithmetic: its degenerate structure satisfies all four L0 axioms and is
excluded by a Section VI *close*, so its P0 is the field read with its opaque
predicates left open. That barrier is field-local and checkable against
`collapsed_model`, which that repository already ships. It cites this field's
arithmetic barrier only to record that it does not hold.

The general lesson is worth keeping: **the P0 barrier appears to be
field-specific.** Three fields examined, three different candidate barriers, and
the one that tried to be arithmetic is the one that broke.

## Provenance

The draft and the precursor tree are intact and backed up. Nothing in this
repository was modified to produce this note, and nothing in the precursor was
modified at all.
