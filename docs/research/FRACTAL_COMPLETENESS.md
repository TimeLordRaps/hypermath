# Fractal meta-representation and Gödelian completeness

The governing research objective is **Gödelian complete ordinal arithmetic
through fractal meta-representations**, grounded in the proposed
self-derivational Hypermath structure. It is not replaced here by an external
hierarchy of truth predicates. This document states the formal work needed;
it does not announce a completeness result.

## Mechanism and missing bridge

Chapter 24 describes a closed derivation becoming an atomic input for another
application of the same grammar, retaining its trajectory. The proposed
`wcf` operation, **with form**, replaces a verified form with a reusable term.
It is a symbolic operation with no physical units. Term/operator
self-representation and the casting/link specifications add context for how
the mechanism itself could become an input. See the [source map](SOURCE_MAP.md).

The current L0 self-census applies predicates to names of predicates, and L2
uses entries of a proposition-valued derivation matrix as paths. The missing
construction is explicit typed reification: a way to represent those objects
as forms and recover the evidence needed to use them. That construction is
directly relevant to fractal meta-representation, rather than a formatting
detail of a future checker.

The [finite ground-syntax construction](GROUND_SYNTAX.md) now represents
instances of the four primitive ground rules as terms in the source's
`ground`/`apply` grammar. It supplies a record-only decoder and conclusion
checker, a source-relative soundness proof, and a concrete finite reuse
operation. This is a positive fragment of the representation task. It does
not yet represent arbitrary derivations or derive the checker's acceptance
claim internally. A full-clause countermodel also proves why interpreting
those syntax records as semantic Forms can lose their rule identities.

An initial proposed representation is a derivation graph with references to
closed subderivations and their closure evidence. References may be reused
recursively by the same constructors. This is a formalization candidate,
not an assertion that finite graphs exhaust the user's intended objects.
If cycles denote infinite unfoldings, their admissibility and global validity
conditions must be supplied.

## A precise preservation obligation

Let `d` be a derivation, `e(d)` its compressed representation, and `q` an admitted
arithmetic or meta-representation observation. Let `b(d,q)` denote the binary
outcome that the intended semantics requires. An exact observation decoder
exists on the image of `e` precisely when

\[
e(d)=e(d')\;\Longrightarrow\;
\forall q\; b(d,q)=b(d',q).
\]

Proof: a decoder must give the same answer to equal inputs. Conversely, under
this condition, define its answer as the unique common outcome of all
derivations represented by that input. This establishes existence, not an
algorithm or a derivation from the ground axioms. The observation class must
include the contexts in which the representation is to be reused.

Literal path recovery is sufficient but not necessary. Similarity of a
round trip suffices only after proving that the required observations are
invariant under that similarity. A pointer to a retained derivation may
preserve information; the retained store is part of the representation cost.

The criterion is now checked in `lean4/Hypermath/Observation.lean` as
`compatible_iff_decoder`, including uniqueness on the encoding's actual image.
The existence construction uses Lean's classical choice; it is not an executable
native decoder. Its two choice-dependent reports are distinguished from the
22 observation reports with no axiom dependencies.

There is also a constructive sufficient condition for recursive reuse. For an
encoding `e` and every permitted reuse operation `c`, require

\[
e(d)=e(d')\;\Longrightarrow\;e(c(d))=e(c(d')).
\]

Together with the base observation criterion, this preserves the observations
after every finite sequence of those operations. The checked
`reuse_preserves_observations` proves this by induction on the sequence.
It does not cover transfinite limits or silently supply the premise for a
native operation. A concrete two-bit example separates the requirements:
retaining the first bit supports arbitrary first-bit flips, but a swap exposes
the discarded second bit and breaks observation exactness. Thus a successful
single-stage decoder alone cannot certify fractal reuse.

For native finite numeral Forms there is a further exact boundary.
`finiteNumeralEqualityExact_iff_injective` proves that preserving every standard
question "does this input numeral equal k?" is equivalent to injectivity of
`E(n) = f2f^n(ground)`. The existing six-form model has `E(1) = E(3)` and now
formally refutes a decoder for these queries. Addition and multiplication
descending to represented values does not ensure preservation of even these
atomic arithmetic truths about the original natural numbers. A candidate must
derive injectivity for this encoding or supply a different, adequately proved
representation; the result does not rule out all native representations.

## Completeness must have a stated meaning

The following are different claims:

- Every arithmetic sentence or its negation is derivable, with soundness
  ensuring the derived choice is correct.
- Every arithmetic truth is covered by the entire mathematical structure,
  possibly through infinitary or non-effective validity conditions.
- The system closes under representation of its own derivation machinery.

The project must specify the intended meaning and prove any bridge between
these claims. A candidate classical arithmetic target, conditional on that
interpretation of completeness, is

\[
\mathbb N\models\varphi
\quad\Longleftrightarrow\quad
\exists m\;\operatorname{Valid}(m,\iota(\varphi)),
\]

where `iota` is a specified arithmetic translation and `Valid` is defined by
the actual inference/closure rules, not by assuming the truth on the left.
Soundness and completeness are separate directions. The translation must
preserve operations, negation, and quantification.

If the translation is computable, certificates are effectively enumerable,
and acceptance is uniformly computably recognizable, sound coverage of every
sentence or its negation would decide arithmetic truth by searching both
certificate sets in parallel. Thus full classical coverage cannot have all
those effective properties. Finite descriptions of infinite objects do not
make their global validity effectively recognizable. This boundary must be
identified for the actual construction; it is not a reason to substitute
another completeness definition.

## Novelty comparisons

[Pakhomov, Rathjen, and Rossegger](https://arxiv.org/html/2405.09275v2#S6),
Corollary 23, establish arithmetic completeness across suitable full-uniform-
reflection progressions with ordinal-notation values below `omega^omega`.
The presentation, not just ordinal value, matters. This is a direct comparison
for retained derivation information.

[Brotherston and Simpson](https://www.pure.ed.ac.uk/ws/files/12304236/bs_journal.pdf)
study recursive infinite and finite cyclic proofs with global trace conditions.
[Das](https://lmcs.episciences.org/6008/pdf) compares the strength and proof sizes
of cyclic arithmetic and Peano arithmetic. These give concrete prior mechanisms
for recursively represented derivations. A novel theorem must distinguish the
proposed representation, its preservation properties, its mathematical
strength, or a quantified resource bound. This is a bounded literature
comparison, not an exhaustive novelty assessment.

## Next proof sequence

The [finite-trace milestone](FINITE_TRACES.md) supplies witnessed `D` entries,
typed reuse, and preservation of their recorded edges. It does not yet represent
those witnesses as native forms or interpret arithmetic through them. Its new
countermodel shows why an endpoint return cannot discharge per-step preservation.
The [finite arithmetic bridge](FINITE_ARITHMETIC.md) adds least finite closure
and Form-valued length observations. Its refutation of universal ground-spanning
and endpoint-decoding obstruction constrain the next native representation;
the full arithmetic objective remains open.

Finite addition and multiplication respect equal ground-orbit numeral
representations without an injectivity assumption. Every witnessed finite-orbit
Form has a natural-number representative, and an explicit numeral-injectivity
premise yields a two-sided correspondence and representative independence on
every starting Form. The exact-action criterion is now characterized in Lean,
with classical choice used for the
conditional existence direction. A six-form interpretation satisfies all 38
declared logical clauses, with Congruent an equivalence relation, but refutes
both exact and congruence-valued uniform finite actions. This concerns the
declared clauses; it does not encode the stronger native generativity intent.

The proposed `ordinalZeroIdentity`, `ordinalSuccApplies`, and
`pathLengthArithmetic` statements are retained as `Claim` definitions after
the model refuted their entailment. Their withdrawal from the admitted theorem
list does not prove them or settle the intended ordinal interpretation.
The same model now proves a sharper separation: all 38 declared logical clauses
and the exact current `selfDerivation` target hold together while the global
finite-action criterion and all three ordinal computation claims fail. Thus the
current self-derivation proposition is not itself an arithmetic interpretation
theorem. A positive result needs the typed reification, transfinite-path, and
semantic preservation premises listed below.
Fractal reuse must retain or justify the observations needed for its actual
domain of application; neither this obstruction nor the finite-orbit result
establishes a completeness verdict.

The [composed ground calculus](COMPOSED_GROUND_DERIVATIONS.md) now supplies
typed finite derivations and structured records for primitive rules, predicate
closes, conjunction, and projections. Its record-only checker is sound under
the explicit source premises, accepts every derivation of that calculus, and
preserves the complete rule tree through typed reconstruction. This is a
constructive representation result at the host level. The
[record encoding](RECORD_ENCODING.md) now supplies free ground-term codes for
records and formulas, exact recovery, and checking of packed numerical inputs.
The existing two-chain model of all 38 clauses now supplies a concrete faithful
interpretation, with full recovery and checker correspondence. Faithfulness
for the intended native realization, internal representation of the checker,
and ranked acceptance are still open. The unary expansion is
exponential in the prefix length; no compression result is claimed.

The [native acceptance boundary](NATIVE_ACCEPTANCE.md) now separates executive
closure from record checking in that faithful model. A valid primitive record
and an invalid projection have the same true conclusion; both representations
satisfy syntax, substance, semantics, form closure, and ground anchoring. The
checker distinguishes their inference trees. Replacing acceptance with those
closure conditions or the conclusion alone therefore fails on an explicit
counterexample. This identifies a missing correspondence theorem, not a
contradiction in the source clauses or a refutation of all native mechanisms.

1. Establish source adequacy for a faithful interpretation of the typed
   composed-record codes, and internally represent their checking operations.
   Derive ranked acceptance through explicit source rules that check every
   premise and bind the exact record to its claimed conclusion.
2. Resolve the current relation, composition, and finite/transfinite path
   conflicts documented in the audit.
3. Prove preservation of the declared observations under compression and reuse.
4. Prove the arithmetic interpretation and soundness of accepted closure.
5. Prove the selected completeness statement and locate its effectiveness
   boundary. Do not place coverage into the definition of validity.
6. Establish a comparison theorem against a named existing construction.

The Python Ordinatics package presently supplies finite, exact computational
components. Neither it nor this repository's unresolved Lean translation
currently realizes the proposed full completeness mechanism.
