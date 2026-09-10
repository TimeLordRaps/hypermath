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

1. Define typed representation, expansion, and closure evidence, including how
   predicates and derivations become forms.
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
