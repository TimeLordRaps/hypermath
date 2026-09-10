# Encoded composed records in free ground syntax

`lean4/Hypermath/GroundCode.lean` and `lean4/Hypermath/RecordEncoding.lean`
encode the [composed ground calculus](COMPOSED_GROUND_DERIVATIONS.md) as single
terms of the free `ground`/`apply` syntax. Every encoded record retains its rule
tree, arguments, formula annotations, and premises. An executable checker takes
two encoded data inputs: a candidate record and its claimed formula.

This is host serialization infrastructure with an explicit correspondence to
the free source syntax. It does not identify that syntax with semantic `Form`,
derive a native checker, or establish arithmetic completeness.

## Construction and recovery

1. A finite binary tree has prefix bits: `false` for a leaf, and `true` followed
   by the left and right encodings for a fork. The parser consumes the whole
   input, rejecting incomplete trees and trailing bits. Its recursion fuel is
   the actual input length, so termination is bounded by the finite input.
2. Bits are packed into a natural number: the empty list is zero; prepending
   `false` gives `2*n+1`, and prepending `true` gives `2*n+2`. `unpack_pack`
   proves recovery. The tree round trip follows from `parse_bits`.
3. Constructor tags distinguish terms, structural statements, formulas, and
   records within their declared grammars. Outer tags 8 and 9 distinguish
   records from formulas; these numbers are format tags, not truth ranks.
4. `recordCode` and `formulaCode` return packed natural numbers. `recordTerm`
   and `formulaTerm` denote the free ground terms having those depths.
   `decode_recordCode`, `decode_formulaCode`, and their term counterparts prove
   exact recovery. Wrong-sort decoding returns no result.

`recordCode_injective` and `recordTerm_injective` establish separation in these
host representations. `observe_recordCode` and `observe_recordTerm` preserve
every function of the retained record, including its complete formation tree.
The generic conclusion for native interpretation is conditional:
`semantic_record_recovery` requires a recovery map satisfying the displayed
faithfulness premise. The source clauses do not supply that premise; existing
finite-model collisions remain relevant.

## A faithful interpretation under all current clauses

`lean4/FullAxiomModel.lean` instantiates the encoding in the existing two-chain
model, whose forms are pairs `(n, branch)` with `n` a natural number and `branch`
a Boolean. Ground is `(0, false)`, and application increments `n` on the same
branch. All 38 logical clauses still hold, with no changes to their meanings
or the model operations.

The interpreted record value is `(recordCode(r), false)`, and the formula
value uses `formulaCode` on that same branch. Two interpretation theorems
identify these packed pairs with the actual interpretation of their free
ground terms. `interpreted_record_recovered` supplies exact recovery, and
`interpreted_observation_preserved` preserves every function of the record
after this interpretation. Values on the second branch are rejected.

`checkValues_values` proves that checking the interpreted values agrees with
the original composed checker. `checkValues_sound` proves that accepted
decoded conclusions hold in this model. `full_clauses_with_faithful_records`
combines the clause model, full record recovery, and checker correspondence.
This is a concrete compatibility witness. It does not imply that all models
of the clauses have faithful records; the six-form countermodel remains.

The existing congruence-preserving path relation has no positive edge in this
model. Distinct record and formula envelopes yield distinct values, so
`no_preserving_record_to_formula` rules out implementing their direct
record-to-conclusion transition as one of those paths here. This isolates a
remaining operational obligation even when record recovery succeeds. It does
not refute other native checking or ranked acceptance constructions.

The decoder and checker on these model values are still host functions. No
new source operation, computation law, or acceptance rule was added.

## Acceptance and finite reuse

`checkNumbers` decodes both arguments and runs the existing composed checker.
Decoding alone is insufficient for acceptance. `checkNumbers_codes` proves
agreement with that checker; `checkNumbers_sound` proves truth of the decoded
conclusion in any model satisfying the explicit composed-calculus premises.
This relative soundness theorem adds no native axiom and uses no arithmetic
truth oracle or external typed proof as an input.

`checkTerms_quote` establishes acceptance of the encoded quotation of every
typed derivation in the specified finite calculus. `joinCodes` reconstructs
and joins represented records; `joinCodes_recordCode` proves its exact behavior.
The original checker still checks both branches. Reusing a good branch cannot
conceal an invalid premise in the other branch.

These are external Lean definitions and proofs. The system does not yet derive
a next-rank acceptance formula using its own native rules. Encoding the data
consumed by a checker does not internalize the checker or its soundness proof.

## Resource cost

For a prefix bit list of length `b` and packed number `n`, `pack_bounds` proves
`2^b <= n+1` and `n+2 <= 2^(b+1)`. The free unary term therefore has exponentially
many `apply` nodes relative to the prefix length. This is not a compression
theorem. The packed interface avoids materializing that term, but still stores
the represented tree and all repeated subrecords; there is no sharing claim.

The executable separation example has 81 prefix bits and unary depth
`2820815200072616987372202`. The reporter checks its packed round trip,
acceptance, invalid-premise rejection, and join without constructing that unary
term. This is one executable example, not a performance benchmark. Neither
representation is claimed to handle unbounded input within finite resources.

## Audit boundary

The mandatory `record_encoding` process runs `lean4/RecordEncodingChecks.lean`.
Its 45 exact reports comprise seven without axiom dependencies, three using
only propositional extensionality (`propext`), 34 using propositional
extensionality and quotient soundness (`Quot.sound`), and one size-bound proof
also using classical choice (`Classical.choice`). No report uses an admission
or a native Hypermath parameter or clause. Classical choice occurs in the
resource-bound proof, not the executable decoder or checker.

The source and reporter bytes are bound by the audit policy. Missing reports,
concealed dependencies, admissions, changed bytes, or failed execution fail
the gate; native replay requires this process. Negative probes include wrong
sorts, unknown tags, wrong arity, malformed primitive records, incomplete tree
prefixes, trailing bits, incorrect claims, and a projection hiding a bad premise.

The separate full-model process now checks 26 exact dependency reports:
two without axioms, four using propositional extensionality, 15 also using
quotient soundness, and five additionally using classical choice. The five
include the full-clause proof and boundary results that use it or the existing
trace obstruction. The policy rejects omitted or extra dependencies as well
as admissions; it does not permit built-in assumptions indiscriminately.

The [native acceptance boundary](NATIVE_ACCEPTANCE.md) gives a further
counterexample in this faithful model. Every encoded raw record satisfies the
listed executive closure and ground-anchoring predicates, including a malformed
projection with a true, derivable conclusion. Closure of its representation
therefore does not certify that its claimed inference is valid.

The broader translation still has 67 declared assumptions and 16 admission
sites. Source-adequate native self-representation, internal acceptance, arithmetic
interpretation, transfinite coverage, and novelty remain open.
