# From unary forming to a compositional layer

The author's clarification places sequencing at layer `n+1`, relative to a
self-derivation kernel at layer `n`. Self-derivation supplies verification
geometry; it is not thereby identified with the sequencing identity. The next
layer must construct an operation that combines the representations it uses.
The result below identifies one precise limitation of the starting signature.
It does not replace the author's proposed layer construction with that signature.

## The expression language examined

[Ground Section I](../../L0_ground.hm) supplies a constant `ground` and one
unary operation `apply`. [UnaryFormation.lean](../../lean4/Hypermath/UnaryFormation.lean)
examines fixed, finite expressions over that signature with two input variables:

```text
t ::= ground | first | second | apply(t)
```

The input variables are placeholders, not additional native operations. For
any carrier `A`, base `g` and function `a : A -> A`, interpretation substitutes
two values for the variables and interprets each `apply` by `a`. This does
not require the carrier to be a free syntax type or the function to be injective.
The expressions, values and layer indices here have no physical units.

A **fixed term definition** chooses one expression before receiving its input
values. Its number of `apply` nodes cannot depend on those values. Recursion on
an input, conditional tests, variable-length execution, a binary constructor,
and interpretation of encoded rules are additional mechanisms. Their absence
from this small expression grammar does not prove their absence from every
possible native development.

## Checked input-dependence theorem

For every such term `t`, its interpreted binary operation ignores at least one
input. The proof is structural induction: each leaf contains at most one input
variable, and unary application cannot combine two dependency branches.

Two consequences are checked for all terms and all interpretations:

1. Suppose a symmetric, transitive relation `R` is the comparison used for the
   left and right identity laws. If the term has a two-sided identity `e`, then
   `R(x,y)` holds for every pair of carrier values. Thus no fixed term supplies
   those identity laws when some pair is unrelated. Associativity and
   noncommutation are not premises of this obstruction.
2. If a decoder of the output recovers both input values for every pair, then
   all carrier values are equal. The decoder may be an unrestricted host
   function returning an optional pair; it need not itself be a unary term.
   On a carrier with two distinct values, information discarded by the encoder
   cannot be recovered this way.

For the first consequence, if the operation ignores its first input, its right
identity law relates the common value `operation(e,e)` to every `x`. If it
ignores the second input, its left identity law does the same. Symmetry and
transitivity then relate every `x` to every `y`.

These are distinct conclusions. Universal relatedness need not mean equality
of values. The module checks two boundary examples: a singleton carrier admits
a term identity under equality, and the universal relation admits a term
identity even on natural numbers. The required nontriviality cannot be dropped.

## Existing full-clause interpretation

[FullAxiomModel.lean](../../lean4/FullAxiomModel.lean) interprets forms as two
successor chains and native congruence as equality. Ground and its first
successor are distinct. In this same model:

| Declaration | Checked proposition |
| --- | --- |
| `no_fixed_term_identity` | No expression of the displayed grammar supplies the two-sided identity laws |
| `no_fixed_term_pair_encoder` | No such expression encodes both arbitrary form inputs with exact recovery |
| `full_clauses_without_fixed_term_composition` | Both obstructions coexist with all 38 translated logical clauses |

This is separate from the earlier [uniform noncommutation conflict](SEQUENCING_LAWS.md).
Removing uniform noncommutation repairs that particular conflict but does not
give a unary expression a second input dependency. Conversely, this result does
not exclude an externally defined operation on the model or an operation
derived through a richer, adequately justified native construction.

## What layer `n+1` must contribute

The existing [finite representation construction](LAYER_PRESERVATION.md)
retains both operands in its `seq` constructor. A lift retains the complete
lower representation as an atom. Its preservation theorem therefore concerns
a grammar with actual binary composition and explicit decoding. The
[Verifier adapter](LAYER_GRAPH.md) checks those supplied operations and binds
their ordered inputs to their output.

The remaining native bridge must explain how forming produces that capacity:
how two representations become jointly available, how their boundaries and
order are retained, and how the resulting checking operations are derived.
Merely renaming a fixed nest of unary applications as composition cannot
establish those properties. This does not require adding a second *primitive*:
a justified derived execution or representation mechanism could supply them.
Its derivation and adequacy are the open obligations.

As a concrete distinction, natural-number addition is available through the
host's recursive definition and supplies the existing sequencing interface.
`natural_add_not_a_term` nevertheless proves that no fixed term in `0`,
successor and two variables computes it on all natural numbers. Therefore
failure of fixed-term definability is not failure of recursive definability.
The source-native recursion needed for an analogous construction is not
established by using Lean's recursion.

Neither this boundary theorem nor the finite graph supplies a source-native
acceptance predicate, new logical inference rules, an ordinal interpretation,
limit stages, arithmetic completeness or a novelty result. Those obligations
remain distinct from preservation of existing finite derivation records.

## Reproduction and evidence scope

Run the audit from the repository root after installing the pinned toolchain
and the development dependencies:

```console
python -u lean4/audit.py
python -m pytest tests/test_audit.py tests/test_integrity_commands.py -vv -s --durations=10 --timeout=60
```

The mandatory full-model process now reports 63 declarations. Eleven were
added for this boundary: eight generic results or boundary examples, two model
specializations, and the combined full-clause statement. Ten have no axiom
dependencies. The combined statement inherits propositional extensionality,
classical choice and quotient soundness from the existing full-model proof.
The new module adds no axiom or admission. Its source bytes and all exact
dependency reports are required by the audit policy.

The overall audit still reports 67 source assumptions and 11 admission sites.
It does not discharge the existing self-derivation or arithmetic proof gates.
