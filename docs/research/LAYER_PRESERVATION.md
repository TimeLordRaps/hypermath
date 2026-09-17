# Composition and preservation through finite representation layers

The author places composition at layer `n+1` relative to a self-derivation
kernel at layer `n`: self-derivation supplies verification geometry, which
supports a provable graph and further composed surfaces. The intended chain
continues through logical structures to ordinal arithmetic and arithmetic
redefined "formally closed-like." This note gives a checked finite
representation construction toward that chain. Its source is
[`LayeredDerivation.lean`](../../lean4/Hypermath/LayeredDerivation.lean).
The native kernel-to-geometry construction and ordinal interpretation remain
separate obligations.

## Defined objects and checking behavior

The dimensionless natural number `n` indexes representation layers. It is
neither an assigned ordinal value nor an arithmetic-truth rank. Layer zero
contains a pair: a raw ground-calculus proof record and its claimed formula.
The record retains its complete inference tree, including premise records.
It can be invalid; acceptance is computed, not supplied as a constructor.

Every successor layer uses three expression constructors:

| Constructor | Retained representation | Checking behavior |
| --- | --- | --- |
| `empty` | An explicit empty expression | Produces an empty list of checked records |
| `atom` | The complete encoded lower-layer surface | Decodes at exactly the preceding layer and checks recursively |
| `seq` | Two ordered child expressions, including their grouping | Requires both checks to succeed and concatenates their record lists |

The tree encoding has an outer format tag `12` and a nested layer tag. The
decoder rejects an encoded surface from a different layer. Successor layers
share the `Expression` carrier, so this runtime layer check is material.
`decode_encode` proves exact recovery; `encode_injective` proves that distinct
surfaces at a given layer cannot acquire the same encoding. This is a theorem
about the defined trees, not a wire-format or cryptographic-hash guarantee.

`unfold n s` returns either the complete ordered list of checked record/claim
pairs or `none`. At layer zero it runs the existing instruction-level
`RecordMachine.check`. At a successor layer it checks encoded atoms at the
strictly lower layer and visits the finite expression tree. Invalid records,
incorrect claims, malformed encodings, and wrong-layer atoms fail the check.

`check n s claims` additionally compares the resulting **ordered list** of
formulas with `claims`. Repetitions count. This surface composition sequences
checked evidence; it does not introduce a new inference rule combining two
conclusions into an otherwise unproved third conclusion. Inferences within
each record remain the existing ground-calculus rules.

## Preservation theorem

Write `L_n(s)` for `lift n s`, the next-layer atom containing the exact encoding
of `s`. Write `L_n^k(s)` for `iterateLift k n s`, which repeats that construction
`k` times. Here `k` is another dimensionless natural number. Let `U_n` denote
`unfold n`, and let `R_n^k` denote `recoverThrough k n`, which removes those
atom boundaries and decodes at every step. Define `combine` to concatenate two
successful evidence lists and return failure if either input failed.

For every layer, surface, and finite iteration count, Lean checks:

\[
R_n^k(L_n^k(s))=\operatorname{some}(s),
\qquad U_{n+k}(L_n^k(s))=U_n(s).
\]

These are `recoverThrough_iterateLift` and `unfold_iterateLift`. Induction on
`k` uses the exact one-layer decoder and checking equalities. Consequently,
every function observing the original surface can be applied after recovery
with the same result (`observe_iterateLift`). This retains encoded syntax and
inference data, including rejected inputs; it does not require acceptance.

The combined result, `composition_lift_preserves`, specializes those equalities
to a composition of arbitrary surfaces `a` and `b` at layer `n+1`:

\[
R_{n+1}^k(L_{n+1}^k(\operatorname{seq}(a,b)))
=\operatorname{some}(\operatorname{seq}(a,b)),
\]

\[
U_{n+1+k}(L_{n+1}^k(\operatorname{seq}(a,b)))
=\operatorname{combine}(U_{n+1}(a),U_{n+1}(b)).
\]

Thus both the exact composition tree and its checking outcome survive every
finite number of lifts. A failed premise cannot become valid by wrapping it
in further representation layers. `check_seq` also proves that composing two
accepted surfaces accepts their concatenated list of claims; `check_iff`
characterizes the list equality tested by the checker.

`unfold_sound` connects every emitted record to the existing recursive ground
checker. `unfolded_claims_sound` and `check_sound` then use its soundness theorem:
every emitted claim holds in any **supplied model of that ground calculus**.
This is conditional model soundness. It does not supply the intended native
model or a soundness interpretation into arithmetic.

## Composition laws and retained distinctions

`SameExpansion n a b` means equality of the complete `unfold` results at layer
`n+1`. With this declared relation, `seq` and `empty` instantiate the
[sequencing monoid interface](SEQUENCING_LAWS.md): identity, associativity,
equivalence, and compatibility are proved together for that operation.
`liftMap` preserves the operation and identity under this relation, and
`lift_reflects_expansion` proves preservation and reflection of the relation.

The raw syntax retains more information than `SameExpansion` observes:

- Different parenthesizations have different encodings, although they expand
  to the same ordered records.
- Lifting a whole composition and composing its lifted inputs have different
  layer boundaries, although their checked expansions agree.
- All surfaces whose expansion is `none` are related by `SameExpansion`.
  Their different rejected representations remain available in the raw syntax.

This relation is therefore not being identified with native congruence,
similarity, simulation, or exact surface equality. The constructed empty
expression is a unit modulo `SameExpansion`; it does not identify the native
self-derivation kernel with that unit.

The existing free-ground syntax also represents any entire surface as one
term: `readGroundTerm_groundTerm` proves recovery, `observe_groundTerm`
preserves observations, and `checkGroundTerm_groundTerm` proves agreement with
checking the original surface. This unary representation can be enormous.
The construction supplies no compression or practical complexity bound.

## Audit scope and reproduction

The default Lean library imports the new module. The audit runs
[`LayeredDerivationChecks.lean`](../../lean4/LayeredDerivationChecks.lean) as a
separate required process and checks 80 exact dependency reports. The original
45 consist of 31 supporting and main theorems, two algebra constructions, and
12 positive or negative probes. The [contextual composition bridge](CONTEXTUAL_COMPOSITION.md)
adds 11 theorems and six checks connecting retained premises, conjunction
inference, execution histories, and finite lifts.
The [operational correspondence criterion](OPERATIONAL_CORRESPONDENCE.md) adds
11 local-to-global execution/layer theorems and seven checks of the required
representation-domain and retained-state conditions.
Their only reported axioms are Lean's propositional extensionality and
quotient soundness where used. None uses classical choice, a native Hypermath
assumption, or an admitted proof.

The probes include universally quantified finite-lift acceptance and rejection
theorems, malformed and wrong-layer atoms, invalid composition, reversed claims,
lost repetition, and retained grouping and layer boundaries. Executable checks
exercise lift depths zero, one, two, and four; these examples supplement the
induction theorems rather than establish their universal quantifiers.

From a Hypermath checkout with the declared development dependencies and Lean
toolchain installed, the repository audit runs each native process under the
specified time bound:

```console
python -u -m hypermath_foundations audit --root . --timeout 60 --output build/layer-audit.json
python -m pytest tests -vv -s --durations=10 --timeout=60
```

The audit binds the layer and contextual composition sources and their exact reports. Missing
preservation or recovery results, hidden dependencies, an admission, replaced
source bytes, or a failed process cannot pass this check. Windows checkout
tests cover the line-ending rules needed to preserve the bound source bytes.
Software and audit integrity do not discharge the stronger mathematical gates.

## What remains to connect to the author's mechanism

The finite construction implements an explicit preservation step. Its grammar,
layer counter, decoder, and recursive checker are host definitions. They have
not yet been generated from the opaque native `Form` and `f2f` operations.
The next connection must establish that native forming realizes these
constructors and checking transitions, retaining their required observations.

The [finite layer graph adapter](LAYER_GRAPH.md) now binds these host transitions
through Verifier. It invokes this Lean checker, retains ordered operands and
repetitions, and checks the exact output. The native geometry-to-graph
correspondence and internally represented acceptance proof remain further
obligations; input-set membership alone cannot establish them.

The finite iteration theorem supplies no limit stage, ordinal ordering, ordinal
operation, full arithmetic-truth coverage, or self-certification of the checker.
It also supplies no separation from existing representation methods. Native
generation, the ordinal interpretation, and the intended "formally closed-like"
arithmetic and novelty claims remain active research obligations.
