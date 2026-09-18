# Finite ground syntax, primitive records, and checked reuse

This construction implements a first explicit source-syntax fragment for the
[fractal completeness target](FRACTAL_COMPLETENESS.md). It retains formation
syntax, represents primitive derivations as records in that same syntax, and
checks their exact conclusions. Soundness is proved relative to the four
primitive source rules. The full ranked self-closing surface remains open.

## Source correspondence

`lean4/Hypermath/GroundSyntax.lean` defines `Term` with exactly the finite
formation constructors in `L0_ground.hm`, Section I: `ground` and unary `apply`.
This free syntax is distinct from the semantic `Hypermath.Form` parameter.
Interpretation recursively maps the constructors to the existing `ground` and
`f2f` parameters, where `f2f` means form-to-form application.

| Source rule, L0 Section III | Syntactic derivation | Decoded conclusion |
| --- | --- | --- |
| `ax-ground-self` | `AxiomInstance.groundSelf` | Ground continues from itself |
| `ax-diff` at term `t` | `AxiomInstance.diff t` | Applying `t` is structurally distinct from ground |
| `ax-sim` at term `t` | `AxiomInstance.sim t` | Applying `t` continues from ground |
| `ax-box` at term `t` | `AxiomInstance.box t` | Applying twice to `t` structurally orbits `t` |

Distinctness, continuation, and orbit assertions remain separate. They are not
replaced by equality, similarity, or congruence. This fragment does not yet
encode composed derivations, arbitrary propositions, or acceptance derivations.
Lean's inductive types, recursion, equality, and checker proofs are host
infrastructure, with their assumptions reported explicitly. These are symbolic
objects; no physical unit or geometric fractal dimension is asserted.

## Record-only checking

An instance is encoded as another `Term`. Ground-self has depth zero. The other
rule tags have depths one, two, and three; every application in the argument
adds four applications to its record. Positive multiples of four are rejected.
This deliberately unary code makes no compression or efficiency claim.

`decode_encode` proves recovery of every encoded instance; `encode_injective`
proves that different instances retain different syntactic records.
`observe_encode` proves recovery of any observation of the retained instance.
Neither `decode` nor `check` receives an external proof object.

The checker decodes a record and compares its conclusion with the claimed
syntactic statement. `check_iff` characterizes acceptance exactly, and
`check_encode` proves acceptance of every encoded instance with its correct
conclusion. Concrete Lean theorems reject the wrong predicate, argument,
conclusion, and malformed records.

`Model` supplies precisely the four source-rule premises. `instance_sound` and
`check_sound` prove semantic soundness in every such interpretation.
`native_check_sound` specializes to six existing source parameters and four
logical clauses, plus Lean's propositional extensionality and quotient equality
principle. It adds no native clause and uses no admitted proof. This concerns
the four schemata; full source adequacy is not established.

## Concrete finite reuse

`nextArgument` reinstantiates a parameterized rule at `apply t`; the
argument-free ground-self instance remains itself. `reuse` decodes a record,
performs that transformation, and encodes the resulting instance. Malformed
input returns no record.

For every finite count `n` and instance `p`, `reuse_many_encode` proves

\[
\operatorname{reuseMany}(n,\operatorname{encode}(p))
=\operatorname{some}\bigl(\operatorname{encode}
  (\operatorname{nextArgument}^{n}(p))\bigr).
\]

Round-trip decoding and checker soundness therefore apply after every such
finite reuse. This does not create a derivation of the checker's own acceptance
claim or represent the checker as a native term. Those are separate obligations
in the ranked interface. No transfinite reuse theorem is supplied here.

## Semantic interpretation can lose records

In `FiniteActionCountermodel.lean`, the encoded `diff ground` and `box ground`
records have depths one and three. Their interpretations coincide in the
six-form model of all 38 current clauses, while their syntactic conclusions
differ. `no_semantic_primitive_record_decoder` proves that no function of that
semantic Form alone recovers every original instance encoded by this protocol.
All three new countermodel reports have no axiom dependencies.

This concerns these records and their interpretation. It does not exclude every
alternative encoding or require full recovery for every possible observation
class. Retaining syntax avoids this specific loss; its native reification and
acceptance still require proofs.

## Audit and next obligations

The mandatory `ground_syntax` process runs `GroundSyntaxChecks.lean` and requires
23 exact dependency reports: 13 without axioms, seven with propositional
extensionality, two with propositional extensionality and the quotient equality
principle, and the native specialization described above. The policy binds the
checker and reporter source bytes. Missing dependencies, altered source,
failed execution, or omitted replay cannot count as a successful audit.

The broader translation retains 67 declared assumptions and 11 admission sites.
Its existing 38 production milestones remain a separate audit group. The new
fragment leaves self-derivation, source adequacy, and arithmetic completeness
unresolved. The [composed ground calculus](COMPOSED_GROUND_DERIVATIONS.md) now
checks finite rule trees built from these primitives, the three predicate
closes, conjunction, and projections. It preserves accepted records through
typed reconstruction. Encoding those structured records as native terms,
preserving them through semantic interpretation, and internally deriving ranked
acceptance remain open.
