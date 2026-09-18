# Source and translation audit, September 7, 2026

Base: `TimeLordRaps/hypermath` commit
`819f6856101c91fb3f0f4d25126e2f7329137b53`. Scope: four root `.hm` layers,
their Lean translation, directly related dictionary entries, and the selected
Seed-ai mathematical sources. This is an assisted internal review, not an
external peer review or a consistency/completeness certificate.

## Repairs made without changing the intended mathematical laws

### Source integrity

Commit `bf22cb89cf6243e29e7788e9d09c83621dfbf6bb` accidentally removed L1's
deriver/matrix block and left truncated text while removing other declarations.
The block was recovered from
`e587fefc871e4c4a067303e41c159894bc55f5fd`. Its text is unchanged apart from
the section numeral. `deriver`, `D`, `D-is-reflexive`, and `D-spans-ground`
now each appear once. The stray `VIII` and duplicated trailing `1, 2505.`
fragment were removed. The deliberately removed unrelated primitives remain
removed. Restoring a purported derivation does not prove it.

### Lean translation

The original bounded build failed: bodyless `opaque` declarations attempted
to obtain unspecified inhabitants. Source-declared uninterpreted primitives
are now explicit Lean parameter axioms, making their assumption status
visible. The logical clauses and unresolved theorem obligations remain
separate. No missing theorem was replaced with an axiom.

Mechanical repairs address iteration syntax, incorrectly typed proof terms,
and the path/form mismatch in the limit-path clause. The source's `start`
and `end` projections are represented explicitly rather than confusing a
path with a form or its length with its endpoint. This does not prove the
missing infinite-path laws. The audit command reports exact current counts
and axiom dependencies, including `sorryAx` where a proof remains unfinished.

### Public descriptions

The README now states the stronger research objective and the actual
translation status. Dictionary corrections distinguish structural distinction
from ambient inequality, restore the restricted ground-continuation bridge,
and expose the unproved translation of native propositions to Lean's `Prop`.
The original layer `FORM` labels remain source claims; they are not presented
as mechanical verification results.

## Mathematical findings requiring explicit resolution

| ID | Finding | Evidence and next obligation |
| --- | --- | --- |
| M1 | Universal operand asymmetry conflicts with identity in the intended nontrivial congruence structure. | L2 `ax-seq-asymm` and `ax-seq-identity`: if `a` is not congruent to ground, the first forbids congruence between `a+ground` and `ground+a`; the identity laws and symmetric/transitive congruence require it. State the intended scope of noncommutativity. No axiom was silently weakened. |
| M2 | Strong self-return is assumed during its purported derivation. | L3 `deriver-cycle-is-closed` promotes similarity to congruence/simulation without a preservation theorem. A two-step return also does not imply that each single edge identifies its endpoints. Terminal self-derivation depends on this gap. |
| M3 | Finite and transfinite path contracts disagree. | L1 defines derivability by a finite chain; L2 declares finite paths; L3 describes an infinite path in that same type. Its limit description claims derivability while excluding finite congruent reachability. Separate and connect these contracts explicitly. |
| M4 | The written limit clauses omit their advertised content. | L3's limit-path clause omits the infinite-prefix conditions in its comments; its leastness clause does not assert the upper-bound property. An abstract object named `ordinalLimit` does not supply these facts. |
| M5 | Self-representation crosses sorts without a defined conversion. | L0 applies `syntax : Form -> Prop` to predicates/functions without reification. L2 uses proposition-valued entries of `D` as paths. Define representation and evidence extraction, then prove their preservation properties. |
| M6 | Similarity return does not prove a finite universe or terminating normalization. | The cited relational laws admit natural-number forms with successor and universal similarity, retaining infinitely many distinct forms. Decidable comparison, finite scope, strict decrease, and normal-form properties are separate obligations. |
| M7 | Reachability transitivity and directionality need additional arguments. | Finite reachability up to congruence need not compose unless `apply` respects congruence. Lack of a reverse proof is not proof of its negation. The finite probes below reproduce failures of these implications. |
| M8 | Path observation preservation is underspecified. | L2 compares endpoint, trace, and cost using similarity, while describing identical observations. Specify exactly which observations must agree for reuse and compression. |

These findings concern the stated implications and intended semantics. A
countermodel of selected relational assumptions is not a model of every
unwritten intended property of the framework. Conversely, an intended property
does not repair a proof until stated and justified.

## Imported-source findings

- Chapter 24 describes closed trajectories becoming reusable atoms. Its state
  count ratio is not an encoding/decoding or arithmetic coverage theorem.
- Chapter 45 explicitly leaves the combinatorial derivation open. Its displayed
  entropy expression evaluates to one half at continuation capacity one half,
  despite the stated value one. Its equation `n*n-n=n` has solutions zero and
  two. Interpreting `2^(n*n-n)` as independent off-diagonal binary choices does
  not establish a bijection with derivation paths.
- Chapter 46 infers failure of natural-number encoding from fast growth of
  finite path counts. For each depth `n`, let `c(n)=2^(n*n-n)`. The code
  `sum(c(j) for j<n)+k`, for `0<=k<c(n)`, assigns a distinct natural number
  to every such pair. Finite growth alone does not obstruct effective coding.
- Chapter 47 retains an explicit open mathematical target. Its presence is
  useful evidence that the earlier program was not a completed theorem.
- Chapters 97–99 mix ordinary ordinal operations, field operations, and complex
  exponential images. Under the current Ordinatics polynomial specialization,
  wrap of `omega+1` is one half, while wrap of `omega` is minus one half. The
  actual obstruction is preserving ordinary ordinal addition into a field,
  not failure of this map to distinguish those two values. An unrestricted
  complex exponential parametrization also has nonzero periods; a quotient or
  branch restriction is needed for injectivity.

The snapshots retain their source text for provenance. These observations
govern how those claims may be used in the current research. No analytic,
physical, or other downstream claims were certified by importing them.

## Reproduction and claim boundaries

From the repository root:

```console
python -u scripts/check_reference_sources.py
python -u scripts/check_audit_models.py
```

The first checks captured bytes, duplicate aliases, and correspondence paths.
The second runs five named finite probes: overlap, reachability composition,
two-step return, identity versus universal asymmetry, and finite enumeration.
They report each check visibly and terminate on small finite instances. The
general claims use the arguments above; finite examples alone do not prove
arithmetic completeness or incompleteness of the full proposed system.

From `lean4`, run the bounded audit described in [its README](../../lean4/README.md).
Build success means the Lean scaffold elaborates with its declared assumptions
and placeholders. The proof-completion gate must remain unsuccessful while
the selected results depend on unresolved proof obligations. The Lean audit
also checks an independent finite model of the specified lower-layer clauses;
it is distinct from a claimed native interpretation.

Observed results on the corrected working tree with Lean 4.14.0:

| Check | Observed result | Bound |
| --- | --- | --- |
| Library build | Exit 0, with admission warnings | 60 seconds per subprocess |
| Central dependency report | Exit 0; `selfDerivation` includes `sorryAx` | 60 seconds |
| Independent Lean countermodel | Exit 0; no custom axioms or admitted proofs in its reported results | 60 seconds |
| Overall proof gate | Exit 2: incomplete | Explicitly expected while proof holes remain |
| Lean source inventory | 21 `sorry` tokens; 31 source parameters and 38 logical clauses | Source inspection plus dependency report |
| Reference mapping | 20 snapshots and 36 source records checked | 30 seconds |
| Finite audit probes | Five named checks passed | 30 seconds |

The countermodel's reported ambient dependencies are propositional
extensionality (`propext`) and quotient soundness (`Quot.sound`), both Lean
foundational principles. It satisfies the translated 24 logical L0/L1 clauses;
it does not claim to satisfy all later L2/L3 assumptions or the missing native
continuation semantics.

No complete `.hm` parser, source-to-Lean adequacy theorem, full arithmetic
soundness/completeness theorem, or exhaustive novelty review was established.
The next mathematical work is in [FRACTAL_COMPLETENESS.md](FRACTAL_COMPLETENESS.md).
