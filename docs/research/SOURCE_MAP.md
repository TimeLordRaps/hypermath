# Seed-ai to Hypermath source map

Mapped September 7, 2026, against Hypermath base commit
`819f6856101c91fb3f0f4d25126e2f7329137b53`. The current root specifications are
preserved. Selected earlier sources live under
[`references/seed-ai`](../../references/seed-ai/README.md), with exact byte
provenance in its manifest. They supply missing context for fractal
meta-representation and self-derivation; importing them establishes no theorem.

## Correspondence

| Seed-ai source | Current destination or obligation | Disposition |
| --- | --- | --- |
| `hypermath/spec/axioms.hm` | `L0_ground.hm`, relation foundations | Earlier unified specification; reference copy |
| `hypermath/spec/casting.hm`, `links.hm` | `L1_relations.hm`, explicit casts and dependency links | Unique proposed machinery; reference copies |
| `hypermath/spec/verify.hm` | Lean/checker correspondence | Non-executable checker specification; reference copy |
| `hypermath_form/ground.hm` | `L0_ground.hm` | Earlier layered presentation; preserve separately |
| `hypermath_form/relations.hm` | `L1_relations.hm` | Earlier relation definitions; reconcile semantics |
| `hypermath_form/operations.hm` | `L2_operations.hm` | Earlier operators; reconcile path and composition contracts |
| `hypermath_form/ordinatics.hm` | `L3_ordinatics.hm` | Earlier ordinal/wrap proposal; not a proved extension |
| `hypermath_form/kernel.hm` | Reification and proof-checking bridge | Proposed Metamath correspondence; not a verified kernel |
| `hypermath_frame/spec/kernel.hm` | Checker obligations and explicit limits | More conservative verification design; preserve comparison |
| `hypermath_frame/spec/ordinatics.hm`, `stdlib/hyperordinal.hm` | Value/path separation beyond L3 | Design proposals; do not merge their assertions into current axioms |
| Hypergrammar chapter 24 | Fractal representation operation | Closed trajectories become reusable atoms; preservation theorem absent |
| Chapter 36, lines 43–149 | Term/operator self-representation | Mathematical excerpt only |
| Chapters 45–47 | Compression and completeness target | Conjectures, known numerical/coding errors, and explicit open target |
| Chapters 97–99 | Extended hierarchy and path/base-descent | Later proposals and preserved downstream gaps |

There are 20 captured source inputs: 19 whole files and one bounded excerpt.
Remaining `.hm` files in the three Hypermath source directories are
metadata-mapped without importing their application content. The frame-tree
`axioms.hm` is byte-identical to `hypermath/spec/axioms.hm` and maps to the
single captured copy. The manifest distinguishes that duplicate from files
merely sharing names.

## Supporting context without bulk import

- Chapters 1–6 supply conceptual ancestry of the ground, relation, and
  hyperstructure vocabulary. Their older primitive counts and relation laws
  are not automatically the current specification.
- Chapters 9, 22–23, 42–44, and 48–53 supply language calculus, compression,
  arithmetic, and ordinal motivation. Selected chapter/specification snapshots
  capture the immediate dependencies of this investigation.
- Chapters 75–76 and 83–84 concern glyphs, form calculus, wrap, and cardinal
  questions. Their stronger application claims require separate proofs.
- Chapter 82 proposes a sequence from ordinal ground to set theory, number
  theory, analysis, and applications. This is an architecture plan. Replacing
  assumptions by genuine derivations at each step is the substantive work;
  neither a `#check` command nor a closure label discharges it. Its full text
  is not imported because it mixes mathematics with unrelated rhetoric.
- The nomenclature catalogue is a terminology source. Analytic, metric,
  zeta-function, density, quantum, and simulation modules are an application
  backlog. They are outside this foundational import.

Personal/clinical material, business and political notes, historical state
ledgers, generated scaffolds, archives, and Windows device-like entries are
excluded. The original Seed-ai worktrees remain untouched.

## Semantic differences that must not be merged by name

1. Hypergrammar's earlier strict `=` denotes derivation-path identity. The
   `.hm` sources use `==` for mutual path reproduction. Neither is automatically
   Lean equality or the other source's relation.
2. The earlier `hypermath_form` congruence definition uses all continuation
   capacity; current L0 describes substance agreement independent of path.
   An interpretation must establish the intended relationship.
3. Nonempty continuation overlap need not be transitive. The alternative
   shared-ground biconditional would be transitive. The latter cannot serve
   as an unnoticed implementation of the former.
4. Source-native propositions include a proposed discharge account. The Lean
   translation currently uses Lean's proposition sort. Adequacy is unproved.
5. A representation's nesting depth, an ordinal's value, a proof's ordinal
   presentation, and a truth-language stage are distinct coordinates. The
   earlier Ordinatics paper supplies one semantic hierarchy, not the whole
   self-derivational mechanism.

## Import and provenance checks

The import script contains a fixed file allowlist and one fixed excerpt range.
It checks the destination remote before writing, retains source bytes, and
refuses differing existing snapshots. The manifest includes source and
destination digests; the checker validates each captured file and local
correspondence path. These checks establish reproducible mapping, not the
validity of the imported claims. Relative imports inside old `.hm` snapshots
may remain unresolved, so this collection is not advertised as executable.

The stronger target is developed in
[FRACTAL_COMPLETENESS.md](FRACTAL_COMPLETENESS.md); concrete defects and repairs
are recorded in [PROOF_AUDIT.md](PROOF_AUDIT.md).
