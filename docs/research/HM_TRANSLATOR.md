# The `.hm` translator: measured coverage and limits

`hypermath_foundations.translate` reads `.hm` files and emits a canonical intermediate
representation, a Lean 4 file, a Metamath file, and a receipt that records for every
declaration whether it was translated and, if not, why. It uses the Python standard library
only; `dependencies = []` is unchanged.

```console
hypermath-foundations translate L0_ground.hm L1_relations.hm L2_operations.hm L3_ordinatics.hm \
    --out out/ --lean "$HM_LEAN" --mmverify "$HM_MMVERIFY"
python -m hypermath_foundations.translate --lint L0_ground.hm L1_relations.hm \
    L2_operations.hm L3_ordinatics.hm
hypermath-foundations translate --drift lean4 L0_ground.hm L1_relations.hm \
    L2_operations.hm L3_ordinatics.hm
```

Files are given in dependency order so that relation symbols, arities and infix words are
inherited. `--out` receives `Out.lean` (when `--lean` is given), `out.mm` (when
`--mmverify` is given) and `receipt.json`. `--lint` and `--drift` print and exit. Without
`--lean`, nothing is kernel-checked and no Lean file is written; the command says so.

Labels used here: **FORM** is a result checked by a named tool in this repository;
**OPEN** is an obligation with no result; **UNKNOWN** is not established either way.

## Fail-closed behavior

Every declaration ends in exactly one status: `translated`, `admitted`, `untranslated`
(with a reason and a source line) or `builtin`. Nothing is dropped, guessed at, or promoted
to a proved statement. An axiom or derive that uses a word the sources never declare, a
`close:` stated in prose, or a block with no `close:` line stays `untranslated`.

A `derive` is proved only when it is a bare single-step instantiation of one stated
axiom whose result equals its `close:`. Otherwise it is emitted as a Lean theorem whose
proof is `by sorry` (status `admitted`) and is omitted from Metamath. If the proof of a
supposed instantiation fails in the Lean kernel, the translator replaces it with `sorry` and
records the repair in the receipt; it never keeps a proof the kernel rejected.

## What the checkers certify

| Target | Oracle | Certifies | Does not certify |
|---|---|---|---|
| Lean 4.14.0 (the pinned `lean4/lean-toolchain`) | `lean` kernel | the generated file type-checks; `sorry` marks an admitted obligation | that the Lean statement means what the `.hm` statement means |
| Metamath | `mmverify.py` | the vocabulary is sort- and arity-consistent; a bare-instantiation derive has a real substitution proof | any logic: the generated database has no logical axioms |

Translation fidelity, that is, source adequacy of the translator, is UNKNOWN. A passing
Lean or Metamath check on the output is evidence about the output file, not about the
`.hm` text. The receipt's own `guarantees` list says the same, and its SHA-256 binds the
receipt contents and the SHA-256 of every source file given.

## Measured coverage on L0 to L3

Recomputed in this repository on the four `.hm` files at their root-relative paths, with
Lean 4.14.0 from the pinned toolchain and `mmverify.py`, by the `translate` command above.
There are 109 declarations (L0: 41, L1: 25, L2: 26, L3: 17).

| Kind | Translated | Admitted | Untranslated | Builtin |
|---|---|---|---|---|
| axiom | 20 | | 6 | |
| derive | | 5 | 32 | |
| close | | | 12 | |
| graduation | | | 4 | |
| relation | 3 | | | |
| opaque | 17 | | | |
| primitive | 9 | | | 1 (`Prop`) |

- Of the 20 translated axioms, 16 are also emitted to Metamath and 4 are omitted there
  because they contain nested quantifiers (each omission records its reason).
- Of the 5 admitted derives, 3 (`apply-ground-is-distinct`, `apply-ground-continues`,
  `double-apply-ground-orbits`) are proved by instantiation in Lean and Metamath. The other
  two (`two-members-in-class`, `ground-is-form-closed`) are not bare instantiations and
  stay `sorry` in Lean and omitted in Metamath. The generated Lean file contains 2
  `by sorry` obligations, and the Lean compiler reports exactly two `sorry` warnings.
- Lean 4.14.0 compiles the generated file with exit code 0 and no errors; no kernel repair
  was needed.
- The 6 untranslated axioms are `ax-seq-asymm` and `ax-seq-identity` (use `plus`, never
  declared), `ax-coop-comm` and `ax-coop-identity` (use `additionally` with no declared
  arity), `ax-compose-nonempty` (the token `congruent-path-part-of` is outside the
  translatable fragment) and `ax-limit-derives` (uses `start`, never declared).
- The 32 untranslated derives mostly have a `close:` that names another block, a status
  tag, or prose; 6 have no `close:` line at all. The 12 untranslated closes and 4
  graduation blocks are prose or comment-only.

The tests do not pin these numbers, because they move whenever an `.hm` file changes.
`tests/test_translate_targets.py` instead asserts invariants on the real files: every
declaration has a status, every untranslated one has a reason, counts add up, the receipt is
deterministic and binds the source digests, and, when the tools are present, the generated
Lean compiles and the Metamath subset verifies.

## Source defects the translator surfaces

`--lint` groups, per declaration, the first problem found. On the current `.hm` files it
reports three words that are used but never declared (`additionally`, `plus`, `start`; five
declarations), twelve distinct `close:` names across fourteen declarations that point at
another block or a status tag instead of stating a formula, three closes whose content is
only in comments (`close-struct-continues`, `close-struct-distinct`,
`close-struct-orbits`), and 21 statements in prose outside the translatable fragment. These
are findings about the `.hm` text for the maintainer. This change edits none of the `.hm` files.

A `close X as Y:` block that carries a formula line becomes a named axiom with universal
binders whose sorts are read from parameter positions; ambiguous or untyped variables are
refused. None of the current L0 closes carries a formula line, so none translates today.
That is a source-syntax proposal and is not applied anywhere.

## Drift against the hand-written Lean

`--drift lean4` compares each derive's `.hm` tag with the hand-written Lean theorem of the
expected name. The comparison is textual and not semantic: a theorem that depends on a
`sorry` elsewhere is read as `proved`. On the current repository, of 37 derives: 16
`proved`, 7 `sorry`, 9 with no Lean theorem of the expected name, 2 `FRAME` without Lean,
and 3 reported as `refuted-in-countermodel`.

The three are `ordinal-zero-identity`, `ordinal-succ-applies` and
`path-length-arithmetic`, tagged `FORM` in `L3_ordinatics.hm` while
[`FiniteActionCountermodel.lean`](../../lean4/FiniteActionCountermodel.lean) refutes their
claims, as consequences of the 38 Lean clauses, in a finite model. Their tags are unchanged.
That finite refutation shows non-derivability from the clauses as formalized; that file
itself disclaims native-semantics adequacy. The separate result that the same finite model
satisfies the three claims once `ordinalApply` is given a table is recorded in
[transfinite form, ladder induction, and the counterexample rescue](LADDER_INDUCTION.md).
Whether to add recursion equations to L3 or retag the derives is a maintainer decision and
is still pending.

## Tests

`tests/test_translate_parser.py`, `test_translate_expr.py`, `test_translate_project.py` and
`test_translate_targets.py` hold 62 tests. Without any environment variable, 56 pass and 6
skip: the kernel and Metamath tests skip when `HM_LEAN` or `HM_MMVERIFY` is unset, and a
skip is not a pass. Set both in any run meant to be a gate:

```console
HM_LEAN=/path/to/lean HM_MMVERIFY=/path/to/mmverify.py python -m pytest -q
```

With both set, all 62 pass. The suite includes a differential test against the hand-written
`lean4/Hypermath/L0Ground.lean` (the generated vocabulary and the four named axioms match
its types exactly), negative tests in which the Lean kernel and `mmverify.py` reject
tampered output, and a test that a bad instance proof falls back to `sorry` rather than
being silently accepted.

## Limits

- Only a fragment of the `.hm` language is parsed into statements. Blocks outside it
  (termformer, law and similar) are kept as raw text with a reason.
- Untranslated does not mean false or unimportant; 21 prose statements and the six
  untranslated axioms carry mathematical content that this tool does not read.
- A kernel-accepted output file is accepted relative to the Lean statements the translator
  chose. Source adequacy remains UNKNOWN.
- The Metamath output has no logical axioms and certifies vocabulary and instantiation only.
- The translator is not part of the audit gate. `lean4/audit.py` does not run it, and no
  gate result depends on it.
