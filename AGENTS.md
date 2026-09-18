# AGENTS.md

Working rules for automated contributors to Hypermath. Read this before editing anything.

## 0. Before you touch anything

High-risk couplings are enforced by CI. Check this table first.

| If you are changing... | You must also... |
|---|---|
| the version, anywhere | bump all five: `pyproject.toml`, `src/hypermath_foundations/__init__.py`, `CITATION.cff`, `.zenodo.json`, and a dated `## X.Y.Z - YYYY-MM-DD` heading in `CHANGELOG.md` |
| `lean4/Hypermath/*.lean` axioms | keep the source assumption inventory matching `src/hypermath_foundations/_baseline.py` exactly (18 kernel axioms; never add unreviewed axioms) |
| dependencies | put it in an optional extra. `dependencies = []` is enforced by CI stdlib-smoke |
| boundary phrasing in `README.md` | preserve required boundaries and non-claims; the presentation gate asserts them |
| release scripts or boundaries | run `scripts/check_release_boundary.py` and `scripts/release_artifacts.py` |

Then, before you propose the change:

```bash
python -m pytest -q
python scripts/check_presentation.py
```

## 1. What this repository is

Hypermath is a **foundational formalization and bounded evidence audit framework** for
a self-derivational mathematical universe built around the primitive operation `□` (`f2f`),
finite layer graphs, operational correspondence, and reflexive structures.

The distribution is `hypermath-foundations`, the import package is `hypermath_foundations`,
and the CLI command is `hypermath-foundations`.

### 1.1 Ecosystem Ancestry and Adjacent Repositories

Hypermath operates within Tyler Roost's formal mathematical ecosystem alongside three
tightly coupled adjacent formal systems and one reference standard:

1. **`ordinatics`** (`TimeLordRaps/ordinatics`):
   Transfinite stage semantics, ordinal arithmetic, ordinal notation normal forms, and
   Veblen/Bachmann hierarchies that provide the transfinite backbone for Hypermath's
   stage limits (`L3_ordinatics.hm`, `L3Ordinatics.lean`).
2. **`grounded-hyperset-theory`** (`TimeLordRaps/grounded-hyperset-theory`):
   Aczel's Anti-Foundation Axiom (AFA), accessible pointed graphs (APGs), non-well-founded
   set systems, and quotient abstractions grounded in physical and operational traces.
3. **`grounded-hypercalculi`** (`TimeLordRaps/grounded-hypercalculi`):
   The six formal calculus pathways: Oracle, Language, Meta, Hyper, Ordinal, and Real
   Calculi, governing discrete rewrite semantics, Lie brackets, and dimensional transitions.
4. **`verifier`** (`TimeLordRaps/verifier`):
   The Verifier Standard (VSTD) reference implementation for portable, bounded, refutable
   evidence receipts, certificate checking, and provenance ledgers. Hypermath verification
   receipts conform directly to VSTD formats (`hypermath_foundations.vstd`).

### 1.2 Understatement as Strategy

A formal foundation that claims more than its machine-checked proofs establish spends its
only credibility budget. That is why an uncertain or negative result is frequently the
correct output:
- Source adequacy is UNKNOWN (no meta-adequacy proof connects `.hm` to `.lean`).
- Recursive arithmetic completeness is UNKNOWN.
- An unproved proposition is marked UNKNOWN, never PASS.
- Refutations (such as the non-spanning countermodel) are positive results.

## 2. Prime directive

> Changes that strengthen a claim without stronger evidence are non-conforming.

Specifically, never:
- turn `UNKNOWN` or `CONFLICTED` into a clean or passing result;
- infer, backfill, or synthesize missing provenance;
- add unreviewed axioms to bypass a failing proof gate;
- treat self-observation as independent verification;
- soften a detected countermodel into silence.

## 3. Environment and commands

```bash
python -m pip install -e ".[dev,verification]"
python -m pytest -q
python scripts/check_presentation.py
python -m compileall -q src scripts
```

Pure standard-library smoke, mirroring the CI `stdlib-smoke` job:

```bash
PYTHONPATH=src python -S -c "import hypermath_foundations; print(hypermath_foundations.__version__)"
```

Lean 4 compilation and verification, mirroring the CI `native-audit-integrity` job:

```bash
cd lean4
lake -v build
lake env lean Audit.lean
```

Local reproducible release checks, mirroring `release-integrity`:

```bash
python scripts/release_artifacts.py build --ref HEAD --release 0.1.0 --output-dir dist/release-integrity
python scripts/release_artifacts.py verify dist/release-integrity/hypermath-foundations-0.1.0.manifest.json
python -m twine check dist/release-integrity/*.whl dist/release-integrity/*.tar.gz
python scripts/check_release_boundary.py dist/release-integrity/*.zip dist/release-integrity/*.whl dist/release-integrity/*.tar.gz
```

Cross-platform artifact comparison:

```bash
python scripts/release_artifacts.py compare PATH_TO_LINUX_ARTIFACTS PATH_TO_WINDOWS_ARTIFACTS
```

## 4. Layout

- `L0_ground.hm` ... `L3_ordinatics.hm` — foundational domain specifications.
- `lean4/` — Lean 4 formalization, axiom definitions, countermodels, probes, Lake build.
- `src/hypermath_foundations/` — Python reference package:
  - `audit.py` — subprocess execution of Lean 4 audit commands.
  - `_baseline.py` — reviewed declaration identities and source SHA-256 allowances.
  - `_reports.py` — parser and policy validator for Lean output.
  - `_surface.py` — Lean surface runner with input/source digest binding.
  - `layer_graph.py` — finite layer graph construction and transformation.
  - `abstraction.py` — quadrilateral filtration and transitive abstraction (~=).
  - `calculus_bridge.py` — formal metamath bridge and calculi models.
  - `meta_fractal.py` — hyperkernel fixed-points, Quine atoms, APGs.
  - `objectification.py` — proof trajectories and quotient classes.
  - `vstd.py` — Verifier Standard receipt generation and binding.
  - `gate.py` — proof admission and self-derivation gating.
- `scripts/` — `release_artifacts.py`, `check_presentation.py`, `check_release_boundary.py`,
  `check_installed_wheel.py`, `check_foundation.py`, `check_layer_graph.py`, `setup_lean.py`.
- `tests/` — pytest contract suite.

## 5. Invariants that must not be refactored away

**Kernel isolation and reviewed allowance.** The 18 kernel axioms in `_baseline.py` and
`lean4/Hypermath/` represent the reviewed assumption policy. Adding new axioms to
`lean4/Hypermath/` without explicit mathematical review violates the audit integrity gate.
Extensions must be defined constructively via inductive types, structures, or definitions.

**Zero required runtime dependencies.** `dependencies = []` in `pyproject.toml` is enforced
by `stdlib-smoke`. All third-party tools (`pytest`, `verifier-standard`, `ruff`, `build`,
`twine`) belong in optional extras.

**LF line endings.** `.gitattributes` forces `eol=lf`. The release builder and verifier
refuse CRLF/LF equivalence as byte identity.

**Reproducible multi-platform builds.** The wheel, sdist, and source ZIP produced on Linux
and Windows must match byte-for-byte under `scripts/release_artifacts.py compare`.

## 6. Presentation gate

`scripts/check_presentation.py` runs in CI and checks:
- local markdown links resolve;
- version agreement across `pyproject.toml`, `__init__.py`, `CITATION.cff`, `.zenodo.json`,
  and `CHANGELOG.md`;
- zero boundary leaks of private paths, drive letters, credentials, or token shapes;
- preservation of required non-claim disclosures.

## 7. Change process

Work lands via pull request into `main`. Commits are GPG-signed (`git commit -S`).
Never pass `--no-gpg-sign` or set `commit.gpgsign=false`.
Tagging and PyPI publication are maintainer-only operations executed through the OIDC
Trusted Publishing workflow in `.github/workflows/release.yml`.
