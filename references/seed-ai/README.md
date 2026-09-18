# Seed-ai mathematical reference snapshots

These are selected, author-supplied mathematical source documents mapped into
Hypermath on September 7, 2026. They preserve original source bytes except the
explicitly identified chapter 36 excerpt. Their original `FORM`, `FRAME`, and
completeness assertions remain historical claims, not current verification
results. They are reference material, not active repository instructions or a
runnable dependency tree.

Read the [source map](../../docs/research/SOURCE_MAP.md) and
[proof audit](../../docs/research/PROOF_AUDIT.md) before using a claim from these
documents. The current four root `.hm` files and the Lean translation are
separate artifacts with their own unresolved obligations.

[manifest.json](manifest.json) records each original path and its Secure Hash
Algorithm 256-bit (SHA-256) digest, the imported byte digest, classification,
and target correspondence. A digest binds bytes; it does not certify their
mathematics. Chapter 36 is limited to source lines 43–149, inclusive. The two
identical earlier `axioms.hm` files share one captured copy.

Git text normalization is disabled for this directory so a fresh checkout
retains the bytes bound by the manifest. Original trailing spaces and excerpt
boundary blank lines are preserved; they are not formatting changes to the
active code or specifications.

The mathematical selection excludes unrelated personal, clinical, business,
political, and physical-application material, generated outputs, and archives.
Original notices and author attribution are retained. Historic layer names and
filenames are evidence locators; current framework terminology is Ordinatics.

To check the snapshots from the repository root:

```console
python -u scripts/check_reference_sources.py
```

The import script's explicit allowlist documents the selection. It refuses to
overwrite differing snapshots; a later source revision requires a separately
reviewed capture. The mapping records local working-file bytes, including
uncommitted source changes, rather than pretending they all belong to an older
Git commit.
