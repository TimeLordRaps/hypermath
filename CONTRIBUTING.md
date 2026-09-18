# Contributing to Hypermath

Contributions are welcome when they make a formal proof, specification surface, or
evidence audit more precise, more independently checkable, or easier to implement without
strengthening unsupported claims.

## Required for a normative change

- identify the affected Hypermath layer, repository release, and coordinate or seam;
- state compatibility effects, including any formal specification files (`.hm`) or Lean 4
  modules affected;
- include a falsification condition or countermodel;
- preserve the reviewed assumption policy: never add unreviewed axioms to the kernel;
- add tests that fail before the change and pass after it;
- document new trust roots, unknowns, residuals, and horizons.

Do not replace `UNKNOWN` with false, erase `CONFLICTED`, infer missing provenance, or
call self-observation independent verification.

Unless explicitly stated otherwise, a contribution intentionally submitted for
inclusion in this repository is provided under the Apache License 2.0, including its
Section 3 patent terms and Section 5 contribution terms.

## Commits

Commits in this repository are GPG-signed (`git commit -S`). Pull requests are expected to
carry signed commits, and automated contributors must never bypass signing. A commit
signature binds bytes to a signing key; it does not establish the signer's legal identity,
the change's correctness, independence, authorization, or safety.

## Feedback that does not require a proposed patch

Use structured issue forms for specification ambiguities, proof countermodels, or unsound
claims. A countermodel or refutation attempt is valuable evidence. Send vulnerability
details only through the private route in `SECURITY.md`.
