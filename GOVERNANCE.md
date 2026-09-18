# Hypermath governance

## Current phase

Hypermath is founder-maintained formal mathematics and proof-audit specification work.
Publication makes the specifications, Lean 4 proofs, and reference audit package
inspectable; it does not manufacture external consensus or academic recognition.

The Lean 4 formalization is implemented for the core layers (L0 through L3), operational
correspondence, finite layer graphs, and verified countermodels. Bounded claims remain
strictly qualified:
- Source adequacy connecting `.hm` to `.lean` is UNKNOWN.
- Recursive arithmetic completeness is UNKNOWN.
- The non-spanning countermodel refutes universal ground reachability.

## Layer and release states

- **Implemented base:** a layer has a published `.hm` specification, verified Lean 4
  formulation, passing Lake build, and passing audit assertions.
- **Experimental:** definitions or structural conjectures exist, but full machine-checked
  proofs or countermodels are still being investigated.
- **Refuted:** mathematical analysis or countermodels establish that a previously claimed
  property does not hold (e.g., universal ground-spanning).
- **Superseded:** an additive correction replaces a bounded specification while historical
  records and Git commit digests remain immutable.

Specification layers use integer designations (L0, L1, L2, L3); repository releases use
semantic versions. Released artifacts are frozen.

## Decision rights

Tyler Roost (TimeLordRaps) is the maintainer and primary editor. This is a disclosed
centralization boundary.

The repository's Apache License 2.0 governs the code, specifications, documentation, and
Lean 4 theories.
