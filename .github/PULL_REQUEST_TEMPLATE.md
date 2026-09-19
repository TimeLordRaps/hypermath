## Coordinate

- Hypermath layer (L0-L3) or formal feature:
- Repository release or target commit:
- Claim, Lean 4 theory, or implementation seam:

## Change and evidence

- What changes:
- What does not change:
- Falsification condition or countermodel:
- Tests added or updated:
- Lake / Lean 4 verification result:

## Consequences

- Kernel assumption policy impact (reviewed allowance unchanged):
- Trust roots, unknowns, residuals, and horizons:
- Downstream documents, proofs, and examples reviewed:

## Test skip rubric disclosure

To prevent skip slippage, every skipped test or unrun check MUST disclose reasoning clearing this rubricized checklist of definitional terms:

- [ ] `OS_CAPABILITY_GUARD`: Underlying operating system capability absent.
- [ ] `OPTIONAL_DEPENDENCY_ABSENT`: Non-core dependency or optional extra absent.
- [ ] `EXTERNAL_SERVICE_BOUNDARY`: Live network, external daemon, or remote service unavailable.
- [ ] `ARCHITECTURAL_PLATFORM_UNSUPPORTED`: Target processor architecture or endianness unsupported.
- [ ] `HARDWARE_DEVICE_UNAVAILABLE`: Physical accelerator or specialized hardware absent.
- [ ] `PRIVILEGE_OR_CREDENTIAL_BOUNDARY`: Elevated permissions or secret keys absent.
- [ ] `PERFORMANCE_OR_DURATION_EXCLUSION`: Long-running stress or benchmark excluded from default pass.
- [ ] `QUARANTINED_DEFECT`: Known tracked issue isolated under active quarantine.
- [ ] `NOT_APPLICABLE`: Zero tests or checks were skipped (clean full-suite run).

| Check / Test Target | Category | Bounded Reason | Claim Consequence |
|---|---|---|---|
| <!-- target --> | <!-- category --> | <!-- reason --> | <!-- consequence --> |

## Checklist

- [ ] I did not turn `UNKNOWN` or `CONFLICTED` into a clean result.
- [ ] I did not add unreviewed axioms to the kernel assumption policy.
- [ ] I did not strengthen a claim without stronger machine-checked evidence.
- [ ] I did not include secrets, private data, or drive-qualified paths.
- [ ] Python test suite (`pytest -q`) and Lean 4 build (`lake build`) both succeed, with all skips justified against the rubric.
