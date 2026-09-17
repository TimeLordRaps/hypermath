# Security policy

## Supported release

Only the latest tagged public release on the canonical repository is supported.
Historical releases remain immutable records; corrections are published additively.

## Reporting

Do not place secrets, exploit payloads, or private vulnerability details in a public
issue. Use **Security** → **Report a vulnerability** in the canonical GitHub repository:

`https://github.com/TimeLordRaps/hypermath/security/advisories/new`

If GitHub does not show the private-reporting form, report only the non-sensitive fact
that the private route is unavailable.

## Scope

The reference implementation parses and audits Lean 4 declarations and verifies
mathematical evidence. It does not sandbox arbitrary external code. Run audits and Lake
builds only on checkouts and toolchains you trust.

Report parser vulnerabilities, boundary scanner bypasses, credential leaks, or evidence
forgery risks through the private advisory channel.
