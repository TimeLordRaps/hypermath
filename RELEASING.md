# Release procedure

Public releases are built only from a commit already present on the canonical public repository.
The release manifest is published beside the source ZIP rather than tracked inside the
source tree. This avoids a self-referential commit field and lets the manifest bind an
exact, publicly resolvable commit.

1. Merge the versioned release change through the public pull-request workflow. Require
   every protected conformance check on the exact candidate commit.
2. From a clean checkout of that commit, run:

   ```bash
   python -m pytest -q
   python -m compileall -q src scripts
   ```

3. Build a pre-tag candidate from the full commit SHA, not an arbitrary working directory:

   ```bash
   VERSION=0.1.0
   python scripts/release_artifacts.py build \
     --ref FULL_PUBLIC_COMMIT_SHA --release "$VERSION" --output-dir dist/candidate
   ```

   The builder uses `git archive`, records exact Git-blob member bytes, and rewrites the
   source ZIP with a UTC commit timestamp, stable Unix modes, sorted members, and stored
   compression. It builds both the wheel and standard source distribution twice from
   separate source extractions with `SOURCE_DATE_EPOCH` set to the commit timestamp.
   Generated packaging text is normalized to LF; wheel `RECORD` is rebuilt after
   normalization; ZIP metadata, tar metadata, gzip metadata, ownership, modes, and member
   order are canonical. The build fails unless each pair is byte-identical and both
   distributions declare `hypermath-foundations`, the release version, import package
   `hypermath_foundations`, and the declared console scripts.

   The protected conformance gate separately builds this complete artifact set on
   Windows and Linux and compares every byte. Do not prepare a tag unless that
   cross-platform comparison passed on the exact candidate commit.

4. Run `twine check` on the candidate wheel and source distribution.
   Run `scripts/check_installed_wheel.py` with `--wheel-dir dist/candidate`.
5. Require a zero-match boundary scan of the candidate source archive, wheel, and source
   distribution:

   ```bash
   python scripts/check_release_boundary.py dist/candidate/*.zip dist/candidate/*.whl dist/candidate/*.tar.gz
   ```

6. Create the release tag locally at the exact tested commit. Prefer a cryptographically
   signed annotated tag (`git tag -s`). Rebuild using the tag coordinate:

   ```bash
   VERSION=0.1.0
   git tag -s "v$VERSION" FULL_PUBLIC_COMMIT_SHA
   python scripts/release_artifacts.py build \
     --ref "refs/tags/v$VERSION" --release "$VERSION" --output-dir dist/tagged
   ```

7. Run the verifier independently before upload:

   ```bash
   VERSION=0.1.0
   python scripts/release_artifacts.py verify \
     "dist/tagged/hypermath-foundations-$VERSION.manifest.json"
   ```

8. Push the tag only after all preceding checks pass. The tag-triggered release workflow
   rechecks protected-main ancestry, package version, the successful `conformance-gate`,
   the full test suite, deterministic build, installed wheel, and artifact manifest.
   It then attests and publishes exactly the tested source ZIP, wheel, source distribution,
   and external release manifest to the GitHub release. A second job accesses only the
   wheel and source distribution, requires approval in the protected `pypi` environment,
   and publishes them through PyPI Trusted Publishing.
9. Verify each downloaded asset with both the external manifest and:

   ```bash
   gh attestation verify PATH_TO_ASSET --repo TimeLordRaps/hypermath
   ```
