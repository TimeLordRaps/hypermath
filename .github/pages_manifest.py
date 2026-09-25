"""Record exactly what was built, so that what was deployed can be checked.

This is the portable half of verifier's promotion receipt. verifier validates
its deployment against a component index that exists in one repository; what
generalises is cheaper and still load-bearing: the source commit, plus a
SHA-256 of every byte of the built site. The deploying workflow fetches this
file back from the live site afterwards and compares. If they differ, what is
being served is not what passed the gate.

It walks the built directory rather than being emitted by the builder, so it
works over a repository's own `scripts/build_pages.py` as readily as over the
shared fallback -- and those builders were written before this existed and
take no arguments for it.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import sys


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("site", type=pathlib.Path)
    parser.add_argument("--source-ref", required=True)
    parser.add_argument("--repository", default="")
    parser.add_argument("--builder", default="")
    options = parser.parse_args()

    site = options.site
    if not site.is_dir():
        print(f"no built site at {site}", file=sys.stderr)
        return 1

    destination = site / "deployment-manifest.json"
    files: dict[str, str] = {}
    for path in sorted(site.rglob("*")):
        if not path.is_file() or path == destination:
            continue
        relative = path.relative_to(site).as_posix()
        files[relative] = hashlib.sha256(path.read_bytes()).hexdigest()

    if not files:
        print(f"the built site at {site} is empty", file=sys.stderr)
        return 1

    # Jekyll drops every path beginning with an underscore unless told not to.
    # Written before the manifest is, so that it is covered by the manifest.
    nojekyll = site / ".nojekyll"
    if not nojekyll.exists():
        nojekyll.write_bytes(b"")
        files[".nojekyll"] = hashlib.sha256(b"").hexdigest()

    manifest = {
        "source_ref": options.source_ref,
        "repository": options.repository,
        "builder": options.builder,
        "file_count": len(files),
        "files": dict(sorted(files.items())),
    }
    serialized = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    destination.write_text(serialized, encoding="utf-8")

    digest = hashlib.sha256(serialized.encode("utf-8")).hexdigest()
    print(f"manifest covers {len(files)} file(s) built by {options.builder}")
    print(digest)
    return 0


if __name__ == "__main__":
    sys.exit(main())
