"""Check imported file identities and the local source-map bindings.

This checks provenance bytes and file paths, not mathematical correctness.
"""

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    manifest = json.loads((ROOT / "references/seed-ai/manifest.json").read_text(encoding="utf-8"))
    copied = 0
    seen = set()
    for record in manifest["records"]:
        assert record["source"] not in seen, record["source"]
        seen.add(record["source"])
        if record["disposition"] == "reference_snapshot":
            path = (ROOT / record["destination"]).resolve(strict=True)
            assert path.is_relative_to(ROOT / "references/seed-ai")
            data = path.read_bytes()
            assert len(data) == record["bytes"], path
            assert hashlib.sha256(data).hexdigest() == record["sha256"], path
            assert (ROOT / record["maps_to"]).exists(), record["maps_to"]
            if "excerpt" not in record:
                assert record["sha256"] == record["source_sha256"], path
            copied += 1
            print(f"PASS identity and target: {record['destination']}", flush=True)
        elif "alias_of" in record:
            canonical = ROOT / record["alias_of"]
            assert hashlib.sha256(canonical.read_bytes()).hexdigest() == record["source_sha256"]
            print(f"PASS duplicate alias: {record['source']}", flush=True)
    assert copied == 20
    print(f"Checked {copied} snapshots and {len(seen)} source records; mathematical status unchanged.", flush=True)


if __name__ == "__main__":
    main()
