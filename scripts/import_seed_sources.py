"""Capture an explicit mathematical allowlist from an existing Seed-ai folder.

Source files remain untouched. Existing differing snapshots are never overwritten.
The manifest records original and imported byte identities, including excerpts.
"""

import argparse
import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PREFIX = Path("references/seed-ai")
CHAPTERS = "hyper-grammar/docs/prerequisites/"
SELECTED = {
    "hypermath/spec/axioms.hm": ("earlier specification", "L0_ground.hm"),
    "hypermath/spec/casting.hm": ("design proposal", "L1_relations.hm"),
    "hypermath/spec/links.hm": ("design proposal", "L1_relations.hm"),
    "hypermath/spec/verify.hm": ("checker specification; not executable", "lean4/"),
    "hypermath_form/ground.hm": ("earlier layered presentation", "L0_ground.hm"),
    "hypermath_form/relations.hm": ("earlier layered presentation", "L1_relations.hm"),
    "hypermath_form/operations.hm": ("earlier layered presentation", "L2_operations.hm"),
    "hypermath_form/ordinatics.hm": ("earlier layered presentation", "L3_ordinatics.hm"),
    "hypermath_form/kernel.hm": ("proposed Metamath correspondence", "lean4/"),
    "hypermath_frame/spec/kernel.hm": ("checker design and explicit limits", "lean4/"),
    "hypermath_frame/spec/ordinatics.hm": ("value-layer design proposal", "L3_ordinatics.hm"),
    "hypermath_frame/spec/stdlib/hyperordinal.hm": ("path/value design proposal", "L3_ordinatics.hm"),
    CHAPTERS + "24_fractal_hypergrammar_compression.md": ("fractal proposal; compression unproved", "docs/research/FRACTAL_COMPLETENESS.md"),
    CHAPTERS + "36_meta_closure.md": ("bounded mathematical excerpt", "docs/research/FRACTAL_COMPLETENESS.md"),
    CHAPTERS + "45_hyper_information_theory.md": ("proposal with numerical errors", "docs/research/PROOF_AUDIT.md"),
    CHAPTERS + "46_hypergrammar_and_godel.md": ("historical argument with coding error", "docs/research/PROOF_AUDIT.md"),
    CHAPTERS + "47_hypermath.md": ("explicit open research target", "docs/research/FRACTAL_COMPLETENESS.md"),
    CHAPTERS + "97_ordinate_hierarchy_ordinatics_ordinetics_ordinaretics.md": ("hierarchy design proposal", "L3_ordinatics.hm"),
    CHAPTERS + "98_dimensional_transition_operators.md": ("open operator proposal with operation mismatch", "L3_ordinatics.hm"),
    CHAPTERS + "99_language_calculus_downstream_closures.md": ("downstream gaps; not proof authority", "docs/research/PROOF_AUDIT.md"),
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", required=True, type=Path)
    args = parser.parse_args()
    source_root = args.source_root.resolve(strict=True)
    manifest_path = ROOT / PREFIX / "manifest.json"
    if manifest_path.exists():
        raise SystemExit("Manifest already exists; compare a fresh import in a new snapshot")
    remote = subprocess.run(
        ["git", "remote", "get-url", "origin"], cwd=ROOT, check=True,
        capture_output=True, text=True, timeout=15,
    ).stdout.strip().removesuffix(".git")
    if remote != "https://github.com/TimeLordRaps/hypermath":
        raise SystemExit("Unexpected destination repository")
    records = []
    for relative, (classification, target) in SELECTED.items():
        source = (source_root / relative).resolve(strict=True)
        if not source.is_relative_to(source_root) or not source.is_file():
            raise SystemExit(f"Source escapes root or is not a file: {relative}")
        original = source.read_bytes()
        imported = original
        destination = PREFIX / relative
        record = {
            "source": relative, "source_sha256": digest(original),
            "source_bytes": len(original), "classification": classification,
            "maps_to": target, "disposition": "reference_snapshot",
        }
        if relative.endswith("36_meta_closure.md"):
            destination = PREFIX / "hyper-grammar/36_meta_closure.math-excerpt.md"
            lines = original.decode("utf-8").splitlines(keepends=True)
            imported = "".join(lines[42:149]).encode("utf-8")
            record["excerpt"] = {"first_line": 43, "last_line": 149, "numbering": "one-based inclusive"}
        output = (ROOT / destination).resolve()
        if not output.is_relative_to(ROOT / PREFIX):
            raise SystemExit("Destination escapes snapshot directory")
        if output.exists() and output.read_bytes() != imported:
            raise SystemExit(f"Refusing to overwrite differing snapshot: {destination}")
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(imported)
        record.update(destination=destination.as_posix(), sha256=digest(imported), bytes=len(imported))
        records.append(record)
        print(f"Captured {relative}", flush=True)

    # Account for the remaining mathematical files without importing applications.
    for family in ("hypermath", "hypermath_form", "hypermath_frame"):
        for source in sorted((source_root / family).rglob("*.hm")):
            relative = source.relative_to(source_root).as_posix()
            if relative in SELECTED:
                continue
            data = source.read_bytes()
            record = {
                "source": relative, "source_sha256": digest(data),
                "source_bytes": len(data), "disposition": "mapped_without_copy",
                "classification": "application or terminology backlog",
            }
            if relative == "hypermath_frame/spec/axioms.hm":
                canonical = next(r for r in records if r["source"] == "hypermath/spec/axioms.hm")
                if record["source_sha256"] != canonical["source_sha256"]:
                    raise SystemExit("Expected duplicate axioms now differ; inspect before mapping")
                record.update(classification="byte-identical duplicate", alias_of=canonical["destination"])
            records.append(record)

    manifest = {
        "schema_version": 1,
        "captured_at_utc": datetime.now(timezone.utc).isoformat(),
        "source_root_label": "Seed-ai local working files",
        "status": "reference material; source closure labels are not proof verification",
        "records": records,
        "excluded_categories": ["personal and clinical notes", "business and political material", "generated scaffolds", "archives", "nul device entries", "historical TIME ledger"],
    }
    manifest_path.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"Captured {len(SELECTED)} inputs; mapped {len(records)} records", flush=True)


if __name__ == "__main__":
    main()
