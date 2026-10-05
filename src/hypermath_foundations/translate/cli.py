"""`hypermath-foundations translate FILE.hm… --out DIR [--lean BIN] [--mmverify PATH]`.

Files must be given in dependency order. Also runnable as
`python -m hypermath_foundations.translate`.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

from . import lean, lint, metamath, project, receipt


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="hypermath-foundations translate", description=__doc__)
    ap.add_argument("files", nargs="+", type=Path)
    ap.add_argument("--out", type=Path)
    ap.add_argument("--lean", help="path to a `lean` binary; enables kernel checking")
    ap.add_argument("--mmverify", help="path to mmverify.py; enables Metamath output")
    ap.add_argument("--namespace", default="Hypermath")
    ap.add_argument("--lint", action="store_true", help="print source defects and exit; --out not required")
    ap.add_argument("--drift", type=Path, metavar="LEAN_DIR",
                    help="compare each derive's tag with hand-written Lean files in LEAN_DIR; print and exit")
    a, _ = ap.parse_known_args(argv)
    proj = project.analyze([(f.name, f.read_text(encoding="utf-8")) for f in a.files])
    if a.drift:
        from . import drift
        rows = drift.drift(proj, [p.read_text(encoding="utf-8") for p in sorted(a.drift.rglob("*.lean")) if ".lake" not in p.parts])
        for r in rows:
            mark = "DISAGREES" if r["disagrees"] else "ok"
            print(f"{mark:9s} {r['file']}:{r['line']:<4d} {r['derive']:36s} .hm={r['hm_tag']:5s} lean={r['lean']}")
        print(drift.summary(rows))
        return 0
    if a.lint:
        print(lint.format_report(lint.lint(proj)))
        return 0
    if a.out is None:
        ap.error("--out is required unless --lint is given")
    a.out.mkdir(parents=True, exist_ok=True)
    lean_text, log, ver = None, [], None
    if a.lean:
        out, log = lean.kernel_check(proj, a.lean, a.namespace)
        lean_text = out.text
        (a.out / "Out.lean").write_text(lean_text, encoding="utf-8")
        ver = subprocess.run([a.lean, "--version"], capture_output=True, text=True).stdout.strip()
    else:
        print("note: no --lean given; nothing was kernel-checked and no Lean file was written", file=sys.stderr)
    mm_text, mm_status = None, None
    if a.mmverify:
        mm_text, mm_status = metamath.emit_checked(proj, a.mmverify)
        (a.out / "out.mm").write_text(mm_text, encoding="utf-8")
    rec = receipt.build(proj, lean_text, log, mm_text, mm_status, ver, a.mmverify)
    (a.out / "receipt.json").write_text(json.dumps(rec, indent=1, ensure_ascii=False), encoding="utf-8")
    for k, n in rec["counts"].items():
        print(f"{n:4d}  {k}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
