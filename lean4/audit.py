"""Compatibility entry point; exit 2 still means admitted proofs remain.

Install hypermath-foundations or run this wrapper from its source checkout.
The structured report separates compilation, admissions, and mathematical claims.
"""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
try:
    from hypermath_foundations.__main__ import legacy_main
except ModuleNotFoundError as error:
    if error.name != "hypermath_foundations":
        raise
    sys.path.insert(0, str(ROOT / "src"))
    from hypermath_foundations.__main__ import legacy_main

if __name__ == "__main__":
    raise SystemExit(legacy_main(ROOT))
