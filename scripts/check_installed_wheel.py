"""Check imports and representative calls from a clean, non-editable wheel install."""

from __future__ import annotations

import argparse
import subprocess
import sys
import tempfile
import venv
from pathlib import Path


def run(command: list[str], *, cwd: Path, timeout: int = 180) -> None:
    print(f"START installed-wheel check: {Path(command[0]).name} {' '.join(command[1:3])}",
          flush=True)
    subprocess.run(command, cwd=cwd, check=True, timeout=timeout)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wheel-dir", type=Path, default=Path("dist"))
    parser.add_argument("--foundation-wheel-dir", type=Path)
    parser.add_argument("--package", choices=("hypermath_foundations", "ordinatics"),
                        default="hypermath_foundations")
    args = parser.parse_args()
    wheels = sorted(args.wheel_dir.resolve().glob("*.whl"))
    if len(wheels) != 1:
        raise SystemExit("Expected exactly one subject wheel")
    requirements = [str(wheels[0])]
    if args.foundation_wheel_dir:
        foundations = sorted(args.foundation_wheel_dir.resolve().glob("*.whl"))
        if len(foundations) != 1:
            raise SystemExit("Expected exactly one pinned foundation wheel")
        requirements.insert(0, str(foundations[0]))
    with tempfile.TemporaryDirectory(prefix="installed-wheel-") as temporary:
        root = Path(temporary)
        environment = root / "environment"
        venv.EnvBuilder(with_pip=True).create(environment)
        python = environment / ("Scripts/python.exe" if sys.platform == "win32" else "bin/python")
        run([str(python), "-m", "pip", "install", "--only-binary=:all:", *requirements], cwd=root)
        run([str(python), "-m", "pip", "check"], cwd=root)
        probe = (
            "import importlib, pathlib, sys; "
            f"module=importlib.import_module({args.package!r}); "
            "assert pathlib.Path(module.__file__).resolve().is_relative_to("
            "pathlib.Path(sys.prefix).resolve()), 'import did not come from the isolated environment'; "
        )
        if args.package == "hypermath_foundations":
            probe += "assert module.evaluate_gate({}) is False; "
        else:
            probe += (
                "assert 1 + module.OMEGA == module.OMEGA; "
                "assert module.OMEGA + 1 > module.OMEGA; "
                "assert callable(module.verify_grounding); "
            )
        probe += f"print('PASS: installed {args.package} wheel is importable and usable')"
        run([str(python), "-I", "-c", probe], cwd=root, timeout=30)


if __name__ == "__main__":
    main()
