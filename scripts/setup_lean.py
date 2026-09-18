"""Install the pinned Linux CI toolchain from a digest-checked Elan release."""

from __future__ import annotations

import hashlib
import io
import os
import platform
import subprocess
import tarfile
from pathlib import Path
from urllib.request import urlopen

ROOT = Path(__file__).resolve().parents[1]
URL = (
    "https://github.com/leanprover/elan/releases/download/v4.2.4/"
    "elan-x86_64-unknown-linux-gnu.tar.gz"
)
SHA256 = "42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63"


def main() -> None:
    if platform.system() != "Linux" or platform.machine() not in {"x86_64", "AMD64"}:
        raise SystemExit("This installer targets Linux x86-64 CI; use Elan locally.")
    destination = ROOT / "build" / "elan"
    destination.mkdir(parents=True, exist_ok=True)
    print("Downloading Elan 4.2.4; checking the published archive digest", flush=True)
    with urlopen(URL, timeout=60) as response:
        archive = response.read(20_000_001)
    if len(archive) > 20_000_000 or hashlib.sha256(archive).hexdigest() != SHA256:
        raise SystemExit("Elan archive size or digest mismatch")
    with tarfile.open(fileobj=io.BytesIO(archive), mode="r:gz") as bundle:
        member = bundle.getmember("elan-init")
        if not member.isfile():
            raise SystemExit("Expected a regular elan-init executable")
        stream = bundle.extractfile(member)
        if stream is None:
            raise SystemExit("Missing elan-init executable")
        executable = destination / "elan-init"
        executable.write_bytes(stream.read())
        executable.chmod(0o755)
    elan_home = destination / "home"
    environment = dict(os.environ, ELAN_HOME=str(elan_home))
    subprocess.run(
        [str(executable), "-y", "--no-modify-path", "--default-toolchain", "none"],
        check=True, env=environment, timeout=120,
    )
    toolchain = (ROOT / "lean4" / "lean-toolchain").read_text().strip()
    print(f"Installing the repository toolchain: {toolchain}", flush=True)
    subprocess.run(
        [str(elan_home / "bin" / "elan"), "toolchain", "install", toolchain],
        check=True, env=environment, timeout=300,
    )
    if "GITHUB_PATH" in os.environ:
        with open(os.environ["GITHUB_PATH"], "a", encoding="utf-8") as output:
            output.write(str(elan_home / "bin") + "\n")
        with open(os.environ["GITHUB_ENV"], "a", encoding="utf-8") as output:
            output.write(f"ELAN_HOME={elan_home}\n")
    print("Pinned Lean toolchain installed", flush=True)


if __name__ == "__main__":
    main()
