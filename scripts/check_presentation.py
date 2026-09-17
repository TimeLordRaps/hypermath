#!/usr/bin/env python3
"""Fail closed when public presentation surfaces drift from executable truth."""

from __future__ import annotations

import argparse
import json
import re
import sys
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote

ROOT = Path(__file__).resolve().parents[1]
IGNORED_PARTS = {
    ".artifacts",
    ".benchmarks",
    ".git",
    ".pytest_cache",
    ".ruff_cache",
    ".venv",
    "__pycache__",
    "build",
    "dist",
    "references",
}
TEXT_SUFFIXES = {
    ".cff",
    ".css",
    ".hm",
    ".html",
    ".json",
    ".jsonl",
    ".lean",
    ".md",
    ".py",
    ".svg",
    ".toml",
    ".txt",
    ".yaml",
    ".yml",
}
MARKDOWN_LINK = re.compile(r"!?\[[^\]]*\]\(([^)]+)\)")

LOCAL_WINDOWS_PATH = re.compile(
    r"(?i)(?:[A-Za-z]:[\\/](?:Users|Documents and Settings)[\\/]|"
    r"\\\\Users[\\/]|[\\/]\.codex[\\/])"
)
DRIVE_QUALIFIED_PATH = re.compile(
    r"(?i)(?<![A-Za-z0-9_%])(?:[A-Za-z]:(?:\\\\|[\\/])[A-Za-z0-9._-]{2,})"
)
PUBLIC_BOUNDARY_PATTERNS = (
    ("local user or home path", LOCAL_WINDOWS_PATH),
    ("drive-qualified local path", DRIVE_QUALIFIED_PATH),
    ("synthetic private locator", re.compile(r"(?i)evaluator-vault://")),
    (
        "private deployment field",
        re.compile(
            r"(?i)\b(?:model_path|launcher_path|mmproj_path|server_path|"
            r"private_target_manifest)\b"
        ),
    ),
    ("local model artifact filename", re.compile(r"(?i)\b[^\s/\\]+\.gguf\b")),
    (
        "business operations identifier",
        re.compile(
            r"(?i)(?:\bPRO" r"SP-[A-Z0-9-]+\b|FIRST" r"_REVENUE|sales[\\/])"
        ),
    ),
    ("private key block", re.compile(r"-----BEGIN [A-Z ]*PRIVATE KEY-----")),
    ("GitHub token shape", re.compile(r"\bgh[pousr]_[A-Za-z0-9_]{20,}\b")),
    ("PyPI token shape", re.compile(r"\bpypi-[A-Za-z0-9_-]{20,}\b")),
    ("AWS access key shape", re.compile(r"\bAKIA[0-9A-Z]{16}\b")),
    ("OpenAI-style secret shape", re.compile(r"\bsk-[A-Za-z0-9_-]{32,}\b")),
)
LINEAGE_CAUSALITY_PATTERNS = (
    (
        "recorded lineage described as causal",
        re.compile(r"(?i)\bcausal\s+(?:lineage|ancestor(?:s)?)\b"),
    ),
    (
        "recorded transformation described as causal",
        re.compile(r"(?i)\bcausal\s+process\b"),
    ),
    (
        "recorded ancestry described as causal contribution",
        re.compile(r"(?i)\bcausally\s+contribut(?:e|ed|es|ing)\b"),
    ),
)


class LinkCollector(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.links: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        for name, value in attrs:
            if name in {"href", "src"} and value:
                self.links.append(value)


def _public_files() -> list[Path]:
    return sorted(
        path
        for path in ROOT.rglob("*")
        if path.is_file()
        and not any(part in IGNORED_PARTS for part in path.relative_to(ROOT).parts)
        and path.suffix.lower() in TEXT_SUFFIXES
    )


def _local_target(source: Path, raw: str) -> Path | None:
    value = raw.strip().strip("<>").split(maxsplit=1)[0]
    if not value or value.startswith(("#", "http://", "https://", "mailto:", "data:")):
        return None
    relative = unquote(value.split("#", 1)[0].split("?", 1)[0])
    if not relative:
        return source
    return (source.parent / relative).resolve()


def check_local_links(errors: list[str]) -> None:
    for source in _public_files():
        suffix = source.suffix.lower()
        if suffix not in {".md", ".html"}:
            continue
        text = source.read_text(encoding="utf-8", errors="replace")
        links: list[str] = []
        if suffix == ".md":
            links.extend(match.group(1) for match in MARKDOWN_LINK.finditer(text))
        elif suffix == ".html":
            parser = LinkCollector()
            parser.feed(text)
            links.extend(parser.links)
        for raw in links:
            target = _local_target(source, raw)
            if target is not None and not target.exists():
                errors.append(
                    f"broken local link in {source.relative_to(ROOT)}: {raw}"
                )


def check_versions(errors: list[str]) -> None:
    pyproject = (ROOT / "pyproject.toml").read_text(encoding="utf-8")
    project_match = re.search(r'^version\s*=\s*"([^"]+)"$', pyproject, re.MULTILINE)
    if project_match is None:
        errors.append("pyproject.toml has no parseable [project] version")
        return
    expected = project_match.group(1)

    init_text = (ROOT / "src/hypermath_foundations/__init__.py").read_text(encoding="utf-8")
    init_match = re.search(r'^__version__\s*=\s*"([^"]+)"$', init_text, re.MULTILINE)

    citation_path = ROOT / "CITATION.cff"
    citation_match = None
    if citation_path.exists():
        citation_match = re.search(
            r"^version:\s*([^\s]+)$", citation_path.read_text(encoding="utf-8"), re.MULTILINE
        )

    zenodo_path = ROOT / ".zenodo.json"
    zenodo_version = None
    if zenodo_path.exists():
        try:
            zenodo_version = json.loads(zenodo_path.read_text(encoding="utf-8")).get("version")
        except json.JSONDecodeError:
            errors.append(".zenodo.json contains invalid JSON")

    changelog_path = ROOT / "CHANGELOG.md"
    changelog = changelog_path.read_text(encoding="utf-8") if changelog_path.exists() else ""

    found = {
        "src/hypermath_foundations/__init__.py": None if init_match is None else init_match.group(1),
        "CITATION.cff": None if citation_match is None else citation_match.group(1),
        ".zenodo.json": zenodo_version,
    }

    for label, version in found.items():
        if version != expected:
            errors.append(f"version mismatch: pyproject={expected}, {label}={version}")

    if not re.search(rf"^## {re.escape(expected)} - \d{{4}}-\d{{2}}-\d{{2}}$", changelog, re.MULTILINE):
        errors.append(f"CHANGELOG.md has no dated {expected} release heading")


def check_claim_boundaries(errors: list[str]) -> None:
    readme_path = ROOT / "README.md"
    if not readme_path.exists():
        errors.append("README.md does not exist")
        return
    readme = readme_path.read_text(encoding="utf-8", errors="replace")
    required_phrases = (
        "A self-derivational mathematical framework built around the operation □",
        "The source does not yet establish an axiom-free executable kernel",
        "proof audit",
    )
    for phrase in required_phrases:
        if phrase not in readme:
            errors.append(f"README.md lacks required claim boundary phrase: {phrase!r}")


def public_boundary_violations(text: str) -> list[str]:
    return [label for label, pattern in PUBLIC_BOUNDARY_PATTERNS if pattern.search(text)]


def lineage_causality_violations(text: str) -> list[str]:
    """Reject phrases that silently upgrade recorded ancestry into causality."""
    return [label for label, pattern in LINEAGE_CAUSALITY_PATTERNS if pattern.search(text)]


def check_public_paths(errors: list[str]) -> None:
    checker = Path(__file__).resolve()
    boundary_checker = ROOT / "scripts/check_release_boundary.py"
    for path in _public_files():
        if path.resolve() in (checker, boundary_checker):
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        for label, pattern in PUBLIC_BOUNDARY_PATTERNS:
            match = pattern.search(text)
            if match:
                line = text.count("\n", 0, match.start()) + 1
                errors.append(
                    f"{label} leaked into {path.relative_to(ROOT)}:{line}"
                )


def check_lineage_claims(errors: list[str]) -> None:
    checker = Path(__file__).resolve()
    for path in _public_files():
        if path.resolve() == checker:
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        for label, pattern in LINEAGE_CAUSALITY_PATTERNS:
            match = pattern.search(text)
            if match:
                line = text.count("\n", 0, match.start()) + 1
                errors.append(f"{label} in {path.relative_to(ROOT)}:{line}")


def run() -> list[str]:
    errors: list[str] = []
    check_local_links(errors)
    check_versions(errors)
    check_claim_boundaries(errors)
    check_public_paths(errors)
    check_lineage_claims(errors)
    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args(argv)

    errors = run()
    if errors:
        for error in errors:
            print(f"[PRESENTATION FAIL] {error}", file=sys.stderr)
        return 1
    print("[PRESENTATION OK] links, versions, and boundary checks pass")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
