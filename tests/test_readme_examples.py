"""Every fenced ``python`` block in README.md is executed, not just read.

The defect this exists to catch is specific, and an import check does not find
it. A README section can name only real symbols -- every import resolving
against ``__all__`` -- while describing constructors, methods and attributes
that do not exist. It then passes the one check a reader applies casually, and
fails the moment anyone runs it.

That is what happened here. A section documenting the library API named 17
symbols, all of which existed, and made 18 claims about their behaviour, of
which 16 were wrong: a constructor taking two arguments that takes none, four
methods that were never defined, an enum member that does not exist, and an
architecture in which one calculus contained the other four when in fact the
five are peers.

So the blocks are executed. Each runs in its own subprocess, and a failure
names the README line the block starts on.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
README = ROOT / "README.md"
SRC = ROOT / "src"

#: Blocks may be added freely; this fails if one is removed or silently
#: relabelled to a non-``python`` fence, which is the cheap way to make a
#: failing example stop being checked.
EXPECTED_MINIMUM_BLOCKS = 6


def _python_blocks() -> list[tuple[int, str]]:
    """Each fenced ``python`` block, with the 1-indexed line it starts on."""
    text = README.read_text(encoding="utf-8")
    blocks: list[tuple[int, str]] = []
    for match in re.finditer(r"```python\n(.*?)```", text, re.DOTALL):
        line = text.count("\n", 0, match.start()) + 1
        blocks.append((line, match.group(1)))
    return blocks


BLOCKS = _python_blocks()


def test_the_readme_still_contains_its_examples() -> None:
    """Guards against the examples being deleted rather than fixed."""
    assert len(BLOCKS) >= EXPECTED_MINIMUM_BLOCKS, (
        f"README.md has {len(BLOCKS)} python blocks, expected at least "
        f"{EXPECTED_MINIMUM_BLOCKS}. Adding examples is fine; removing one means "
        f"editing EXPECTED_MINIMUM_BLOCKS deliberately."
    )


@pytest.mark.parametrize(
    ("line", "body"), BLOCKS, ids=[f"README.md:{line}" for line, _ in BLOCKS]
)
def test_a_readme_example_runs(line: int, body: str) -> None:
    code = f"import sys; sys.path.insert(0, {str(SRC)!r})\n{body}"
    proc = subprocess.run(  # noqa: S603
        [sys.executable, "-c", code],
        capture_output=True,
        text=True,
        cwd=str(ROOT),
    )
    assert proc.returncode == 0, (
        f"the example at README.md:{line} does not run:\n{proc.stderr}"
    )
