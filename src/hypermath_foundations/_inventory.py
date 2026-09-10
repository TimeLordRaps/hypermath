"""Source inventory; token counts are not a proof checker."""

from __future__ import annotations

import re
from pathlib import Path

SOURCE_PARAMETERS = frozenset({
    "Form", "ground", "f2f", "structContinues", "structDistinct", "structOrbits",
    "Similar", "Congruent", "Simulation", "HMSyntax", "Substance", "Semantics",
    "Derives", "Discharge", "Definition", "FormClosure", "deriver",
    "DerivationPath", "pathStep", "pathGround", "pathLength", "pathTrace",
    "compose", "congruentPath", "pathStart", "pathEnd", "ordinalLimit",
    "ordinalSucc", "finiteApplyFromGround", "ordinalApply",
})


def lean_code(source: str) -> str:
    """Mask nested comments and string literals, retaining line positions."""
    output = list(source)
    index = depth = 0
    in_string = False
    while index < len(source):
        if depth:
            if source.startswith("/-", index):
                output[index:index + 2] = "  "
                depth += 1
                index += 2
            elif source.startswith("-/", index):
                output[index:index + 2] = "  "
                depth -= 1
                index += 2
            else:
                if source[index] != "\n":
                    output[index] = " "
                index += 1
        elif in_string:
            if source[index] == "\\" and index + 1 < len(source):
                output[index:index + 2] = "  "
                index += 2
            else:
                if source[index] == '"':
                    in_string = False
                if source[index] != "\n":
                    output[index] = " "
                index += 1
        elif source.startswith("/-", index):
            output[index:index + 2] = "  "
            depth = 1
            index += 2
        elif source.startswith("--", index):
            end = source.find("\n", index)
            end = len(source) if end < 0 else end
            output[index:end] = " " * (end - index)
            index = end
        elif source[index] == '"':
            in_string = True
            output[index] = " "
            index += 1
        else:
            index += 1
    return "".join(output)


def inventory(root: Path) -> tuple[list[dict], list[dict]]:
    admissions, assumptions = [], []
    for path in sorted((root / "lean4" / "Hypermath").rglob("*.lean")):
        code = lean_code(path.read_text(encoding="utf-8-sig"))
        relative = path.relative_to(root).as_posix()
        for match in re.finditer(r"\b(?:sorry|sorryAx|admit)\b", code):
            admissions.append({"path": relative, "line": code.count("\n", 0, match.start()) + 1,
                               "token": match.group()})
        for match in re.finditer(r"(?m)^\s*axiom\s+([^\s:]+)", code):
            name = match.group(1)
            assumptions.append({
                "name": f"Hypermath.{name}", "path": relative,
                "line": code.count("\n", 0, match.start(1)) + 1,
                "kind": "source_parameter" if name in SOURCE_PARAMETERS else "logical_axiom",
            })
    return admissions, assumptions
