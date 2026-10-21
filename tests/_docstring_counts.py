"""Numbers a guard's own docstring states, held to what the guard measures.

Increment 54 built `_states` because four docstrings in
`test_declared_counts.py` stated nine numbers between them and every one of the
nine was wrong. The instrument then lived in that module, and so did all five
of its callers: the tool for holding a docstring's count could reach only the
docstrings in the file that defined it. Every other guard under `tests/` writes
counts into its prose as well, and nothing read any of those.

Three of them were wrong in the same way, and each sat above a floor that
admitted the true value without complaint. `test_layer_boundary` writes
"Sixteen mentions" in one docstring and "refuted sixteen times over" in the
next, under `assert len(comments) >= 16`, with seventeen mentions in the files.
`test_stated_process_rules` writes "five of the eight glosses", under
`assert len(agents) >= 8`, with six of nine --- and the guard directly below it
records, in its own docstring, that the rubric gained a ninth. Two documents
disagreeing is the thing that module exists to catch; two docstrings in it
disagreeing was not something anything could see.

So the instrument moved here, to a module that is not a test and can therefore
be imported by any of them. `test_declared_counts` already imports
`agents_rubric` from `test_stated_process_rules`, so the one module that most
needed `_states` could not have taken it from there without a cycle.
"""
from __future__ import annotations

import re

# Spelled out because the prose guard requires it of these documents, and the
# roster's own total is prose like any other number in them.
NUMBER_NAMES = {
    "twenty": 20, "thirty": 30, "forty": 40, "fifty": 50, "sixty": 60,
    "seventy": 70, "eighty": 80, "ninety": 90,
    "one": 1, "two": 2, "three": 3, "four": 4, "five": 5,
    "six": 6, "seven": 7, "eight": 8, "nine": 9,
    "ten": 10, "eleven": 11, "twelve": 12, "thirteen": 13, "fourteen": 14,
    "fifteen": 15, "sixteen": 16, "seventeen": 17, "eighteen": 18,
    "nineteen": 19,
}


def _spelled(word: str) -> int:
    """A number written in words, as these notes write them.

    This read on hyphens only, and the roster's total line was matched by a
    pattern that allowed one hyphenated word, so together they could say
    `ninety-nine` and nothing above it. The roster stood at ninety-eight. Two
    increments would have taken a document whose whole subject is hand-kept
    numbers going wrong past the largest number it could state, and the failure
    would have arrived as a `KeyError` on the word `hundred` rather than as a
    disagreement about a count.
    """
    value = 0
    for part in re.split(r"[\s-]+", word.strip().lower()):
        if part == "and":
            continue
        if part == "hundred":
            value = (value or 1) * 100
            continue
        value += NUMBER_NAMES[part]
    return value


def _states(doc: str | None, pattern: str, *values: int) -> None:
    """Hold the numbers a guard's own docstring states to the sources.

    Every count in this repository is held to a computation except the ones
    written in the guards that do the holding. Four docstrings in
    `test_declared_counts.py` state what their corpus is, and on 2026-09-21
    every number in all four was wrong: 204 paths were 208, 847 cited
    identifiers were 928, 309 names in the Lean comments were 314, 3,586
    comment lines were 3,624, 52 discharge lines were 54, 89 claims across 22
    documents were 105 across 20. Two of them --- six unresolved paths and
    fifty-one unresolved names --- disagreed with a table twenty lines below
    them that *is* compared exactly, so the guard was holding one number while
    its own prose stated another.

    None of them made anything fail, because each sat above a floor. A count in
    a docstring is a claim like any other, and this is what makes it one.

    A captured group is read as written, so the sentence stays a sentence:
    a thousands separator is dropped, and a number spelled out in words
    goes through `_spelled`, the same table the roster's totals use.
    """
    said = re.search(pattern, " ".join((doc or "").split()))
    assert said, "the sentence this guard measures is gone from its docstring"
    stated = tuple(int(group.replace(",", "")) if group[0].isdigit()
                   else _spelled(group[0].upper() + group[1:])
                   for group in said.groups())
    assert stated == values, ("the docstring says " + repr(said.group(0))
                              + f" --- the sources have {values}")
