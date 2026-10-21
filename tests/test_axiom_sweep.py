"""The axiom sweep and the table the audit checks it against.

Thirteen Lean files end in a run of `#print axioms` lines, and for each of them
the audit holds the printed records against a pinned tuple of names. That
comparison is exact in both directions: a record with no pinned name and a
pinned name with no record both raise `missing or unexpected dependency
records`, which is not a failing check but the end of the run --- the probe that
raised it is marked FAIL and every probe after it is left UNKNOWN.

Nothing here could see that. The Python suite stubs `lake`, so it never reads a
sweep's output, and the thing standing between an edit to a swept file and a
broken audit was the reviewed-source digest, which is a different kind of guard
than it looks like: it fires on *every* edit to the file, so it reports nothing
about any particular edit. Refreshing it is what reviewing the file means. On
2026-09-21 three theorems were added to `Countermodels.lean` with three sweep
lines and nothing on this side at all: no pinned records, no bump to the cost
count, no change to the verification row. Those three Python facts are checked
against each other, so leaving all three out keeps them agreeing --- at a number
the Lean file had stopped having. Leaving out only the records is caught in a
second, by the other two. The digest was refreshed because the file had in fact
been read, the suite was green at 567 passed, and the audit could not complete.

What the two guards below add is the same comparison made without Lean --- or
rather, a necessary condition for it. The audit compares names Lean resolved;
these compare the names the files *ask* Lean to print, resolved by a rule of
their own. Matching cannot prove the audit will agree. Failing to match proves
it will not.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
if str(REPO / "src") not in sys.path:
    sys.path.insert(0, str(REPO / "src"))

#: A sweep line, alone on its line at column zero, as every one of them is.
SWEEP = re.compile(r"^#print axioms\s+([A-Za-z_][\w.']*)\s*$", re.M)
#: One row of the probe table in `audit.py`: the probe's name and its file.
COMMAND = re.compile(
    r'^\s*"(\w+)":\s*\[executable,\s*"env",\s*"lean",\s*"([\w.]+\.lean)"\],\s*$',
    re.M)
#: The one command in that table that runs no file and prints no records.
NOT_A_SWEEP = "lean_build"
#: Lean under these directories is built output or history, not a probe's
#: subject, and a sweep line there is not a claim about anything.
UNRUN = ("build", ".lake", "history", "references", "node_modules")
#: The probe whose tuple is named separately because the audit reads more than
#: the records out of it: the target's kind, its statement, and the transitive
#: admissions all come from this one run.
MAIN_PROBE = "dependency_output"


def _probe_files() -> dict[str, str]:
    """Probe name to the Lean file it runs, read out of the audit itself."""
    source = (REPO / "src" / "hypermath_foundations" / "audit.py").read_text(
        encoding="utf-8")
    table = dict(COMMAND.findall(source))
    assert NOT_A_SWEEP in source, "the probe table no longer builds first"
    return table


def _pins() -> dict[str, tuple[str, ...]]:
    from hypermath_foundations._reports import DEPENDENCY_TARGETS, PROBE_TARGETS

    return {MAIN_PROBE: DEPENDENCY_TARGETS, **PROBE_TARGETS}


def _lean_files() -> list[Path]:
    return [path for path in sorted((REPO / "lean4").rglob("*.lean"))
            if not any(part in UNRUN for part in path.parts)]


def _swept(path: Path) -> list[str]:
    return SWEEP.findall(path.read_text(encoding="utf-8"))


def _resolve(short: str, pinned: tuple[str, ...]) -> tuple[str | None, list[str]]:
    """The pinned name a sweep line names, or the candidates it cannot choose
    between.

    A sweep line is written relative to whatever namespaces are open where it
    stands, and the pinned name is fully qualified, so the two differ by a
    prefix. Three namespaces in `Countermodels.lean` each declare a
    `prefixAxioms_hold`, so the bare line matches four pinned names; the one
    with the fewest segments in front of it is the one an outer sweep line
    means, and the three inner ones are written with their namespace and match
    one each. That rule is not Lean's --- Lean resolves inwards from where the
    line stands, and this resolves outwards from the name --- which is why an
    ambiguity it cannot settle is reported rather than guessed.
    """
    hits = [full for full in pinned
            if full == short or full.endswith("." + short)]
    if not hits:
        return None, []
    depth = min(full[:-len(short)].count(".") for full in hits)
    best = [full for full in hits if full[:-len(short)].count(".") == depth]
    return (best[0], []) if len(best) == 1 else (None, best)


def test_every_probe_runs_a_swept_file_and_every_sweep_is_a_probe() -> None:
    """The three sets that have to be the same size, and are not checked to be.

    There are probes, there are pinned tuples, and there are files that end in a
    sweep. The audit pairs the first two by name and the first and third by the
    command it runs; nothing pairs the second and third, and nothing says the
    third has no extra member. A sweep added to a file no probe runs is printed
    by nobody and compared against nothing, which is the quietest way for one of
    these lists to be wrong: the lines are there, they look exactly like the
    lines that are checked, and no run ever reads them.
    """
    files = _probe_files()
    pins = _pins()

    assert NOT_A_SWEEP not in files, (
        "the build command now looks like a file probe: " + NOT_A_SWEEP)
    assert set(files) == set(pins), {
        "runs a file and has no pinned tuple": sorted(set(files) - set(pins)),
        "has a pinned tuple and runs no file": sorted(set(pins) - set(files))}

    twice = sorted({name for name in files.values()
                    if list(files.values()).count(name) > 1})
    assert not twice, "two probes run the same file: " + ", ".join(twice)

    missing = [name for name in files.values()
               if not (REPO / "lean4" / name).is_file()]
    assert not missing, "probes naming a file that is not there: " + ", ".join(
        missing)

    run = {(REPO / "lean4" / name).resolve() for name in files.values()}
    stray = sorted(path.relative_to(REPO).as_posix() for path in _lean_files()
                   if _swept(path) and path.resolve() not in run)
    assert not stray, (
        "files ending in a sweep that no probe runs, so the lines are printed "
        "by nobody:\n" + "\n".join(stray))

    empty = sorted(name for name in files.values()
                   if not _swept(REPO / "lean4" / name))
    assert not empty, (
        "probes whose file has no sweep at all, so the tuple is compared "
        "against nothing:\n" + "\n".join(empty))


def test_every_swept_theorem_has_a_pinned_record() -> None:
    """A sweep line with no pinned name ends the audit, and the suite is green.

    The pairing has to be exact in both directions, because both directions end
    the run: an unpinned line makes a record the tuple does not expect, and a
    pinned name whose line was deleted makes a record the tuple expects and does
    not get. The audit says the same thing for both --- `missing or unexpected
    dependency records` --- and stops.

    Two things this does not claim. It reads the names the files ask for, not
    the names Lean resolves them to, so agreement here is necessary for the
    audit's comparison and not sufficient for it. And it says nothing about what
    the sweep reports: whether a theorem is axiom-free, and what it costs if it
    is not, is the pinned dependency table's business and is held elsewhere.
    """
    files = _probe_files()
    pins = _pins()

    total = 0
    for probe, name in sorted(files.items()):
        path = REPO / "lean4" / name
        lines = _swept(path)
        pinned = pins[probe]
        total += len(lines)

        repeats = sorted({line for line in lines if lines.count(line) > 1})
        assert not repeats, (
            f"{name} asks for the same record twice, which the reader rejects "
            "before it compares anything: " + ", ".join(repeats))

        taken: dict[str, str] = {}
        unmatched: list[str] = []
        ambiguous: list[str] = []
        for line in lines:
            full, candidates = _resolve(line, pinned)
            if full is None:
                target = ambiguous if candidates else unmatched
                target.append(f"{line} -> {candidates}" if candidates else line)
                continue
            taken[full] = line

        assert not unmatched, (
            f"{name} sweeps names that {probe}'s tuple does not pin, so the "
            "audit ends at this probe and every probe after it is left "
            "UNKNOWN:\n  " + "\n  ".join(unmatched))
        assert not ambiguous, (
            f"{name} sweeps a name that matches more than one pinned name at "
            "the same depth, so which record it makes cannot be read off the "
            "file:\n  " + "\n  ".join(ambiguous))

        orphan = [full for full in pinned if full not in taken]
        assert not orphan, (
            f"{probe} pins names that {name} no longer sweeps, so the audit "
            "waits for records that never come:\n  " + "\n  ".join(orphan))

        assert len(taken) == len(pinned) == len(lines), (
            name, len(taken), len(pinned), len(lines))

    assert total > 1000, total
