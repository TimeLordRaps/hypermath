"""Rules this repository states about its own work, applied to its own work.

`AGENTS.md` §8 says that every skipped test MUST disclose its rationale against
a rubric of definitional categories, and `.github/PULL_REQUEST_TEMPLATE.md`
states the same rubric for the pull request that carries the skip.  Nothing
read either document.  Every other guard in this suite holds the prose to the
sources; these hold the sources to the prose, which is the same claim from the
other side and had no guard at all.

When the rule was first applied, all three of this repository's own skips
failed it -- two of them for a reason the rubric had no category for.
"""

from __future__ import annotations

import ast
import re
from pathlib import Path

from _docstring_counts import _states

REPO = Path(__file__).resolve().parents[1]
AGENTS = REPO / "AGENTS.md"
TEMPLATE = REPO / ".github" / "PULL_REQUEST_TEMPLATE.md"

#: A rubric entry: a name in code style, then its definition.
RUBRIC_ENTRY = re.compile(r"`([A-Z][A-Z0-9_]+)`\s*:\s*(.+?)\s*$")

#: The template carries one entry that is not a category: the box a pull
#: request ticks when it skipped nothing at all.  A marker for the empty case
#: is not a kind of skip, and counting it as one would make "every skip names a
#: category" satisfiable by a run that skipped nothing.
NOT_A_CATEGORY = "NOT_APPLICABLE"


def _rubric(path: Path, marker: re.Pattern[str]) -> dict[str, str]:
    """The categories a document states, by name, with what it says each means."""
    found: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if not marker.match(line.strip()):
            continue
        entry = RUBRIC_ENTRY.search(line)
        if entry:
            found[entry.group(1)] = entry.group(2)
    return found


def agents_rubric() -> dict[str, str]:
    return _rubric(AGENTS, re.compile(r"^\d+\.\s+`"))


def template_rubric() -> dict[str, str]:
    return _rubric(TEMPLATE, re.compile(r"^- \[ \] `"))


def _skips() -> list[tuple[str, int, str]]:
    """(file, line, reason) for every skip this repository takes.

    Read from the syntax tree rather than by matching text, because a skip is a
    call and a decorator, not a line.  `pytest.skip(reason)`,
    `@pytest.mark.skip(reason=...)` and `@pytest.mark.skipif(cond, reason=...)`
    are the three shapes, and a reason that is not a literal is itself a
    failure to disclose: a category assembled at runtime is not one a reader of
    the source can check.
    """
    found: list[tuple[str, int, str]] = []
    for path in sorted(REPO.glob("tests/*.py")) + sorted(
            REPO.glob("src/**/*.py")):
        relative = path.relative_to(REPO).as_posix()
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=relative)
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            name = ast.unparse(node.func)
            if name not in ("pytest.skip", "pytest.mark.skip",
                            "pytest.mark.skipif", "pytest.xfail"):
                continue
            reason = next(
                (keyword.value for keyword in node.keywords
                 if keyword.arg == "reason"), None)
            if reason is None and node.args and name in ("pytest.skip",
                                                         "pytest.xfail"):
                reason = node.args[0]
            said = (reason.value if isinstance(reason, ast.Constant)
                    else "" if reason is None
                    # An f-string's literal parts are the part a reader can
                    # check; the interpolations are the bounded reason.
                    else "".join(piece.value for piece in reason.values
                                 if isinstance(piece, ast.Constant))
                    if isinstance(reason, ast.JoinedStr) else "")
            found.append((relative, node.lineno, said))
    return found


def test_the_skip_rubric_is_stated_the_same_way_twice() -> None:
    """Two documents state this vocabulary, and nothing compared them.

    A vocabulary written down twice is two claims, and the second one is free
    to drift. These two have not drifted in the names, which is what a category
    is; six of the nine glosses are worded differently between the documents,
    and that is prose rather than rot, so the names are what this holds.

    This said five of eight, above a floor of eight. The rubric had gained a
    ninth, and the guard directly below says so in its own docstring, in this
    file: a module whose entire subject is two documents that can disagree
    carried two docstrings that did, and had no way to notice. The floor is
    gone, because a count held exactly leaves a floor beneath it nothing to say.
    """
    agents = agents_rubric()
    template = template_rubric()
    assert set(template) - {NOT_A_CATEGORY} == set(agents), sorted(
        set(template) ^ set(agents))
    assert NOT_A_CATEGORY in template, sorted(template)
    assert NOT_A_CATEGORY not in agents, "the empty case is not a category"

    worded = sorted(name for name in agents
                    if agents[name].strip() != template[name].strip())
    _states(test_the_skip_rubric_is_stated_the_same_way_twice.__doc__,
            r"([a-z]+) of the ([a-z]+) glosses are worded differently",
            len(worded), len(agents))


def test_every_skip_this_repository_takes_names_a_rubric_category() -> None:
    """The rule `AGENTS.md` §8 states, applied to this repository.

    All three skips failed it when it was first applied, which is what a rule
    nothing enforces is worth. One of the three is `OPTIONAL_DEPENDENCY_ABSENT`
    and always was --- the Lean dependency's checkout is not always present ---
    and it said so in words the rubric did not use.

    The other two had no category. They skip a document that is a dated record
    of an earlier commit, whose numbers describe that commit: the test cannot
    fail, because there is nothing about today for it to be wrong about. Every
    one of the eight categories is a reason the test cannot *run* here --- an
    absent capability, dependency, service, architecture, device, privilege, or
    a defect quarantined, or a duration excluded. None of them is a reason the
    test does not *apply*, and that is a different thing: the first says the
    measurement is unavailable, the second says the subject is. So the rubric
    gained a ninth, `DATED_RECORD_BOUNDARY`, because a checklist that does not
    cover the cases in front of it cannot be satisfied honestly, only quietly.
    """
    categories = set(agents_rubric())
    skips = _skips()
    assert len(skips) >= 3, skips
    undisclosed = [f"{path}:{line}: {said!r}" for path, line, said in skips
                   if not any(category in said for category in categories)]
    assert not undisclosed, (
        "skips that name no rubric category:\n" + "\n".join(undisclosed))


def test_the_rubric_categories_the_skips_use_are_ones_that_apply() -> None:
    """A category must be earned, not just named.

    `QUARANTINED_DEFECT` says a tracked issue is isolated, and a skip claiming
    it while nothing is tracked is worse than an undisclosed skip, because it
    reads as disclosed. The two categories this repository uses are the two it
    can show: a dependency whose absence the same function detects, and a
    document the prose guards list as historical.
    """
    used = {category for _, _, said in _skips()
            for category in agents_rubric() if category in said}
    assert used == {"OPTIONAL_DEPENDENCY_ABSENT", "DATED_RECORD_BOUNDARY"}, used
    body = (REPO / "tests" / "test_declared_counts.py").read_text(
        encoding="utf-8")
    # The dependency skip must be guarded by a check that the path is missing,
    # and the dated-record skip by the list that says which documents are dated.
    assert "if not sibling.exists():" in body
    assert "HISTORICAL" in body


def _agents_sections() -> str:
    return AGENTS.read_text(encoding="utf-8")


def test_the_axiom_count_the_policy_states_is_the_inventory_it_names() -> None:
    """`AGENTS.md` states this number twice, and it was wrong in both places.

    "keep the source assumption inventory matching `_baseline.py` exactly (18
    kernel axioms)" is a claim about a set that `_baseline.py` holds and
    `_reports.py` is the arbiter of: `policy_errors` compares the kernel
    declarations it reads out of Lean against `AXIOM_DECLARATIONS`, so
    `AXIOM_DECLARATIONS` is what a kernel axiom is. There are 61 of them, and
    `lean4/Hypermath/` declares exactly those 61 with the `axiom` keyword ---
    the two sides of the sentence agree perfectly with each other and neither
    agrees with the number in front of them.

    A number no subset reconstructs is the worst kind of stale, because there
    is nothing to find by looking: 21 declarations are `ax`-prefixed, 23 with
    the filtration pair, 35 are definitions, 11 are L0's logical clauses. None
    of the obvious readings is 18. The count was right about something once and
    the sentence outlived it, which is the failure this whole suite exists for,
    sitting in the document that tells the suite what to do.
    """
    from hypermath_foundations._baseline import AXIOM_DECLARATIONS

    stated = re.findall(r"(\d+)\s+kernel axioms", _agents_sections())
    assert stated, "AGENTS.md no longer states a kernel axiom count"
    assert {int(number) for number in stated} == {len(AXIOM_DECLARATIONS)}, stated

    declared = set()
    for path in sorted((REPO / "lean4" / "Hypermath").glob("*.lean")):
        for line in path.read_text(encoding="utf-8").splitlines():
            found = re.match(r"^\s*axiom\s+([A-Za-z_][A-Za-z0-9_']*)", line)
            if found:
                declared.add("Hypermath." + found.group(1))
    # "matching `_baseline.py` exactly" is the claim; this is what it means.
    assert declared == set(AXIOM_DECLARATIONS), sorted(
        declared ^ set(AXIOM_DECLARATIONS))


def test_the_presentation_gate_lists_every_check_it_runs() -> None:
    """§6 says what `scripts/check_presentation.py` checks, and listed four of five.

    `check_lineage_claims` rejects phrases that silently upgrade recorded
    ancestry into causality, it has run in CI as long as the other four, and
    the section describing the gate did not mention it. An unlisted check is
    the mirror of an unheld rule: the rule above was stated and not enforced,
    this one was enforced and not stated. Both are a gap between what this
    project does and what it says it does, and only one of them is usually
    called a bug.
    """
    source = (REPO / "scripts" / "check_presentation.py").read_text(
        encoding="utf-8")
    body = re.search(r"^def run\(\).*?(?=^def |\Z)", source,
                     re.M | re.S)
    assert body, "check_presentation.py no longer has a run()"
    runs = set(re.findall(r"^\s+(check_[a-z_]+)\(errors\)", body.group(0), re.M))
    assert len(runs) >= 5, sorted(runs)

    section = _agents_sections().partition("## 6. Presentation gate")[2]
    section = section.partition("## 7.")[0]
    described = {line for line in section.splitlines() if line.startswith("- ")}
    # The section names each check, in code style. Matching the description to
    # the function by the words in its name was the first try and it is the
    # wrong kind of reader --- `check_versions` against "version agreement"
    # fails on a plural. A description of a check should cite the check.
    unlisted = sorted(name for name in runs
                      if not any("`" + name + "`" in line for line in described))
    assert not unlisted, "checks the presentation gate runs but does not list: " + str(
        unlisted)


def test_the_line_ending_invariant_holds_where_the_release_reads_it() -> None:
    """"`.gitattributes` forces `eol=lf`" is a claim about the index, not the disk.

    On the disk it is false right now: twenty tracked files carry CRLF, among
    them every `docs/terms/*.md`, `LICENSE` and `L0_ground.hm`. Nothing sees
    it. Git reports them unmodified because it normalizes on read, and Python
    reports them as LF because text mode translates newlines, so the whole
    suite can read those files all day without a byte of CRLF reaching it.

    It does not reach the release either, and that is the part worth stating
    rather than assuming: the source archive comes from `git archive`, which
    reads the index, and `_normalize_newlines` handles the rest. So the
    invariant is true where it is load-bearing and false where nothing loads it,
    which is a sentence worth being precise about instead of leaving to luck.

    The exceptions are marked, not tolerated. The files whose index bytes are
    CRLF are exactly the imported snapshots under `references/precursor/`, which
    `.gitattributes` marks `-text` so that normalization cannot touch them ---
    they are pinned by sha256 in their own manifest, and a normalized snapshot
    is a different file.
    """
    import shutil
    import subprocess

    if not shutil.which("git"):                   # pragma: no cover
        pytest.skip("OPTIONAL_DEPENDENCY_ABSENT: git is not on PATH")
    listed = subprocess.run(["git", "ls-files", "--eol"], cwd=str(REPO),
                            capture_output=True, text=True)
    if listed.returncode:                         # pragma: no cover
        pytest.skip("OPTIONAL_DEPENDENCY_ABSENT: no git checkout to read")

    index_crlf: list[str] = []
    for line in listed.stdout.splitlines():
        marks, _, name = line.rpartition("\t")
        if "i/crlf" in marks:
            index_crlf.append(name.strip())
    assert index_crlf, "no file is exempt any more, so the exemption is stale"
    outside = [name for name in index_crlf
               if not name.startswith("references/precursor/")]
    assert not outside, "CRLF in the index outside the pinned snapshots: " + str(
        outside)

    attributes = (REPO / ".gitattributes").read_text(encoding="utf-8")
    assert "* text=auto eol=lf" in attributes
    assert "-text" in attributes, "nothing marks the snapshots unnormalized"


#: A number written as a word, which is how these modules write them.
INVARIANT_WORDS = {"one": 1, "two": 2, "three": 3, "four": 4, "five": 5,
                   "six": 6, "seven": 7, "eight": 8, "nine": 9, "ten": 10,
                   "eleven": 11, "twelve": 12}

#: A line that ends in a colon and opens on a number word: a count that
#: introduces the list beneath it.
COUNTED_INTRO = re.compile(
    r"^(" + "|".join(INVARIANT_WORDS) + r")\b[^:]*:$", re.I)


def test_a_module_that_counts_its_own_invariants_counts_them_right() -> None:
    """A guard module's docstring may open by saying how many things it holds.

    Every hand-kept number in this repository has drifted, and a number written
    at the top of the module that enforces the numbers is no different.  The
    module docstring of `test_discharge_pointers` said "Four" for as long as it
    held four, and this increment took it to seven; nothing would have noticed
    if the list and the word had parted company.

    The reader is general and the population is small, so it asserts that it
    found a list at all.  A count guard that passes because it read nothing is
    the failure it exists to prevent.
    """
    wrong: list[str] = []
    found = 0
    for path in sorted((REPO / "tests").glob("test_*.py")):
        tree = ast.parse(path.read_text(encoding="utf-8"))
        lines = (ast.get_docstring(tree) or "").splitlines()
        for index, line in enumerate(lines):
            opening = COUNTED_INTRO.match(line.strip())
            if not opening:
                continue
            listed = 0
            for following in lines[index + 1:]:
                if not following.strip():
                    if listed:
                        break
                    continue
                if following.startswith("* "):
                    listed += 1
                elif not listed:
                    break
                elif not following.startswith(" "):
                    break
            if not listed:
                continue
            found += 1
            claimed = INVARIANT_WORDS[opening.group(1).lower()]
            if claimed != listed:
                wrong.append(f"{path.name}: \"{line.strip()}\" over {listed}")
    assert found, "no module docstring counts a list, so this reader read nothing"
    assert not wrong, "counted lists that are not the length they claim:\n" + "\n".join(wrong)
