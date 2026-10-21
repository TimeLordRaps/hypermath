"""Cross-module discharge pointers in the Lean sources must resolve.

The layer stack carries prose pointers of the form "Discharged in X, theorem Y"
and "proved below at Z".  Nothing checked them, and three of them had rotted:
one named a theorem that had been withdrawn, one named a theorem that never
existed, and one named a layer that carries only a conditional.  A claim
asserted as discharged in several places and proved in none is the exact failure
this module exists to prevent.

Seven invariants, all derived from the Lean sources themselves:

* every identifier cited on a line that claims a discharge must be a
  declaration that exists;
* every repository-rooted dotted name in any comment must resolve;
* every admitted declaration must say what its admission is -- independent,
  open, underivable, or discharged elsewhere by a named declaration that is
  not itself admitted;
* the names these sources retire are read out of the sentences that retire
  them, and none of those names may be cited as a proof;
* no line of a source is read as belonging to two declarations at once;
* a declaration carrying a `/-- ... -/` is read from the line that docstring
  opens on;
* every admitted declaration names a witness that exists and is not itself
  admitted -- the second half of the third invariant, asked of all of them.

The last three were added when the third turned out to be held by an accident.
Every admission in the tree carried a status word, so the pointer half of the
third invariant had never run; and the reader that found those words stopped at
the first blank line above a declaration, which in a paragraphed Lean docstring
is inside it, while the reader that found the end of a declaration ran on to
the next one, swallowing whatever section banner lay between.  One defect was
too narrow above and the other too wide below, so every admission still got
prose and none of it looked wrong.  `definitionOfGround` states no status of
its own and passed on the word "independent" from a census paragraph about
another theorem.

The fourth was a list of one name written down by hand.  The prose of this
project claims a discharge on more lines than its comments do, so the same two
questions are asked of the documents in `test_declared_counts.py`, which is
where document prose is read.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[1]
LEAN = REPO / "lean4"

DECLARATION = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|axiom|instance|class)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)
NAMESPACE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)")
NAMESPACE_END = re.compile(r"^\s*end\s+([A-Za-z_][A-Za-z0-9_'.]*)")
BLOCK_COMMENT = re.compile(r"/-.*?-/", re.DOTALL)
LINE_COMMENT = re.compile(r"--(.*)$")

#: A comment opening in column 0.  These sources set their sections off with
#: banner rules, and a banner after a blank line starts a new region rather
#: than continuing the proof above it.
BANNER = re.compile(r"^(?:--|/-)")
DOTTED = re.compile(r"(?<![A-Za-z0-9_.'])(?:[A-Z][A-Za-z0-9_']*\.)+[A-Za-z_][A-Za-z0-9_']*")
CAMEL = re.compile(r"(?<![A-Za-z0-9_.'])[a-z][A-Za-z0-9_']*[A-Z][A-Za-z0-9_']*")

# Status words that make an admission self-describing.
STATUS_WORDS = ("independent", "open", "underivable", "unavailable", "not available")

# Lean core and Mathlib roots are not this repository's to resolve.
#: Trees no reader in this suite reads: build output, caches, and the
#: virtual environment.  It lives here because more than one module needs
#: it and this one is the leaf they both import.
UNREAD_TREES = {".lake", "archive", "build", ".git", ".venv", "__pycache__",
                ".mypy_cache", ".pytest_cache", "node_modules"}

FOREIGN_ROOTS = frozenset({
    "Nat", "Bool", "Prod", "Sum", "Option", "List", "Array", "String", "Char",
    "Eq", "Iff", "And", "Or", "Not", "Exists", "Classical", "Quot", "Quotient",
    "Function", "Decidable", "Subtype", "Fin", "Int", "Prop", "Type", "Sort",
    "Lean", "Std", "Mathlib", "Init", "Core", "Trace", "Set", "Empty", "Unit",
    "PUnit", "PProd", "Sigma", "Subsingleton", "Inhabited", "Nonempty", "Ne",
    "HEq", "Acc", "WellFounded", "Ordering", "Id", "IO", "Except", "Thunk",
    "Bool.noConfusion", "Absurd",
})


def _strip_blocks(text: str) -> str:
    """Blank out block comments, preserving line numbering."""
    return BLOCK_COMMENT.sub(lambda m: re.sub(r"[^\n]", " ", m.group(0)), text)


def _lean_files() -> list[Path]:
    return sorted(LEAN.rglob("*.lean"))


class Source:
    def __init__(self, path: Path) -> None:
        self.path = path
        self.relative = path.relative_to(REPO).as_posix()
        self.text = path.read_text(encoding="utf-8")
        self.lines = self.text.split("\n")
        self.code_lines = _strip_blocks(self.text).split("\n")
        self.declarations: list[tuple[str, str, int]] = []  # simple, qualified, line
        self._open_before: list[int] | None = None
        self._scan()

    def _scan(self) -> None:
        stack: list[str] = []
        for number, line in enumerate(self.code_lines, start=1):
            opened = NAMESPACE.match(line)
            if opened:
                stack.append(opened.group(1))
                continue
            closed = NAMESPACE_END.match(line)
            if closed:
                if stack and stack[-1] == closed.group(1):
                    stack.pop()
                continue
            found = DECLARATION.match(line)
            if found:
                simple = found.group(2)
                qualified = ".".join(stack + [simple]) if stack else simple
                self.declarations.append((simple, qualified, number))

    def comment_lines(self) -> list[tuple[int, str]]:
        """(line number, comment text) for every line carrying comment prose."""
        out: list[tuple[int, str]] = []
        inside = False
        for number, line in enumerate(self.lines, start=1):
            text = ""
            if inside:
                text = line
                if "-/" in line:
                    inside = False
                    text = line.split("-/")[0]
            elif "/-" in line:
                head, _, tail = line.partition("/-")
                if "-/" in tail:
                    text = tail.split("-/")[0]
                    rest = LINE_COMMENT.search(tail.split("-/", 1)[1])
                    if rest:
                        text += " " + rest.group(1)
                else:
                    inside = True
                    text = tail
                marker = LINE_COMMENT.search(head)
                if marker:
                    text = marker.group(1) + " " + text
            else:
                marker = LINE_COMMENT.search(line)
                if marker:
                    text = marker.group(1)
            if text.strip():
                out.append((number, text))
        return out

    def docstring_start(self, declaration_line: int) -> int:
        """First line of the comment block immediately above a declaration.

        A blank line ends the block only when the blank line is outside one.
        Lean docstrings are paragraphed, and this walk used to stop at the
        first paragraph break inside `/-- ... -/`, so every admitted
        declaration in the tree was read from its closing paragraph alone:
        `derivesIsDirectional` names the two models that settle it and the
        reader saw neither.
        """
        number = declaration_line - 1
        while number >= 1:
            stripped = self.lines[number - 1].strip()
            inside = self._inside_block(number)
            if not stripped:
                if not inside:
                    break
            elif not (
                stripped.startswith("--")
                or stripped.startswith("/-")
                or stripped.endswith("-/")
                or inside
            ):
                break
            number -= 1
        return number + 1

    def _inside_block(self, number: int) -> bool:
        """Is line `number` inside an open `/- ... -/` block?

        Counted once per file and kept, because the walk above now asks this of
        every blank line it passes rather than only of the lines it keeps.
        """
        if self._open_before is None:
            depth = 0
            counts = [0]
            for line in self.lines:
                depth += line.count("/-") - line.count("-/")
                counts.append(depth)
            self._open_before = counts
        return self._open_before[number - 1] > 0

    def span(self, line: int) -> tuple[int, int]:
        """The declaration enclosing `line`, as (start, end) line numbers.

        The region ends where the declaration's own text ends: before the next
        declaration's comment block, and before any section banner set off from
        the proof by a blank line.  It used to end at the line before the next
        declaration, which handed each declaration the next one's docstring and
        every banner in between.  A trailing note written against the proof
        with no blank line before it is the declaration's own and stays.
        """
        starts = [number for _, _, number in self.declarations]
        start = 0
        for number in starts:
            if number <= line:
                start = number
            else:
                break
        following = [number for number in starts if number > start]
        limit = (self.docstring_start(following[0]) - 1) if following \
            else len(self.lines)
        for number in range(start, limit + 1):
            if self.lines[number - 1].strip():
                continue
            after = next(
                (self.lines[index - 1]
                 for index in range(number + 1, limit + 1)
                 if self.lines[index - 1].strip()),
                "",
            )
            if BANNER.match(after):
                return start, number - 1
        return start, limit


@pytest.fixture(scope="module")
def sources() -> list[Source]:
    files = _lean_files()
    assert files, "no Lean sources found under lean4/"
    return [Source(path) for path in files]


@pytest.fixture(scope="module")
def declared(sources: list[Source]) -> tuple[frozenset[str], frozenset[str]]:
    simple = {name for source in sources for name, _, _ in source.declarations}
    qualified = {name for source in sources for _, name, _ in source.declarations}
    return frozenset(simple), frozenset(qualified | modules_of(sources))


def modules_of(sources: list[Source]) -> frozenset[str]:
    """Module names, which resolve in prose but never count as proofs."""
    names = {
        "Hypermath." + source.path.stem
        for source in sources
        if source.path.parent.name == "Hypermath"
    }
    return frozenset(names | {source.path.stem for source in sources})


@pytest.fixture(scope="module")
def repository_roots(sources: list[Source]) -> frozenset[str]:
    roots = {"Hypermath"}
    for source in sources:
        for line in source.code_lines:
            opened = NAMESPACE.match(line)
            if opened:
                roots.add(opened.group(1).split(".")[0])
    return frozenset(roots - FOREIGN_ROOTS)


@pytest.fixture(scope="module")
def admissions(sources: list[Source]) -> list[tuple[Source, str, int, int]]:
    """(source, declaration name, start line, end line) per admitted declaration."""
    found: dict[tuple[str, str], tuple[Source, str, int, int]] = {}
    for source in sources:
        for number, line in enumerate(source.code_lines, start=1):
            if re.search(r"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])", line):
                start, end = source.span(number)
                if not start:
                    continue
                name = next(
                    (
                        qualified
                        for _, qualified, declared_at in source.declarations
                        if declared_at == start
                    ),
                    "<unknown>",
                )
                found[(source.relative, name)] = (source, name, start, end)
    return sorted(found.values(), key=lambda item: (item[0].relative, item[2]))


def _resolves(token: str, simple: frozenset[str], qualified: frozenset[str]) -> bool:
    if token in qualified or token in simple:
        return True
    tail = token.rsplit(".", 1)[-1]
    return tail in simple


def test_lean_sources_are_scannable(sources: list[Source]) -> None:
    assert len(sources) >= 20
    assert any(source.path.name == "Countermodels.lean" for source in sources)
    assert any(source.path.name == "FullAxiomModel.lean" for source in sources)


def test_discharge_claims_name_declarations_that_exist(
    sources: list[Source], declared: tuple[frozenset[str], frozenset[str]]
) -> None:
    """A line claiming a discharge may only cite identifiers that exist."""
    simple, qualified = declared
    broken: list[str] = []
    for source in sources:
        for number, text in source.comment_lines():
            if "ischarge" not in text:
                continue
            for token in CAMEL.findall(text):
                if not _resolves(token, simple, qualified):
                    broken.append(f"{source.relative}:{number}: {token}")
    assert not broken, "discharge pointers naming nonexistent declarations:\n" + "\n".join(broken)


def test_repository_qualified_names_in_comments_resolve(
    sources: list[Source],
    declared: tuple[frozenset[str], frozenset[str]],
    repository_roots: frozenset[str],
) -> None:
    """`Namespace.theoremName` written in prose must be a real declaration."""
    simple, qualified = declared
    broken: list[str] = []
    for source in sources:
        for number, text in source.comment_lines():
            for token in DOTTED.findall(text):
                if token.endswith(".lean"):
                    continue
                root = token.split(".")[0]
                if root not in repository_roots:
                    continue
                if token in qualified:
                    continue
                if not _resolves(token, simple, qualified):
                    broken.append(f"{source.relative}:{number}: {token}")
    assert not broken, "qualified names in comments that do not resolve:\n" + "\n".join(broken)


def test_every_admission_states_its_status(
    sources: list[Source],
    admissions: list[tuple[Source, str, int, int]],
    declared: tuple[frozenset[str], frozenset[str]],
) -> None:
    """No silent `sorry`.

    An admitted declaration must either name its status -- independent, open,
    underivable -- or point at a declaration that closes it and is not itself
    admitted.
    """
    simple, qualified = declared
    modules = modules_of(sources)
    admitted_names = {name for _, name, _, _ in admissions}
    admitted_simple = {name.rsplit(".", 1)[-1] for name in admitted_names}
    silent: list[str] = []
    for source, name, start, end in admissions:
        prose = " ".join(
            text
            for number, text in source.comment_lines()
            if source.docstring_start(start) <= number <= end
        )
        lowered = prose.lower()
        if any(word in lowered for word in STATUS_WORDS):
            continue
        pointers = set(CAMEL.findall(prose)) | set(DOTTED.findall(prose))
        resolved = {
            token.rsplit(".", 1)[-1]
            for token in pointers
            if token not in modules and _resolves(token, simple, qualified)
        }
        # A module name is a place, not a proof; only declarations count.
        witnesses = (resolved & simple) - admitted_simple - {name.rsplit(".", 1)[-1]}
        if witnesses:
            continue
        silent.append(f"{source.relative}:{start}: {name}")
    assert not silent, (
        "admissions with no stated status and no resolving pointer:\n" + "\n".join(silent)
    )


def test_no_two_declarations_are_read_the_same_line(
    sources: list[Source],
) -> None:
    """A line of a Lean source belongs to one declaration, or to none.

    A declaration's region is its comment block plus its body, and every reader
    that asks what a declaration says reads that region.  Where two regions
    overlap, one declaration is handed prose written about another, and a guard
    looking for a word finds it in a paragraph about something else.

    That is not hypothetical.  `Hypermath.definitionOfGround` states no status
    of its own -- it says it is proved downstream, which is the other thing an
    admission may say -- and it satisfied the status guard above for as long as
    that guard existed, on the word "independent" in a section census written
    about `derivesIsDirectional`.  The census is correct, the admission is
    correct, and the reader joined them.  Nothing was false and the claim was
    not held.
    """
    clashes: list[str] = []
    for source in sources:
        regions = sorted(
            (source.docstring_start(at), source.span(at)[1], name)
            for _, name, at in source.declarations
        )
        for (_, last, name), (first, _, after) in zip(regions, regions[1:]):
            if first <= last:
                clashes.append(
                    f"{source.relative}: {name} is read through line {last},"
                    f" and {after} is read from line {first}"
                )
    assert not clashes, (
        "declarations reading each other's lines:\n" + "\n".join(clashes)
    )


def test_a_docstring_is_read_from_the_line_it_opens_on(
    sources: list[Source],
) -> None:
    """Where a declaration carries a `/-- ... -/`, the reader starts at the `/--`.

    Lean docstrings are paragraphed, and a walk upwards that ends at a blank
    line ends inside them.  The readers here then take the closing paragraph
    for the whole of what a declaration says, which is a narrower subject than
    the one they name.  `derivesIsDirectional` closes with a sentence of
    verdict and names its two models in the paragraph above it; read as it was,
    it cited nothing at all.
    """
    cut: list[str] = []
    for source in sources:
        for _, name, at in source.declarations:
            first = source.docstring_start(at)
            if first == at:
                continue                       # nothing above it to read
            block = "\n".join(source.lines[first - 1: at - 1])
            if "-/" not in block:
                continue                       # line comments, which have no opener
            if not block.lstrip().startswith("/-"):
                cut.append(
                    f"{source.relative}:{at}: {name} is read from line {first},"
                    " which is not where its docstring opens"
                )
    assert not cut, (
        "declarations read from the middle of their own docstring:\n"
        + "\n".join(cut)
    )


def test_every_admission_names_a_witness_that_is_not_itself_admitted(
    sources: list[Source],
    admissions: list[tuple[Source, str, int, int]],
    declared: tuple[frozenset[str], frozenset[str]],
) -> None:
    """The second thing an admission may say, asked of every admission.

    The status guard above accepts a word or a pointer, in that order, and
    every admission in the tree carried a word -- so the pointer arm never ran
    once, and the clause inside it that refuses a witness which is itself
    admitted never ran either.  A disjunction whose second arm is unreachable
    states more than it holds.

    Asked directly, every admission names a declaration that exists, is not the
    admission itself, and is not admitted.  That is stronger than the
    disjunction and it is what is true, so it is asked here on its own.
    """
    simple, qualified = declared
    modules = modules_of(sources)
    admitted = {name.rsplit(".", 1)[-1] for _, name, _, _ in admissions}
    unwitnessed: list[str] = []
    for source, name, start, end in admissions:
        prose = " ".join(
            text
            for number, text in source.comment_lines()
            if source.docstring_start(start) <= number <= end
        )
        pointers = set(CAMEL.findall(prose)) | set(DOTTED.findall(prose))
        resolved = {
            token.rsplit(".", 1)[-1]
            for token in pointers
            if token not in modules and _resolves(token, simple, qualified)
        }
        witnesses = (resolved & simple) - admitted - {name.rsplit(".", 1)[-1]}
        if not witnesses:
            unwitnessed.append(f"{source.relative}:{start}: {name}")
    assert not unwitnessed, (
        "admissions naming no declaration that is not itself admitted:\n"
        + "\n".join(unwitnessed)
    )


def test_admission_count_is_pinned(
    admissions: list[tuple[Source, str, int, int]]
) -> None:
    """The layer stack carries no admissions."""
    names = sorted(
        name
        for source, name, _, _ in admissions
        if "/Hypermath/" in source.relative
    )
    assert names == [], names


#: How the sources say a name is gone.
RETIREMENT = re.compile(r"\b(?:withdrawn|retired)\b|no such theorem"
                        r"|does not exist|never existed")
#: A backticked span that is a name rather than a term.
CITED_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*$")


def cited_names(text: str) -> set[str]:
    """The names a piece of comment prose cites.

    Backticks are paired by position rather than matched by a regex, because a
    regex looking for a quoted term finds the wrong delimiters: in "the
    withdrawn `conditionalRetrace`, which was `fun _ _ _ hWit => hWit`" the
    first span containing a space is `, which was `, so blanking it leaves the
    term exposed and reads `hWit` as a cited name. A backticked span with a
    space in it is a term, and a name inside a term is part of the term.
    """
    found: set[str] = set()
    for index, span in enumerate(text.split("`")):
        if index % 2:
            if CITED_NAME.match(span.strip()):
                found.add(span.strip())
        else:
            found |= set(CAMEL.findall(span))
    return {name.rpartition(".")[2] for name in found}


def comment_blocks(source: Source) -> list[list[tuple[int, str]]]:
    """Runs of consecutive commented lines, which is how prose is written here."""
    blocks: list[list[tuple[int, str]]] = []
    previous: int | None = None
    for number, text in source.comment_lines():
        if previous is None or number != previous + 1:
            blocks.append([])
        blocks[-1].append((number, text))
        previous = number
    return blocks


def retired_names(sources: list[Source]) -> dict[str, str]:
    """Every name the sources retire, and where each is retired.

    A name is retired when a sentence says it is gone and the sources no longer
    declare it. The reader is one sentence plus the sentence before it, because
    the retirement and the name are not always in the same one --- "Step 16:
    driverCycleIsClosed. There is no such theorem, here or anywhere." is the
    project's own idiom, a label and then the claim about it. It is not the
    whole comment block, because §IX of `L3Ordinatics` is one block of sixty
    lines and two of its steps are retirements; reading the block would retire
    every name the census mentions.
    """
    declared = {name for source in sources for name, _, _ in source.declarations}
    found: dict[str, str] = {}
    for source in sources:
        for block in comment_blocks(source):
            flat = " ".join(" ".join(text.split()) for _, text in block)
            pieces = [piece.strip() for piece in re.split(r"(?<=[.;])\s+", flat)
                      if piece.strip()]
            for index, piece in enumerate(pieces):
                if not RETIREMENT.search(piece):
                    continue
                window = piece if not index else pieces[index - 1] + " " + piece
                for name in cited_names(window):
                    if name not in declared:
                        found.setdefault(
                            name, f"{source.relative}:{block[0][0]}")
    return found


def test_the_retired_names_are_read_out_of_the_sources(
    sources: list[Source],
) -> None:
    """This list used to be one name written down by hand.

    `driverCycleIsClosed` was the name that was being cited as a discharge when
    this module was written, so it was the name the guard held --- under a
    docstring in the plural, which was the only thing that said the list was
    supposed to be longer. It was one of eight. `simulationPairExists`,
    `dSpansGround`, `driverCycle_FRAME`, `conditionalRetrace`, `Abstraction`,
    `abstractionTransitive` and `syntaxToAbstraction` were all retired by these
    sources, in sentences that say so, and any of them could have been cited as
    a proof with nothing objecting.

    A hand-written list of what the sources say is a copy of a measurement, and
    a copy goes stale silently, because the thing it copies has no idea it is
    being copied. The same error, in the same words, as the guard roster's
    hand-kept total two increments ago.
    """
    retired = retired_names(sources)
    # Eight, and not a floor: the count is the claim, so retiring a ninth name
    # or repairing one of these has to be recorded here rather than absorbed.
    assert sorted(retired) == [
        "Abstraction",
        "abstractionTransitive",
        "conditionalRetrace",
        "dSpansGround",
        "driverCycleIsClosed",
        "driverCycle_FRAME",
        "simulationPairExists",
        "syntaxToAbstraction",
    ], sorted(retired)
    declared = {name for source in sources for name, _, _ in source.declarations}
    for name in retired:
        assert name not in declared, name


def test_withdrawn_names_are_not_cited_as_proofs(sources: list[Source]) -> None:
    """Names that were once claimed as discharging theorems and no longer exist."""
    retired = retired_names(sources)
    offenders: list[str] = []
    for source in sources:
        for number, text in source.comment_lines():
            if "ischarge" not in text:
                continue
            for name in cited_names(text) & set(retired):
                offenders.append(
                    f"{source.relative}:{number}: {name}"
                    f" (retired at {retired[name]})")
    assert not offenders, "withdrawn names cited as discharges:\n" + "\n".join(offenders)
