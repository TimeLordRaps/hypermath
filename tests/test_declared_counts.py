"""Every clause count in the prose must be one the Lean sources actually have.

The research notes had drifted to "38 logical clauses" in twenty-eight places
while the model structures enumerated thirty-nine, and to "67 declarations: 29
parameters and 38 clauses" while `lean4/Hypermath/` declared sixty-one axioms.
A number repeated in twenty-eight documents and checked in none is the same
failure as a discharge pointer asserted everywhere and proved nowhere.

Everything here is measured from the sources. The pinned constants are the
current measurements, so a real change to the clause set fails this module and
has to be carried into the prose deliberately.
"""

from __future__ import annotations

import ast
import json
import re
from collections import Counter
from pathlib import Path

import pytest

from hypermath_foundations._baseline import PROVED_DECLARATIONS, TRANSFINITE_CLAUSES
from test_family_neighbourhood import foreign_citations
from hypermath_foundations._inventory import SOURCE_PARAMETERS
from hypermath_foundations._reports import PROBE_TARGETS

# Lean's own roots, classified once in the module that first needed them. Two
# guards asking "is this name this repository's?" should not answer it twice.
from test_discharge_pointers import (
    FOREIGN_ROOTS, UNREAD_TREES, Source, _lean_files, cited_names,
    retired_names)
from test_stated_process_rules import agents_rubric, template_rubric
from test_layer_language import layer_names

# The instrument that holds a docstring against what its guard measures. It
# lived here, and so every docstring it could reach was in this file.
from _docstring_counts import NUMBER_NAMES, _spelled, _states

REPO = Path(__file__).resolve().parents[1]
LAYERS = REPO / "lean4" / "Hypermath"

AXIOM = re.compile(r"^\s*axiom\s+([A-Za-z_][A-Za-z0-9_']*)")
WORD = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
STRUCTURE = re.compile(r"^\s*structure\s+([A-Za-z_][A-Za-z0-9_']*)\b")
# A structure header may wrap across lines; it ends at the line whose code part
# ends in `where`. Requiring that on the opening line made every wrapped
# structure invisible, and the reader returned no fields rather than failing.
HEADER_ENDS = re.compile(r"\bwhere\s*$")
NAMESPACE_OPENS = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$")
NAMESPACE_ENDS = re.compile(r"^end\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$")
FIELD = re.compile(r"^  [A-Za-z_][A-Za-z0-9_']*\s*:\s")
# A field may wrap. Continuation lines are indented deeper than a field and
# must not end the run, or a structure with a wrapped field in the middle is
# reported short.
CONTINUATION = re.compile(r"^   +\S")

# Measured, then pinned.
SOURCE_PARAMETER_COUNT = 26
LOGICAL_AXIOM_COUNT = 40
DECLARED_AXIOM_COUNT = SOURCE_PARAMETER_COUNT + LOGICAL_AXIOM_COUNT  # 66
FULL_CLAUSE_COUNT = 44  # the single `ordinatics` interface projects to five
PREFIX_CLAUSE_COUNT = 24  # L0 + L1 only

# Counts the prose is allowed to name next to the word "clause".
#
# Three clause sets exist in this repository and each is measured, not pinned:
# the 24 of the L0/L1 prefix, the 39 that precede the closing clauses of L0
# §VIII.b and L2 §II, and the 44 of the current theory. The middle one is a
# real set rather than a number: `TransportCountermodel.FullAxioms` and
# `NondegenerateCycle.FullAxioms` state it, and
# `FullAxiomModel.PreClosureAxiomsWith` states it with the reading of
# `congruentPath` left open. Two models witness facts about it, and the
# closing clause `axDiffCongruent` refutes both --- which is the point of
# them, not an accident of their age.
#
# Permitting all three is not a widening of the guard. The guard asks whether
# a number the prose names is a count the sources have; each of these three
# is, and each is measured below from the sources rather than written down
# here. A fourth number is still a failure, and so is any change to any of
# the three. It is bound once, after the third is measured.

# A dated snapshot of an earlier commit. Its numbers are history, not claims
# about the present sources, so they are read but not rewritten.
HISTORICAL = frozenset({"docs/research/PROOF_AUDIT.md"})

CLAUSE_PHRASE = re.compile(r"(?<![A-Za-z0-9])(\d+)([^.\n|\d]{0,45}?)clauses?\b")
NOT_A_CLAUSE_COUNT = ("milestone", "parameter", "step", "observation report")

# Totals the audit reports by name, so the prose has no licence to disagree.
ADMISSION_COUNT = 0
DECLARED_ASSUMPTION_COUNT = DECLARED_AXIOM_COUNT  # 66

# `PROVED_DECLARATIONS` is what the prose calls production milestones. The three
# commits that introduced the three different totals each set that dictionary to
# the number they wrote: 6b050fc/34, b35b795/38, c5de9dc/45. Measured from the
# baseline rather than pinned, because a new proof is meant to move it -- and is
# meant to move the sentences that report it in the same commit.
PRODUCTION_MILESTONE_COUNT = len(PROVED_DECLARATIONS)


def _counted(noun: str) -> re.Pattern[str]:
    """A number attached to the noun it counts, with no other number between.

    Forbidding digits in the gap keeps one total from binding to the next total's
    noun: in "61 declared assumptions and 8 admissions" the admission pattern
    cannot reach back past the 8 to the 61. A hyphen before the number excludes
    identifiers such as NC-1, and "no" before the noun excludes the sentences
    saying some group of reports contains none.
    """
    return re.compile(
        r"(?<![A-Za-z0-9-])(\d+)([^.\n|\d]{0,40}?)(?<!no )(?<!No )\b" + noun
    )


# A number is bound to the first counted noun after it. If one of these sits in
# the gap the number is already spoken for, and a later noun cannot claim it.
# This is the mirror of NOT_A_CLAUSE_COUNT above.
ALREADY_COUNTED = ("clause", "assumption", "admission", "milestone", "declaration")

# A number reporting what an earlier commit withdrew, or what a proposed repair
# would cost, is history rather than a claim about the sources. The exemption is
# per-sentence: it used to skip the whole paragraph, which silently excused every
# other number sharing it -- including two live milestone totals.
EXEMPT = ("were withdrawn", "at that repair")


def _exempt(text: str, index: int) -> bool:
    """Is the match in a sentence that reports history rather than the present?"""
    start = text.rfind(".", 0, index) + 1
    end = text.find(".", index)
    sentence = text[start: len(text) if end == -1 else end + 1].lower()
    return any(phrase in sentence for phrase in EXEMPT)

TOTALS = (
    (_counted(r"assumptions?\b"), DECLARED_ASSUMPTION_COUNT),
    (_counted(r"admissions?\b"), ADMISSION_COUNT),
    (_counted(r"admission sites?\b"), ADMISSION_COUNT),
    (_counted(r"milestones?\b"), PRODUCTION_MILESTONE_COUNT),
    (_counted(r"parameter/axiom declarations?\b"), DECLARED_AXIOM_COUNT),
)


def _layer_axioms() -> list[str]:
    names: list[str] = []
    for path in sorted(LAYERS.glob("*.lean")):
        for line in path.read_text(encoding="utf-8").split("\n"):
            found = AXIOM.match(line)
            if found:
                names.append(found.group(1))
    return names


def _structure_fields(path: Path, name: str) -> list[int]:
    lines = path.read_text(encoding="utf-8").split("\n")
    sizes: list[int] = []
    for index, line in enumerate(lines):
        found = STRUCTURE.match(line)
        if not found or found.group(1) != name:
            continue
        size = 0
        cursor = index + 1
        while cursor < len(lines):
            if FIELD.match(lines[cursor]):
                size += 1
            elif not CONTINUATION.match(lines[cursor]):
                break
            cursor += 1
        sizes.append(size)
    return sizes


SKIPPED_TREES = ("history", "build", ".lake", "references", "paper", "node_modules")


class Paragraph:
    """One block of consecutive non-blank lines, joined for scanning.

    These notes are hard-wrapped, so a number and the noun it counts routinely
    sit on different lines. Joining the block with single spaces lets one
    pattern see the whole phrase; `line_of` maps any offset in the joined text
    back to the source line, so a failure still names a place to go and edit.
    """

    def __init__(self, first_line: int) -> None:
        self.text = ""
        self.line_of: list[int] = []
        self._first = first_line

    def add(self, number: int, line: str) -> None:
        if self.text:
            self.text += " "
            self.line_of.append(number)
        self.text += line
        self.line_of.extend(number for _ in line)

    def line(self, position: int) -> int:
        if not self.line_of:
            return self._first
        return self.line_of[min(position, len(self.line_of) - 1)]

    def quoted(self) -> list[bool]:
        """Per-character "not prose" mask over the joined text.

        A number in quotes is a citation of what some other text said, not a
        claim about the sources: the notes recording this drift have to be able
        to quote the numbers they corrected. A number in an inline code span is
        a term -- `p + q + 1`, `2 ≤ x`, exit code `0` -- and no total in these
        notes is written that way, so reading one as a count only ever produces
        a false report. State resets at the paragraph boundary, which neither
        quotations nor code spans cross, so an unbalanced mark cannot flip the
        rest of the document.
        """
        mask: list[bool] = []
        quotes = code = False
        for character in self.text:
            if character == "`" and not quotes:
                code = not code
                mask.append(True)
            elif character == '"' and not code:
                quotes = not quotes
                mask.append(True)
            else:
                mask.append(quotes or code)
        return mask


def _paragraphs(path: Path) -> list[Paragraph]:
    blocks: list[Paragraph] = []
    current: Paragraph | None = None
    for number, line in enumerate(path.read_text(encoding="utf-8").split("\n"), start=1):
        if not line.strip():
            current = None
            continue
        if current is None:
            current = Paragraph(number)
            blocks.append(current)
        current.add(number, line)
    return blocks


def _prose_files() -> list[Path]:
    files = [
        path
        for path in REPO.rglob("*.md")
        if not any(part in SKIPPED_TREES or part.startswith(".") for part in path.parts)
    ]
    return sorted(files)


def test_layer_axiom_inventory_matches_the_pin() -> None:
    names = _layer_axioms()
    assert len(names) == DECLARED_AXIOM_COUNT, sorted(names)
    parameters = [name for name in names if name in SOURCE_PARAMETERS]
    assert len(parameters) == SOURCE_PARAMETER_COUNT, sorted(parameters)
    assert len(names) - len(parameters) == LOGICAL_AXIOM_COUNT


def test_source_parameters_are_all_declared() -> None:
    """`SOURCE_PARAMETERS` may not name something the layers no longer declare."""
    declared = set(_layer_axioms())
    missing = sorted(set(SOURCE_PARAMETERS) - declared)
    assert not missing, missing


def test_full_clause_structures_agree_on_their_size() -> None:
    lean = REPO / "lean4"
    full = _structure_fields(lean / "FullAxiomModel.lean", "FullAxioms")
    parameterized = _structure_fields(lean / "FullAxiomModel.lean", "FullAxiomsWith")
    action = _structure_fields(lean / "FiniteActionCountermodel.lean", "FullAxioms")
    transport = _structure_fields(lean / "Hypermath" / "TransportCountermodel.lean",
                                  "FullAxioms")
    assert full == [FULL_CLAUSE_COUNT], full
    assert parameterized == [FULL_CLAUSE_COUNT], parameterized
    assert action == [FULL_CLAUSE_COUNT], action
    # The transport model certifies the 39 that precede the closing clauses of
    # L0 §VIII.b and L2 §II, and no more. `no_incongruence_is_derivable` reads
    # its totality of `Congruent` as an independence result about all of those
    # 39, so a shrunk structure there would silently weaken that claim --- and
    # an enlarged one would claim the model satisfies a clause that refutes it
    # (`transport_violates_axDiffCongruent`).
    assert transport == [PRE_CLOSURE_CLAUSE_COUNT], transport
    # Size only. `test_every_clause_structure_names_the_same_clauses` is the
    # part of this that a renaming cannot pass.


def test_every_clause_structure_names_the_same_clauses() -> None:
    """The size test above is four structures agreeing on a number.

    Four independent models each list what they take the clause set to be, and
    until now the only thing tying those lists together was that each had 39
    entries. A clause renamed in one model and a different one renamed back
    would keep all four counts at 39 and nothing would report it.
    """
    lean = REPO / "lean4"
    sources = {
        "FullAxiomModel.FullAxioms": (lean / "FullAxiomModel.lean", "FullAxioms"),
        "FullAxiomModel.FullAxiomsWith": (lean / "FullAxiomModel.lean", "FullAxiomsWith"),
        "FiniteActionCountermodel.FullAxioms": (lean / "FiniteActionCountermodel.lean", "FullAxioms"),
    }
    named = {label: set(_clause_statements(path, structure))
             for label, (path, structure) in sources.items()}
    reference = named["FullAxiomModel.FullAxioms"]
    assert len(reference) == FULL_CLAUSE_COUNT, len(reference)
    for label, clauses in named.items():
        assert clauses == reference, (
            f"{label} lists different clauses: missing {sorted(reference - clauses)}, "
            f"extra {sorted(clauses - reference)}")
    # The transport model is a model of the 39 pre-closure clauses and is
    # refuted by the closing clause `axDiffCongruent`, so its list is the
    # 39-clause set and not the 44-clause one. It is checked separately below
    # rather than being read as a fifth copy of the same list.
    transport = set(_clause_statements(
        lean / "Hypermath" / "TransportCountermodel.lean", "FullAxioms"))
    assert len(transport) == PRE_CLOSURE_CLAUSE_COUNT, len(transport)
    assert transport < reference, (
        "the transport model no longer states a strict subset of the clause set")
    assert reference - transport == {
        "axCongruentPathSymm", "axCongruentTrans", "axDiffCongruent",
        "axSimilarRefl", "axSimilarSymm"}, sorted(reference - transport)


def test_the_clause_lists_agree_word_for_word() -> None:
    """Names were the weaker half of that. These are the same statements.

    Three of the four state all 39 clauses character for character. The fourth
    is `FullAxiomsWith`, and it differs in exactly the three clauses that
    mention `congruentPath`, in exactly one way: the symbol replaced by the
    parameter that abstracts it. Nothing else in the list moved to get that
    abstraction --- which is what makes `congruentPath_symmetry_independent` a
    result about the clause set rather than about a list rewritten until it gave
    one.
    """
    lean = REPO / "lean4"
    reference = _clause_statements(lean / "FullAxiomModel.lean", "FullAxioms")
    assert len(reference) == FULL_CLAUSE_COUNT, len(reference)
    for path in (lean / "FiniteActionCountermodel.lean",):
        assert _clause_statements(path, "FullAxioms") == reference, path.name

    abstracted = _clause_statements(lean / "FullAxiomModel.lean", "FullAxiomsWith")
    differing = {name for name in reference if abstracted[name] != reference[name]}
    mentions = {name for name, statement in reference.items()
                if re.search(r"\bcongruentPath\b", statement)}
    assert differing == mentions, (sorted(differing), sorted(mentions))
    assert differing == {"axComposeAssoc", "axComposeIdentity",
                         "axComposeNonempty", "axCongruentPathSymm"}
    for name in sorted(differing):
        assert abstracted[name] == re.sub(r"\bcongruentPath\b", "cp", reference[name]), name


def test_the_canonical_list_is_the_declared_one() -> None:
    """The free structures and the canonical list are joined by a theorem now.

    `the_canonical_clauses_are_the_free_ones` proves that `CanonicalAxioms`,
    read at the free interpretation of its ten auxiliary predicates, is the
    conjunction of the four free structures --- and Lean accepts it with no
    tactic, so the correspondence is definitional clause by clause. That
    theorem is only worth what its structure states, so this checks that
    `CanonicalAxioms` still states the canonical list character for character,
    and that the theorem still names all five of the lists it joins.
    """
    lean = REPO / "lean4"
    reference = _clause_statements(lean / "FullAxiomModel.lean", "FullAxioms")
    carried = _clause_statements(lean / "Countermodels.lean", "CanonicalAxioms")
    assert carried == reference, sorted(
        name for name in reference if carried.get(name) != reference[name])

    text = (lean / "Countermodels.lean").read_text(encoding="utf-8")
    bridge = re.search(
        r"theorem the_canonical_clauses_are_the_free_ones\b(.*?):= by", text, re.S)
    assert bridge is not None, "the joining theorem is gone"
    statement = bridge.group(1)
    for structure in ("CanonicalAxioms", "PrefixAxioms", "OperationAxioms",
                      "ComposeAxioms", "TransfiniteAxioms", "ClosingAxioms"):
        assert statement.count(structure) == 1, structure
    # The ten auxiliary predicates are what the canonical list leaves open. The
    # theorem is a statement about the free reading only if it closes them
    # there, so each of the free definitions has to appear in the instance.
    for predicate in ("structContinues", "structDistinct", "structOrbits",
                      "HMSyntax", "Substance", "Semantics", "FormClosure",
                      "Derives", "Discharge", "Definition"):
        assert re.search(rf"\({predicate} ", statement), predicate


def test_the_models_list_the_clauses_the_layers_declare() -> None:
    """The first link: from the production axioms to what the models interpret.

    `test_ordinatics_is_the_only_bundled_clause_declaration` relates the two by
    arithmetic --- 40 logical declarations, one standing for five, so 39 + 5 =
    44. That holds whatever the names are. This says the 44 the models list are
    those 39 together with the five `ordinatics` projections and nothing else,
    so a clause declared in a layer and interpreted in no model is reported,
    and so is a clause a model interprets that no layer declares.
    """
    logical = set(_layer_axioms()) - set(SOURCE_PARAMETERS)
    assert "ordinatics" in logical, "the bundle is gone; this test reads it by name"
    projections = {name.split(".")[-1] for name in TRANSFINITE_CLAUSES}
    assert len(projections) == 5, sorted(projections)
    declared = (logical - {"ordinatics"}) | projections

    interpreted = set(_clause_statements(
        REPO / "lean4" / "FullAxiomModel.lean", "FullAxioms"))
    assert declared == interpreted, (
        f"declared but interpreted nowhere: {sorted(declared - interpreted)}, "
        f"interpreted but declared nowhere: {sorted(interpreted - declared)}")


def test_prefix_structures_agree_on_their_size() -> None:
    prefix = _structure_fields(REPO / "lean4" / "Countermodels.lean", "PrefixAxioms")
    assert prefix, "no PrefixAxioms structure found"
    assert set(prefix) == {PREFIX_CLAUSE_COUNT}, prefix


def test_ordinatics_is_the_only_bundled_clause_declaration() -> None:
    """The clause count exceeds the logical axiom count by exactly five.

    `ordinatics` is one declaration standing for the five ordinal clauses the
    model structures list separately. If another bundle appears, the arithmetic
    relating the two numbers stops holding and the prose has to say so.
    """
    names = _layer_axioms()
    logical = [name for name in names if name not in SOURCE_PARAMETERS]
    assert "ordinatics" in logical
    assert FULL_CLAUSE_COUNT - LOGICAL_AXIOM_COUNT == 4
    # 40 logical declarations, one of which projects to five clauses: 39 + 5 = 44.
    assert (len(logical) - 1) + 5 == FULL_CLAUSE_COUNT


@pytest.mark.parametrize("path", _prose_files(), ids=lambda path: path.name)
def test_prose_clause_counts_are_real(path: Path) -> None:
    relative = path.relative_to(REPO).as_posix()
    if relative in HISTORICAL:
        pytest.skip("DATED_RECORD_BOUNDARY: a dated snapshot of an earlier commit")
    wrong: list[str] = []
    for block in _paragraphs(path):
        quoted = block.quoted()
        for found in CLAUSE_PHRASE.finditer(block.text):
            if quoted[found.start()] or quoted[found.end() - 1]:
                continue
            between = found.group(2).lower()
            if any(word in between for word in NOT_A_CLAUSE_COUNT):
                continue
            if int(found.group(1)) in PERMITTED_IN_PROSE:
                continue
            wrong.append(f"{relative}:{block.line(found.start())}: {found.group(0).strip()}")
    assert not wrong, "clause counts the sources do not support:\n" + "\n".join(wrong)


@pytest.mark.parametrize("path", _prose_files(), ids=lambda path: path.name)
def test_prose_totals_match_the_audit(path: Path) -> None:
    """A number attached to a counted noun must be what the audit reports.

    Whatever the wording, "N assumptions", "N admissions", "N milestones" and
    "N parameter/axiom declarations" are claims about measured quantities.
    """
    relative = path.relative_to(REPO).as_posix()
    if relative in HISTORICAL:
        pytest.skip("DATED_RECORD_BOUNDARY: a dated snapshot of an earlier commit")
    wrong: list[str] = []
    for block in _paragraphs(path):
        quoted = block.quoted()
        for pattern, expected in TOTALS:
            for found in pattern.finditer(block.text):
                if quoted[found.start()] or quoted[found.end() - 1]:
                    continue
                gap = found.group(2).lower()
                if any(noun in gap for noun in ALREADY_COUNTED):
                    continue
                if _exempt(block.text, found.start()):
                    continue
                if int(found.group(1)) != expected:
                    wrong.append(
                        f"{relative}:{block.line(found.start())}: "
                        f"{found.group(0).strip()} (audit reports {expected})"
                    )
    assert not wrong, "totals the audit does not report:\n" + "\n".join(wrong)




#: A count written as a word.  The layers and the notes both spell small
#: numbers out, and a reader that only knows digits reads neither.
COUNT_WORDS = {"one": 1, "two": 2, "three": 3, "four": 4, "five": 5, "six": 6,
               "seven": 7, "eight": 8, "nine": 9, "ten": 10, "eleven": 11,
               "twelve": 12, "thirteen": 13, "fourteen": 14, "fifteen": 15,
               "sixteen": 16, "seventeen": 17, "eighteen": 18, "nineteen": 19,
               "twenty": 20}

#: Tens, so a total spelled out reads the same as a total in digits.
#: `COUNT_WORDS` stops at twenty and both counts the prose may name are larger,
#: which is what makes the split below sound rather than a threshold chosen to
#: fit the data: a numeral this project's own word table can express is too
#: small to be a total. The guard asserts that relation instead of assuming it,
#: so moving either constant fails rather than silently widening the skip.
NUMERAL_TENS = {"twenty": 20, "thirty": 30, "forty": 40, "fifty": 50}
NUMERAL_UNITS = {word: value for word, value in COUNT_WORDS.items() if value < 10}

#: "all N clauses": a claim about the whole clause set, however N is written.
TOTAL_CLAUSES = re.compile(
    r"\ball\s+(\d+"
    r"|(?:" + "|".join(NUMERAL_TENS) + r")(?:[- ](?:" + "|".join(NUMERAL_UNITS)
    + r"))?"
    r"|" + "|".join(sorted(COUNT_WORDS, key=len, reverse=True)) + r")"
    r"\s+clauses?\b", re.I)


def _numeral(raw: str) -> int | None:
    """The value of a numeral written either way, or None if it is neither."""
    raw = raw.lower().strip().replace(" ", "-")
    if raw.isdigit():
        return int(raw)
    if raw in COUNT_WORDS:
        return COUNT_WORDS[raw]
    head, _, tail = raw.partition("-")
    if head in NUMERAL_TENS:
        return NUMERAL_TENS[head] + (NUMERAL_UNITS.get(tail, 0) if tail else 0)
    return None


#: "the N pre-closure clauses" and "the N clauses that precede": a claim
#: about a named part of the clause set rather than the whole of it.  These
#: are the two ways the sources name the pre-closure set, and each names a
#: set of thirty-nine --- the count the sources support at that size.
SCOPED_CLAUSES = re.compile(
    r"\b(?:the\s+)?(\d+|"
    + "|".join(sorted(COUNT_WORDS, key=len, reverse=True))
    + r"|(?:twenty|thirty|forty|fifty)(?:[- ](?:one|two|three|four|five|six|"
      r"seven|eight|nine))?)"
    r"\s+(?:logical\s+)?"
    r"(?:pre-closure\s+clauses|clauses\s+that\s+precede)\b", re.I)


def _scoped_clause_claims() -> list[tuple[str, int, str, str, str]]:
    """Every claim about a named part of the clause set, in prose of any kind."""
    found: list[tuple[str, int, str, str, str]] = []

    def look(relative: str, number: int, text: str, suffix: str) -> None:
        for match in SCOPED_CLAUSES.finditer(text):
            found.append((relative, number, match.group(0), match.group(1),
                          suffix))

    for source in map(Source, _lean_files()):
        for number, text in source.comment_lines():
            look(source.relative, number, text, ".lean")
    for path in [*_prose_files(), *sorted(REPO.rglob("*.hm"))]:
        if any(part.startswith(".") for part in path.parts):
            continue
        relative = path.relative_to(REPO).as_posix()
        if relative in HISTORICAL:
            continue
        for number, text in enumerate(
                path.read_text(encoding="utf-8").split("\n"), 1):
            look(relative, number, text, path.suffix)
    return found


def _total_clause_claims() -> list[tuple[str, int, str, str, str]]:
    """Every "all N clauses" this repository writes, in prose of any kind."""
    found: list[tuple[str, int, str, str, str]] = []

    def look(relative: str, number: int, text: str, suffix: str) -> None:
        for match in TOTAL_CLAUSES.finditer(text):
            found.append((relative, number, match.group(0), match.group(1),
                          suffix))

    for source in map(Source, _lean_files()):
        for number, text in source.comment_lines():
            look(source.relative, number, text, ".lean")
    for path in [*_prose_files(), *sorted(REPO.rglob("*.hm"))]:
        if any(part.startswith(".") for part in path.parts):
            continue
        relative = path.relative_to(REPO).as_posix()
        if relative in HISTORICAL:
            continue
        for number, text in enumerate(
                path.read_text(encoding="utf-8").split("\n"), 1):
            look(relative, number, text, path.suffix)
    return found


def test_a_total_clause_claim_is_the_measured_total_wherever_it_is_written() -> None:
    """A claim about the whole clause set has to be the count, in any file.

    `test_prose_clause_counts_are_real` reads `*.md`. The same claim is written
    in Lean comments and in the layer language, and two Lean sources said
    `FullAxiomModel` satisfies "all 38 clauses" when it satisfies thirty-nine.
    That is the drift this module was opened against --- its own docstring says
    the notes had reached "38 logical clauses" in twenty-eight places --- caught
    in markdown and never looked for anywhere else.

    The wider markdown rule does not survive being pointed at the sources, and
    that is why this guard is narrow rather than the old one widened. Running
    `CLAUSE_PHRASE` over the Lean comments reports four spans and none of them
    is a defect. Two are subset counts written in digits, which is legitimate
    and which the markdown happens never to do: "The 14 clauses of
    `PrefixAxioms` that are left once the ten closes are removed", and
    `prefixWithOperations_iff_conditions` reaching "31 of the clauses". Two are
    numbers the forty-five character window reaches across to a noun they were
    never attached to --- a line number, and the size of a reduction. So
    `PERMITTED_IN_PROSE` reads as a fact about this project and is a fact about
    one file type, held up by an accident of how the markdown happens to be
    written.

    What does port is the total. "all N clauses" is a claim about the whole
    set, so the only counts it can name are the two the sources support, and
    that holds wherever the sentence is written. N may be digits or words:
    `docs/research/CLAUSE_INDEPENDENCE.md` writes "all thirty-nine clauses",
    and a digits-only reader would have left the one spelled total unread.
    Words are safe to admit because `COUNT_WORDS` stops at twenty while both
    permitted totals are larger, so a numeral the table can express is a subset
    by construction --- asserted below, not assumed.

    Not claimed: a subset written in words is not checked at all. There are
    four, all correct, and telling one from a total needs the sentence parsed
    rather than the numeral read.
    """
    assert max(COUNT_WORDS.values()) < min(PERMITTED_IN_PROSE), (
        "a spelled numeral can now reach a permitted total, so the skip below "
        "would hide a wrong one")
    claims = _total_clause_claims()
    # The reach is the population the reader reads, and the reader reads two
    # populations: the totals and the scoped claims.  Measuring only the
    # first made a correction look like a coverage loss --- correcting a
    # stale "all 39 clauses" to "the 39 pre-closure clauses" moved a claim
    # out of the totals and the floor fell with it, which is the guard
    # reporting the loss of a member it should have counted twice.
    reach = Counter(suffix for *_, suffix in claims + _scoped_clause_claims())
    # Pinned as floors, not to the number. Increment 47 pinned a reach of four
    # exactly, which is right for a reader touching four spans of settled
    # prose; pinning fifty-odd claims across living documents would fail on
    # correct edits and teach the next person to retype the number without
    # reading it, which is the habit this module exists to break.
    assert set(reach) == {".hm", ".lean", ".md"}, dict(reach)
    assert reach[".lean"] > 15 and reach[".md"] > 25, dict(reach)
    wrong: list[str] = []
    subsets = compared = 0
    for relative, number, span, numeral, _ in claims:
        value = _numeral(numeral)
        assert value is not None, f"{relative}:{number}: {span}"
        if value <= max(COUNT_WORDS.values()):
            subsets += 1
            continue
        compared += 1
        if value not in PERMITTED_IN_PROSE:
            wrong.append(f"{relative}:{number}: {span}")
    assert not wrong, ("clause totals the sources do not support:\n"
                       + "\n".join(wrong))
    # Both arms have to run, or half of the split is untested code. Which is
    # what the second line says and what the first said with a forty-five in
    # it: `compared` is 55, so the floor stood for the arm running and for
    # fifty-four of its comparisons besides, and the two reach floors above are
    # what actually holds this reader to the corpus.
    assert compared, "no total claim was compared, so that arm never ran"
    assert subsets, "no subset claim was read, so that arm never ran"

    # A claim about a named part of the clause set is read here too.  The
    # pre-closure set is the only part the sources name at a different size,
    # so the count it can name is the pre-closure count and no other.  A
    # sentence that says "the 44 pre-closure clauses" is a claim the sources
    # do not support, and one that says "the 39 clauses that precede" is a
    # claim they do.
    scoped = _scoped_clause_claims()
    scoped_wrong: list[str] = []
    for relative, number, span, numeral, _ in scoped:
        value = _numeral(numeral)
        assert value is not None, f"{relative}:{number}: {span}"
        if value != PRE_CLOSURE_CLAUSE_COUNT:
            scoped_wrong.append(f"{relative}:{number}: {span}")
    assert not scoped_wrong, (
        "scoped clause counts the sources do not support:\n"
        + "\n".join(scoped_wrong))
    assert scoped, "no scoped clause claim was read, so that arm never ran"


#: "N <noun> (a, b, c)": a count that introduces the list standing right
#: after it.  Unlike the totals above, this claim needs no audit to check --
#: the list is its own evidence, sitting in the same sentence.
COUNTED_LIST = re.compile(
    r"\b(" + "|".join(COUNT_WORDS) + r"|\d+)\s+"
    r"([A-Za-z][A-Za-z -]{0,40}?)\s*"
    r"\(([^()]{4,400})\)", re.I)

#: The files whose counted lists are read: the layer language, the notes, and
#: the Lean sources.  Imported specifications are pinned by someone else's
#: manifest, and `PROOF_AUDIT.md` is a dated record whose lists describe the
#: commit it was written at.
NUMBER_IN_CLAUSE = (r"\b(?:" + "|".join(COUNT_WORDS) + r"|\d+)\b")

COUNTED_LIST_SUFFIXES = ("*.hm", "*.md", "*.lean")


COMMENT_MARKER = re.compile(r"(?:(?<=\s)|^)--(?=\s)")

def _listed_items(inside: str) -> list[str]:
    parts = [part.strip(" \t`") for part in re.split(r",|\band\b", inside)]
    return [part for part in parts if part]


def _counted_list_files() -> list[Path]:
    found: list[Path] = []
    for suffix in COUNTED_LIST_SUFFIXES:
        for path in sorted(REPO.rglob(suffix)):
            if UNREAD_TREES & set(path.parts):
                continue
            relative = path.relative_to(REPO).as_posix()
            if relative.startswith("references/precursor/") or relative in HISTORICAL:
                continue
            found.append(path)
    return found


def test_a_count_that_introduces_a_list_is_the_length_of_the_list() -> None:
    """The cheapest checkable claim in the repository, and nothing checked it.

    `L0_ground.hm` said "The five axioms" and then named seven of them, in the
    same sentence, ninety lines above the block that calls them "Seven Section
    VIII axioms".  No audit is needed to catch that and none of the counters
    above would have: they hold a number against a measurement, and this is a
    number standing next to its own evidence.

    The reader has to know where the phrase begins.  "three statements with
    one inert binder and one clause implied from beneath (`a`, `b`)" cites two
    witnesses for a compound claim, and the count nearest the parenthesis is
    not the count the parenthesis belongs to -- so when more than one count
    stands in the clause the binding is ambiguous and the reader declines it
    rather than guessing.  A code span is not an aside here, it is the thing
    being counted, so only a `"` quotation exempts a match.

    How far it reaches was not written down, and is four. Sixty-four spans match
    the pattern; fifty-two hold fewer than two items, four hold something that
    is not a bare name, three carry a second number in the clause and one is
    inside a quotation. Four claims are compared, across a hundred and five
    files. That is worth pinning rather than leaving implicit, because this
    guard asserts only that nothing disagrees --- a reader that matched nothing
    at all would satisfy it in silence, which is the failure this module exists
    to catch, one level up. The reach is pinned per file type, so a change that
    empties one surface fails even while the others still compare.
    """
    reach: Counter[str] = Counter()
    wrong: list[str] = []
    for path in _counted_list_files():
        relative = path.relative_to(REPO).as_posix()
        for block in _paragraphs(path):
            # A layer or Lean comment marker survives the join and lands
            # inside the list, where it makes a name look like prose and the
            # whole claim disappear.  Blanking it keeps the text the same
            # length, so a failure still names the line it is on.
            text = COMMENT_MARKER.sub("  ", block.text)
            speech = []
            inside_speech = False
            for character in text:
                if character == '"':
                    inside_speech = not inside_speech
                    speech.append(True)
                else:
                    speech.append(inside_speech)
            for found in COUNTED_LIST.finditer(text):
                if speech[found.start()] or speech[found.end() - 1]:
                    continue
                raw, noun, inside = found.groups()
                count = COUNT_WORDS.get(raw.lower())
                if count is None:
                    count = int(raw)
                listed = _listed_items(inside)
                if len(listed) < 2:
                    continue
                if not all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.:-]*", part)
                           for part in listed):
                    continue                      # parenthetical prose, not a list
                clause = text[:found.start()]
                for terminator in (". ", ": ", "; ", "! "):
                    clause = clause.rpartition(terminator)[2]
                if len(re.findall(NUMBER_IN_CLAUSE, clause + " " + raw, re.I)) > 1:
                    continue                      # ambiguous binding
                reach[path.suffix] += 1
                if count != len(listed):
                    wrong.append(
                        f"{relative}:{block.line(found.start())}: says {count}"
                        f" {noun.strip()!r}, names {len(listed)}")
    assert not wrong, "counts that disagree with the list beside them:\n" + "\n".join(
        wrong)
    assert dict(reach) == {".hm": 1, ".lean": 1, ".md": 2}, dict(reach)


#: A count and its noun, ending the line on a colon. Inline, a colon does not
#: bind its noun to what follows: `README.md` says "across two models: `a`,
#: `b`, `c`, `d`, `e`" and is right --- two models, five declarations --- so a
#: reader taking an inline colon as introducing the count's own list reports a
#: defect that is not there, which is the direction that invents them. The line
#: ending is not what rules that out, though this was first written as if it
#: were: dropping the anchor leaves the guard green, because the list has to be
#: set out beneath and the inline case has nothing beneath it. The anchor is a
#: narrowing nothing in this repository can currently distinguish.
COUNTED_BLOCK = re.compile(
    r"\b(" + "|".join(COUNT_WORDS) + r"|\d+)\s+"
    r"([A-Za-z][A-Za-z -]{0,40}?)\s*:\s*$", re.I)

#: An item of a list set out beneath such a line, bulleted or numbered.
BLOCK_ITEM = re.compile(r"^\s*(?:[-*]|\d+\.)\s+\S")


def test_a_count_that_introduces_a_set_out_list_is_its_length() -> None:
    """The same claim as above, written down the page instead of across it.

    The guard above reads a list inside parentheses, and its reach is four.
    A list set out under its own heading is the same claim in the punctuation a
    document uses when the items are sentences, and nothing read it.
    `CONSTRUCTIVE_QUINE_SELF_CLOSURE.md` said "two rigorous boundary results:"
    over a numbered list of four, and referred to item (4) by number further
    down the same section --- so the list had grown twice, the prose around it
    had followed, and the number introducing it had not. A count is checkable
    exactly when its own list is beside it, and this is the second way this
    repository writes that.

    Four such lists exist after the executable README examples were added; no
    Lean docstring or layer file sets one out this way. The reach is pinned for
    the same reason as above.
    """
    found = 0
    wrong: list[str] = []
    for path in _counted_list_files():
        relative = path.relative_to(REPO).as_posix()
        lines = path.read_text(encoding="utf-8").split("\n")
        for number, line in enumerate(lines, start=1):
            head = COUNTED_BLOCK.search(line)
            if not head:
                continue
            raw, noun = head.groups()
            count = COUNT_WORDS.get(raw.lower())
            if count is None:
                count = int(raw) if raw.isdigit() else None
            if count is None:
                continue
            # The guard above declines a clause carrying a second number,
            # because inline it cannot tell which one the list belongs to.
            # Here it can: the count is the one immediately before the noun
            # and the colon that ends the line, so a second number is just a
            # word. Applying that rule here would have declined the defect
            # this guard was written for, on the strength of "Lean 4".
            items, at = 0, number
            while at < len(lines):
                if BLOCK_ITEM.match(lines[at]):
                    items += 1
                elif lines[at].strip() == "" and not items:
                    pass                          # blank line before the list
                else:
                    break
                at += 1
            if items < 2:
                continue
            found += 1
            if count != items:
                wrong.append(f"{relative}:{number}: says {count} "
                             f"{noun.strip()!r}, sets out {items}")
    assert not wrong, "counts that disagree with the list beneath them:\n" + "\n".join(
        wrong)
    assert found == 4, found


REPORTED = re.compile(r"[^.|\d]{0,45}?\breports?\b")


def test_every_audit_group_size_is_reported() -> None:
    """The other direction, which neither scan above covers.

    Both scans fail when a sentence disagrees with a measurement. Neither fails
    when a measurement is named in no sentence at all, and four groups were in
    exactly that state: `layered_derivation`, `full_model`, `record_machine`
    and `countermodel` had each grown past the last note that mentioned them.
    The ones that were reported are the ones that had not moved since the note
    that introduced them, which is the whole mechanism: each note states a size
    as of its own boundary, the group grows, and nothing revisits the sentence.
    A total no sentence reports is a total no sentence can contradict.

    The requirement is deliberately narrow --- some line, in some scanned file,
    naming the process and its size together. `docs/verification.md` carries
    them as a table, so a new process fails here until it is written down.
    """
    lines: list[str] = []
    for path in _prose_files():
        if path.relative_to(REPO).as_posix() in HISTORICAL:
            continue
        lines += path.read_text(encoding="utf-8").split("\n")
    missing: list[str] = []
    for name, group in sorted(PROBE_TARGETS.items()):
        size = len(group)
        bound = re.compile(
            r"(?<![A-Za-z0-9-])" + str(size) + r"(?![A-Za-z0-9-])" + REPORTED.pattern
        )
        marker = "`" + name + "`"
        if not any(marker in line and bound.search(line) for line in lines):
            missing.append(f"{name}: {size} reports, named in no line that also names it")
    assert not missing, "audit groups the prose reports nowhere:\n" + "\n".join(missing)


def _axiom_statements(path: Path) -> dict[str, str]:
    """Each axiom's declared proposition, whitespace-normalized.

    A declaration runs to the first line that starts a new one, which is any
    line beginning in column zero. Continuation lines are indented.
    """
    lines = path.read_text(encoding="utf-8").split("\n")
    statements: dict[str, str] = {}
    cursor = 0
    while cursor < len(lines):
        found = AXIOM.match(lines[cursor])
        if not found:
            cursor += 1
            continue
        body = [lines[cursor]]
        cursor += 1
        while cursor < len(lines) and lines[cursor][:1] in {" ", "\t"}:
            body.append(lines[cursor])
            cursor += 1
        text = " ".join(" ".join(body).split())
        statements[found.group(1)] = text.split(" : ", 1)[1]
    return statements


def test_sequencing_and_cooperation_are_declared_identically() -> None:
    """Five operation clauses, two propositions.

    `Hypermath.sequencingClausesAreCooperationClauses` is the kernel-level half
    of this: it inhabits one proposition twice, once from each operation's
    declarations. This is the source-level half, and it is what fails if anyone
    strengthens one of the duplicates without saying so. Those two cases have
    different repairs -- the theorem stops elaborating, this test names the pair
    that stopped agreeing -- so both are worth keeping.
    """
    statements = _axiom_statements(LAYERS / "L2Operations.lean")
    groups: dict[str, list[str]] = {}
    for name, statement in statements.items():
        groups.setdefault(statement, []).append(name)
    duplicated = {statement: tuple(sorted(names))
                  for statement, names in groups.items() if len(names) > 1}

    # A clause says something; the rest of the layer's parameters are opaque
    # data. Only the first kind can be redundant.
    clauses = sorted(names for statement, names in duplicated.items()
                     if "∀" in statement or "∃" in statement)
    assert clauses == [
        ("axCoop", "axSeq"),
        ("axCoopIdentity", "axSeqIdentityL", "axSeqIdentityR"),
    ], f"operation clause duplication changed: {clauses}"

    # Four accessors of one path type share an arity, which is not redundancy.
    # Pinned so that dropping one, or giving one a different type, is visible.
    others = sorted(names for statement, names in duplicated.items()
                    if "∀" not in statement and "∃" not in statement)
    assert others == [("pathEnd", "pathLength", "pathStart", "pathTrace")], others


def test_only_one_operation_clause_could_separate_the_two() -> None:
    """`axSeqAsymm` against `axCoopComm`, and nothing else.

    Every other sequencing clause is a cooperation clause. If a future clause
    mentions incongruence outside `axSeqAsymm`, the independence argument for
    `plusAndAdditionallyAreDistinct` has to be re-read, so name them here.
    """
    statements = _axiom_statements(LAYERS / "L2Operations.lean")
    separating = sorted(
        name for name, statement in statements.items()
        if "¬ (a =~ b)" in statement or "¬ (c =~ d)" in statement
    )
    assert separating == ["axSeqAsymm"], f"clauses mentioning incongruence: {separating}"


def _structures(path: Path) -> dict[str, dict[str, str]]:
    """Every structure in one file, keyed by its fully qualified name.

    Qualified, because `Countermodels.lean` declares six different structures
    called `PrefixAxioms` in six namespaces. A reader that keys on the bare name
    returns one of them and does not say which.
    """
    lines = path.read_text(encoding="utf-8").split("\n")
    stack: list[str] = []
    found: dict[str, dict[str, str]] = {}
    index = 0
    while index < len(lines):
        line = lines[index]
        opened = NAMESPACE_OPENS.match(line)
        if opened:
            stack.append(opened.group(1))
            index += 1
            continue
        closed = NAMESPACE_ENDS.match(line)
        if closed and stack and stack[-1] == closed.group(1):
            stack.pop()
            index += 1
            continue
        starts = STRUCTURE.match(line)
        if not starts:
            index += 1
            continue
        header = index
        while (header < len(lines)
               and not HEADER_ENDS.search(lines[header].split("--", 1)[0].rstrip())):
            header += 1
            if header - index > 8:  # not a structure with fields; leave it alone
                break
        if header - index > 8 or header >= len(lines):
            index += 1
            continue
        cursor, body = header + 1, []
        while cursor < len(lines):
            if FIELD.match(lines[cursor]):
                body.append([lines[cursor]])
            elif CONTINUATION.match(lines[cursor]) and body:
                body[-1].append(lines[cursor])
            elif not CONTINUATION.match(lines[cursor]):
                break
            cursor += 1
        fields: dict[str, str] = {}
        for chunk in body:
            # A trailing comment is not part of the statement, and these are
            # read by name, so a symbol named in one would otherwise count.
            plain = [part.split("--", 1)[0] for part in chunk]
            joined = " ".join(" ".join(plain).split())
            field, statement = joined.split(" : ", 1)
            fields[field] = statement
        qualified = ".".join(stack + [starts.group(1)])
        assert qualified not in found, f"two structures named {qualified}"
        found[qualified] = fields
        index = max(cursor, header + 1)
    return found


def _clause_statements(path: Path, name: str) -> dict[str, str]:
    """Each field of one clause structure, whitespace-normalized.

    Read from a model rather than from the layers because a model states every
    clause in full name form. The layers use the `~~`, `=~` and `≡` notations,
    which hide `Similar`, `Congruent` and `Simulation` from any scan that works
    on names.

    `name` may be bare or namespace-qualified, and it must resolve to exactly
    one structure. Both failure modes are raised rather than returned: the
    reader used to answer "no fields" for a name it could not find and "some
    fields" for a name it found more than once.
    """
    everything = _structures(path)
    hits = sorted(key for key in everything
                  if key == name or key.endswith("." + name))
    assert hits, f"{path.name} declares no structure named {name}"
    assert len(hits) == 1, f"{name} is ambiguous in {path.name}: {hits}"
    return everything[hits[0]]


# Symbols no clause mentions. Nothing about these alone is derivable, and no
# model is needed to know it. `pathLengthArithmeticClaim` and
# `compositionLengthAdditiveClaim` were each refuted by building one; the table
# says both were unreachable from the start, as is anything else stated about
# path length, path trace or the path successor by itself.
UNCONSTRAINED = ("pathLength", "pathStep", "pathTrace")

# Symbols exactly one clause mentions. Four of the five are named only by the
# clause that defines them off something else, so they carry no content of their
# own; `pathStart` and `pathEnd` are named only inside `axLimitDerives`, and
# there only at the one path it asserts to exist. At any given path they are as
# free as the three above.
MENTIONED_ONCE = ("Definition", "Discharge", "deriver", "pathEnd", "pathStart")


def _pre_closure_clause_count() -> int:
    """The clauses that precede the closing clauses of L0 §VIII.b and L2 §II.

    Measured from two sources that state them independently, so a change to
    either is a change to the number the prose may name.
    """
    transport = _clause_statements(
        REPO / "lean4" / "Hypermath" / "TransportCountermodel.lean", "FullAxioms")
    cycle = _clause_statements(
        REPO / "lean4" / "Hypermath" / "NondegenerateCycle.lean", "FullAxioms")
    preclosure = _clause_statements(
        REPO / "lean4" / "FullAxiomModel.lean", "PreClosureAxiomsWith")
    assert transport, "the transport model states no clauses"
    assert transport == cycle, (
        "the two pre-closure models no longer state the same clauses")
    assert set(preclosure) == set(transport), (
        "the parameterised pre-closure list no longer names the same clauses")
    return len(transport)


PRE_CLOSURE_CLAUSE_COUNT = _pre_closure_clause_count()
PERMITTED_IN_PROSE = frozenset(
    {FULL_CLAUSE_COUNT, PREFIX_CLAUSE_COUNT, PRE_CLOSURE_CLAUSE_COUNT})


def _clause_incidence() -> dict[str, list[str]]:
    clauses = _clause_statements(REPO / "lean4" / "FullAxiomModel.lean", "FullAxioms")
    assert len(clauses) == FULL_CLAUSE_COUNT, len(clauses)
    words = {name: set(WORD.findall(statement)) for name, statement in clauses.items()}
    return {parameter: sorted(name for name in clauses if parameter in words[name])
            for parameter in SOURCE_PARAMETERS}


# The five structures `Countermodels.lean` characterises the clause set
# through, with the size of each. Pinned separately from their union so that a
# clause moving from one list to another is reported as a move rather than
# passing.
#
# The fifth is the closing tier of L0 §VIII.b and L2 §II: the five clauses the
# closure added. It is a tier of its own rather than a sixth member of the
# prefix, because its clauses are properties of the relations --- reflexivity
# and symmetry of `~~`, transitivity of `=~`, the denial of the ground at
# `=~`, and symmetry of `congruentPath` --- and they say so about the whole
# relation rather than about a carrier.
CLAUSE_STRUCTURES = {
    "FreeFiltration.PrefixAxioms": 24,
    "FreeFiltration.OperationAxioms": 7,
    "FreeFiltration.ComposeAxioms": 3,
    "FreeFiltration.TransfiniteAxioms": 5,
    "FreeFiltration.ClosingAxioms": 5,
}


def test_ten_prefix_clauses_are_closes() -> None:
    """`the_closes_are_definitional` proves ten, and the prose now says ten.

    The reduction is quoted as twenty-nine to nineteen in three documents, and
    twenty-nine is 39 less this number. A close added or removed in the Lean
    moves it, and nothing else would report that.
    """
    fields = _clause_statements(REPO / "lean4" / "Countermodels.lean",
                                "FreeFiltration.PrefixAxioms")
    closes = sorted(name for name in fields if name.startswith("close"))
    assert len(closes) == 10, closes
    opaque = [name for name in closes if name.endswith("Opaque")]
    assert len(opaque) == 7, opaque


def test_the_five_clause_structures_partition_the_clause_set() -> None:
    """`all_forty_four_iff_twenty_four_conditions` covers *these* 44 clauses.

    The theorem joins five structures whose fields add up to the right number.
    Adding up is not the claim. The claim is that they are the same clauses the
    canonical list declares, each in exactly one of the five, and that is what
    this measures --- by name, not by count.

    It could not be measured until the reader above was fixed. `ComposeAxioms`
    and `TransfiniteAxioms` both wrap their binders, the old pattern required
    `where` on the opening line, and the reader returned an empty dict for each
    of them without saying so.
    """
    canonical = set(_clause_statements(
        REPO / "lean4" / "FullAxiomModel.lean", "FullAxioms"))
    assert len(canonical) == FULL_CLAUSE_COUNT, len(canonical)

    seen: dict[str, str] = {}
    for name, size in CLAUSE_STRUCTURES.items():
        fields = _clause_statements(REPO / "lean4" / "Countermodels.lean", name)
        assert len(fields) == size, f"{name}: {len(fields)} fields, expected {size}"
        for field in fields:
            assert field not in seen, f"{field} is in both {seen[field]} and {name}"
            seen[field] = name

    assert set(seen) == canonical, (
        f"not a partition --- unlisted: {sorted(canonical - set(seen))}, "
        f"extra: {sorted(set(seen) - canonical)}")


# The conditions as the fields of the two condition structures, and the
# namespace holding the model that refutes each. The Prop of a field is its name
# with the first letter raised; nothing else joins the two, so the join is
# checked. `Conditions` is the filtration group and `OperationConditions` the
# operation group; a model refuting one of the operations still carries all of
# `Conditions`, which is what makes it a statement about the operations alone.
CONDITION_GROUPS = {"FreeFiltration.Conditions": 8,
                    "FreeFiltration.OperationConditions": 3,
                    "FreeFiltration.ComposeConditions": 3,
                    "FreeFiltration.TransfiniteConditions": 5,
                    "FreeFiltration.ClosingConditions": 5}

# The whole structures a model of each group has to carry beside the conditions
# it names one by one. A model of the eight names the other seven singly and
# must not claim `Conditions`, which is what it is refuting. A model of the
# operations or of the transfinite layer has to stand on a carrier, so it
# carries the groups below it whole; the composition group answers to no
# carrier, so it carries nothing.
CARRIED_WHOLE = {
    "FreeFiltration.Conditions": (),
    "FreeFiltration.OperationConditions": ("Conditions",),
    "FreeFiltration.ComposeConditions": (),
    "FreeFiltration.TransfiniteConditions":
        ("Conditions", "OperationConditions", "ComposeConditions"),
    "FreeFiltration.ClosingConditions": (),
}
GROUP_STRUCTURES = tuple(sorted(
    {name.split(".")[-1] for name in CONDITION_GROUPS}))

NEEDS = re.compile(r"^namespace Needs([A-Za-z]+)$", re.M)
DERIVED = re.compile(r"^theorem ([a-z][A-Za-z]*)_is_implied_by_[a-z_]+\b", re.M)
HOLD = re.compile(r"^theorem ([a-z]+_hold[A-Za-z_]*)\s*:(.*?):=$", re.M | re.S)
PROP_OPENS = re.compile(r"^def ([A-Z][A-Za-z]*)\b")


def _prop_definitions(text: str) -> dict[str, list[str]]:
    """Every `def Name ... : Prop := body`, bodies normalized, keyed by name.

    A name may be declared in more than one namespace --- `Definition` is
    declared in four --- so the bodies are collected rather than overwritten and
    the caller says which names it expects to be unique.
    """
    found: dict[str, list[str]] = {}
    lines = text.splitlines(keepends=True)
    for index, line in enumerate(lines):
        opened = PROP_OPENS.match(line)
        if opened is None:
            continue
        run = [line]
        while ": Prop :=" not in "".join(run) and index + len(run) < len(lines):
            following = lines[index + len(run)]
            if not following.startswith("    "):
                break
            run.append(following)
        joined = "".join(run)
        if ": Prop :=" not in joined:
            continue
        body = [joined.split(": Prop :=", 1)[1]]
        cursor = index + len(run)
        while cursor < len(lines) and lines[cursor].startswith("  "):
            body.append(lines[cursor])
            cursor += 1
        found.setdefault(opened.group(1), []).append(
            " ".join("".join(body).split()))
    return found


def _condition_groups(path: Path) -> dict[str, set[str]]:
    """The Props of each condition structure, keyed by the structure."""
    groups = {}
    for structure, size in CONDITION_GROUPS.items():
        fields = _clause_statements(path, structure)
        assert len(fields) == size, f"{structure}: {sorted(fields)}"
        groups[structure] = {name[0].upper() + name[1:] for name in fields}
    return groups


def _model_namespaces(text: str) -> dict[str, str]:
    """Each `Needs...` namespace body, keyed by the condition it is named for."""
    found: dict[str, str] = {}
    for opened in NEEDS.finditer(text):
        name = opened.group(1)
        closing = f"\nend Needs{name}\n"
        stop = text.index(closing, opened.end())
        assert name not in found, f"two namespaces named Needs{name}"
        found[name] = text[opened.end():stop]
    return found


def test_each_condition_is_either_refuted_or_derived() -> None:
    """Every condition has a `Needs...` model or an `_is_implied_by_` proof.

    The four `*_iff_the_*` theorems check that the Props are the fields of their
    structures. This checks that the answers cover them --- one apiece, none
    twice, none left without one, and none with both. A condition with both
    would be a contradiction in the file rather than a gap in it, which is why
    the two sets are required to be disjoint and not merely to cover.
    """
    path = REPO / "lean4" / "Countermodels.lean"
    text = path.read_text(encoding="utf-8")
    groups = _condition_groups(path)
    props = set().union(*groups.values())
    assert len(props) == sum(len(group) for group in groups.values()), (
        "a condition name belongs to two groups")
    for prop in props:
        assert re.search(rf"^def {prop}\b", text, re.M), f"{prop} is not declared"
    refuted = set(_model_namespaces(text))
    derived = {name[0].upper() + name[1:] for name in DERIVED.findall(text)}
    assert not refuted & derived, f"both refuted and derived: {refuted & derived}"
    assert refuted | derived == props, (
        f"unanswered: {props - refuted - derived}, "
        f"answered but not a condition: {(refuted | derived) - props}")


def test_every_condition_prop_copies_its_field_word_for_word() -> None:
    """Each standalone Prop says what the field of its structure says.

    The three `*_iff_the_three`-shaped theorems prove the two readings agree up
    to definitional equality, which leaves the bound variable names free --- and
    those names are what the prose and the docstrings point at. Here they must
    match as text, for every condition in every group.
    """
    path = REPO / "lean4" / "Countermodels.lean"
    text = path.read_text(encoding="utf-8")
    defined = _prop_definitions(text)
    for structure in CONDITION_GROUPS:
        for field, statement in _clause_statements(path, structure).items():
            prop = field[0].upper() + field[1:]
            bodies = defined.get(prop, [])
            assert len(bodies) == 1, f"{prop} is defined {len(bodies)} times"
            assert bodies[0] == statement, (
                f"{prop} reads {bodies[0]!r}, {field} reads {statement!r}")


def test_every_model_names_its_whole_group_and_denies_one() -> None:
    """Each model names every condition in its own group, denying just its own.

    Lean checks that the statement is true, not that it is the statement meant.
    A model naming its own condition twice and one of the others not at all
    would prove a theorem, and the theorem would read as though it had done the
    work. Each model must also carry exactly the whole structures `CARRIED_WHOLE`
    assigns its group, since the interest of refuting one condition is that
    everything else still holds --- and "everything else" is a different list
    for a model that stands on a carrier than for one that does not.
    """
    path = REPO / "lean4" / "Countermodels.lean"
    text = path.read_text(encoding="utf-8")
    groups = _condition_groups(path)
    owner = {prop: structure
             for structure, props in groups.items() for prop in props}
    for own, body in _model_namespaces(text).items():
        claims = HOLD.findall(body)
        assert len(claims) == 1, f"Needs{own}: {[name for name, _ in claims]}"
        statement = " ".join(claims[0][1].split())
        for prop in groups[owner[own]]:
            hits = re.findall(rf"(\u00ac\s*)?\b{prop}\b", statement)
            assert len(hits) == 1, f"Needs{own} names {prop} {len(hits)} times"
            denied = bool(hits[0])
            assert denied == (prop == own), (
                f"Needs{own} {'denies' if denied else 'asserts'} {prop}")
        expected = CARRIED_WHOLE[owner[own]]
        for structure in GROUP_STRUCTURES:
            carried = re.findall(rf"(\u00ac\s*)?\b{structure}\b", statement)
            if structure in expected:
                assert len(carried) == 1 and not carried[0], (
                    f"Needs{own} does not assert {structure} whole")
            else:
                assert not carried, f"Needs{own} names {structure} as a whole"


def test_the_sharp_list_keeps_six_conditions_word_for_word() -> None:
    """`SharpConditions` weakens two conditions and copies the other six.

    Copies, in a file where a copy can drift. If one of the six is ever edited
    in one structure and not the other, `conditions_iff_six_and_two_implications`
    goes on proving something --- about two lists that no longer agree on what
    the other six say.
    """
    path = REPO / "lean4" / "Countermodels.lean"
    full = _clause_statements(path, "FreeFiltration.Conditions")
    sharp = _clause_statements(path, "FreeFiltration.SharpConditions")
    assert len(full) == 8 and len(sharp) == 8
    assert set(full) - set(sharp) == {"congruentDiagonalIsReach",
                                      "simulationDiagonalIsReach"}
    assert set(sharp) - set(full) == {"congruentDiagonalReaches",
                                      "reachedIsSelfSimulating"}
    for name in set(full) & set(sharp):
        assert full[name] == sharp[name], name


def test_the_sharp_transfinite_list_copies_its_three_word_for_word() -> None:
    """`SharpTransfiniteConditions` drops two conditions and copies the other three.

    The two it drops are the two with derivations rather than models, so this
    test and `test_each_condition_is_either_refuted_or_derived` have to agree
    about which two those are. If they ever stop agreeing, one of them is
    reporting a redundancy the file no longer proves.
    """
    path = REPO / "lean4" / "Countermodels.lean"
    full = _clause_statements(path, "FreeFiltration.TransfiniteConditions")
    sharp = _clause_statements(path, "FreeFiltration.SharpTransfiniteConditions")
    assert len(full) == 5 and len(sharp) == 3
    assert set(full) - set(sharp) == {"someStartAtGround", "someEndAtLimit"}
    assert not set(sharp) - set(full)
    for name in sharp:
        assert full[name] == sharp[name], name
    text = path.read_text(encoding="utf-8")
    derived = {name for name in DERIVED.findall(text)}
    assert derived == set(full) - set(sharp), (
        f"dropped {set(full) - set(sharp)} but derived {derived}")


def test_the_contentful_transfinite_clauses_drop_exactly_one() -> None:
    """`ContentfulTransfiniteAxioms` drops `axLimitDerives` and copies the rest.

    That clause is the one whose two halves became the two derivable
    conditions, so dropping exactly it is what makes the count twenty-eight
    rather than twenty-nine. The other four are copied, and a copy can drift.
    """
    path = REPO / "lean4" / "Countermodels.lean"
    full = _clause_statements(path, "FreeFiltration.TransfiniteAxioms")
    contentful = _clause_statements(
        path, "FreeFiltration.ContentfulTransfiniteAxioms")
    assert len(full) == 5 and len(contentful) == 4
    assert set(full) - set(contentful) == {"axLimitDerives"}
    assert not set(contentful) - set(full)
    for name in contentful:
        assert full[name] == contentful[name], name


def test_the_needed_prefix_clauses_drop_exactly_the_three_derivable() -> None:
    """`NeededPrefixAxioms` drops the three `three_of_the_fourteen_are_derivable`
    derives, and keeps every clause that proof consumes.

    The removal is safe only because the four consumed clauses survive it. If a
    later sharpening removes one of those four as well, the eleven stop carrying
    the fourteen and this test says which clause went missing.
    """
    path = REPO / "lean4" / "Countermodels.lean"
    full = _clause_statements(path, "FreeFiltration.ContentfulPrefixAxioms")
    needed = _clause_statements(path, "FreeFiltration.NeededPrefixAxioms")
    assert len(full) == 14 and len(needed) == 11
    assert set(full) - set(needed) == {
        "axGroundSelf", "axGroundSyntaxAx", "axFormClosesLoop"}
    assert not set(needed) - set(full)
    for name in needed:
        assert full[name] == needed[name], name
    for consumed in ("filtrationCongSim", "filtrationSimCong",
                     "axGroundSubstanceAx", "axSim"):
        assert consumed in needed, consumed


def test_the_operation_clauses_are_seven_names_for_four_statements() -> None:
    """The claim in `operationAxioms_iff_conditions`, checked rather than read.

    Its docstring says four of the seven clauses are carried by two of the three
    conditions. That is a statement about which clauses are literally the same
    proposition, and until now nothing compared them. `axSeq` and `axCoop` are
    one statement written twice; `axSeqIdentityR`, `axSeqIdentityL` and
    `axCoopIdentity` are one statement written three times.
    """
    path = REPO / "lean4" / "Countermodels.lean"
    clauses = _clause_statements(path, "FreeFiltration.OperationAxioms")
    conditions = _clause_statements(path, "FreeFiltration.OperationConditions")
    assert len(clauses) == 7 and len(conditions) == 3
    distinct = set(clauses.values())
    assert len(distinct) == 4, sorted(distinct)
    assert clauses["axSeq"] == clauses["axCoop"]
    assert (clauses["axSeqIdentityR"] == clauses["axSeqIdentityL"]
            == clauses["axCoopIdentity"])
    assert set(conditions.values()) < distinct
    spare = distinct - set(conditions.values())
    assert spare == {clauses["axSeq"]}, spare


def test_the_sharpened_transfinite_clauses_are_the_three_conditions() -> None:
    """Dropping the inert binder leaves the conditions word for word.

    `the_deriver_binder_is_inert` claims the four contentful transfinite clauses
    minus `axDeriverAtLimit` are `SharpTransfiniteConditions`. In Lean that is a
    biconditional, which would still hold if the statements had been rearranged;
    this checks they were not.
    """
    path = REPO / "lean4" / "Countermodels.lean"
    clauses = _clause_statements(
        path, "FreeFiltration.ContentfulTransfiniteAxioms")
    conditions = _clause_statements(
        path, "FreeFiltration.SharpTransfiniteConditions")
    assert len(clauses) == 4 and len(conditions) == 3
    kept = [body for name, body in clauses.items() if name != "axDeriverAtLimit"]
    assert kept == list(conditions.values())


def test_the_nine_prefix_clauses_are_six_conditions_and_one_cycle() -> None:
    """The last layer's shape, which is the headline of the whole reduction.

    Six of the nine clauses are fields of `Conditions` character for character.
    The other three are the diagonal cycle, and the two conditions they are not
    among are the two equivalences. If that split ever stops holding, the claim
    that `three_implications_are_two_equivalences` isolates the entire gap is no
    longer true, whatever the biconditionals still prove.
    """
    path = REPO / "lean4" / "Countermodels.lean"
    eleven = _clause_statements(path, "FreeFiltration.NeededPrefixAxioms")
    nine = _clause_statements(path, "FreeFiltration.SharpPrefixAxioms")
    conditions = _clause_statements(path, "FreeFiltration.Conditions")
    assert len(eleven) == 11 and len(nine) == 9 and len(conditions) == 8
    assert set(eleven) - set(nine) == {
        "axGroundSubstanceAx", "axGroundSemanticsAx", "traceLevels"}
    assert set(nine) - set(eleven) == {"axImageSimilar"}
    for name in set(nine) & set(eleven):
        assert eleven[name] == nine[name], name
    assert eleven["traceLevels"].startswith(nine["axImageSimilar"] + " \u2227 ")

    shared = set(nine.values()) & set(conditions.values())
    assert len(shared) == 6, sorted(set(nine.values()) - set(conditions.values()))
    cycle = {name for name, body in nine.items() if body not in shared}
    assert cycle == {"axSyntaxRequiresSubstance", "axSubstanceRequiresSemantics",
                     "axSemanticsRequiresSyntax"}, cycle
    equivalences = {name for name, body in conditions.items()
                    if body not in shared}
    assert equivalences == {"congruentDiagonalIsReach",
                            "simulationDiagonalIsReach"}, equivalences


COUNTERMODEL_COSTS = {
    (): 149,
    ("propext",): 48,
    ("Quot.sound", "propext"): 23,
    ("Classical.choice", "Quot.sound", "propext"): 5,
}


def test_every_countermodel_report_has_a_pinned_cost() -> None:
    """The countermodel group was the last one checked only for exotic axioms.

    Every other probe group compares against an exact dependency table; this one
    asked only that no axiom outside the Lean builtins appear, so a report's
    cost could change and the audit would still pass once the source digest was
    refreshed alongside it --- which is what refreshing a digest is for. The
    table now says what each of the reports costs, and these are the shapes it
    has.
    """
    from hypermath_foundations._reports import (
        COUNTERMODEL_DEPENDENCIES, COUNTERMODEL_TARGETS)

    assert set(COUNTERMODEL_DEPENDENCIES) == set(COUNTERMODEL_TARGETS)
    assert len(COUNTERMODEL_TARGETS) == sum(COUNTERMODEL_COSTS.values())

    shapes: dict[tuple[str, ...], int] = {}
    for dependencies in COUNTERMODEL_DEPENDENCIES.values():
        assert dependencies == sorted(dependencies), dependencies
        shapes[tuple(dependencies)] = shapes.get(tuple(dependencies), 0) + 1
    assert shapes == COUNTERMODEL_COSTS


def test_the_vocabulary_pair_still_costs_two_different_things() -> None:
    """The exhibit dies quietly if both halves become free, and it can.

    `test_the_axiom_pair_states_one_fact_in_two_vocabularies` checks that the
    two halves state the same fact. They would still state the same fact if the
    expensive one were reproved by hand, and then the pair would demonstrate
    nothing while every other check passed. This is the check that would notice:
    one half costs something and the other costs nothing.
    """
    from hypermath_foundations._reports import COUNTERMODEL_DEPENDENCIES

    prefix = "HypermathCountermodel.AxiomsMeasureVocabulary."
    by_library = COUNTERMODEL_DEPENDENCIES[prefix + "the_image_misses_the_ground_by_library"]
    by_hand = COUNTERMODEL_DEPENDENCIES[prefix + "the_image_misses_the_ground_by_hand"]
    assert by_library, "the library half stopped costing anything"
    assert not by_hand, "the hand-written half started costing something"


BINDER_OPENS, BINDER_CLOSES = "([{⟨⦃", ")]}⟩⦄"


def _binder_region(body: str) -> int:
    """Where `body`'s binders stop and its conclusion starts.

    The first `:` outside every bracket. Collecting binder names without this
    cut treats each parenthesis of the conclusion as a binder group and renames
    whatever heads it --- which is exactly the structure name that tells two
    statements apart, so two different theorems normalize to one string and the
    check below reports a clash that is not there. Two such pairs were reported
    before this cut existed, and both were `NeededPrefixAxioms` against
    `SharpPrefixAxioms`.
    """
    depth = 0
    for index, character in enumerate(body):
        if character in BINDER_OPENS:
            depth += 1
        elif character in BINDER_CLOSES:
            depth -= 1
        elif character == ":" and depth == 0 and body[index:index + 2] != ":=":
            return index
    return len(body)


def _proposition(statement: str) -> str:
    """`statement` with its name, binder style and bound names normalized away.

    Two theorems state the same proposition when this agrees: an implicit and
    an explicit binder are the same binder here, and a bound name is its
    position.
    """
    body = re.sub(r"^\s*(?:theorem|lemma)\s+[A-Za-z_][A-Za-z0-9_'.]*", "",
                  statement)
    for opened, closed in (("{", "("), ("}", ")"), ("⦃", "("), ("⦄", ")")):
        body = body.replace(opened, closed)
    bound: list[str] = []
    depth, group = 0, None
    for index, character in enumerate(body[:_binder_region(body)]):
        if character in BINDER_OPENS:
            if depth == 0 and character == "(":
                group = index + 1
            depth += 1
        elif character in BINDER_CLOSES:
            depth -= 1
            if depth == 0 and group is not None:
                inner = body[group:index]
                head = inner.split(":")[0] if ":" in inner else ""
                bound.extend(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", head))
                group = None
    renamed: dict[str, str] = {}
    for name in bound:
        renamed.setdefault(name, f"v{len(renamed)}")
    if renamed:
        body = re.sub(r"\b(" + "|".join(map(re.escape, renamed)) + r")\b",
                      lambda found: renamed[found.group(0)], body)
    return " ".join(body.split())


def _qualified_statements() -> dict[str, str]:
    """Every theorem of `Countermodels.lean` under its namespaced name.

    `_theorem_statements` is keyed by module and namespace and loses nothing,
    but it does not normalize binders, and two theorems that say the same thing
    with differently named variables are the subject here. That normalization
    is the whole of what this reader adds, and it is confined to one file
    because the question is.

    It once said `_theorem_statements` dropped one of nine colliding pairs. The
    real figure was 89 declarations of 1052, which is the kind of number that
    should have been measured rather than written; it is now zero, and
    `test_the_statement_reader_sees_every_declaration` keeps it there.
    """
    lines = (REPO / "lean4" / "Countermodels.lean").read_text(
        encoding="utf-8").split("\n")
    statements: dict[str, str] = {}
    stack: list[str] = []
    for index, line in enumerate(lines):
        opened = re.match(r"^namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)", line)
        if opened:
            stack.append(opened.group(1))
            continue
        if re.match(r"^end\s", line) and stack:
            stack.pop()
            continue
        found = PAIRING_DECLARES.match(line)
        if not found:
            continue
        block = [line]
        for following in lines[index + 1:]:
            if following and not following[0].isspace():
                break
            block.append(following)
        name = ".".join(stack + [found.group(1)])
        assert name not in statements, f"{name} is declared twice"
        statements[name] = _before_proof(" ".join(" ".join(block).split()))
    return statements


def test_no_proposition_is_proved_twice_for_the_same_price() -> None:
    """A second proof of a proposition earns its line by costing less.

    `ground_is_not_an_image` was proved twice in this file: once in the
    transfinite section, where it was wanted as a lemma, and once eleven
    hundred lines above it, where the question it answers was finally asked.
    Lean caught that pair, because the two proofs chose the same name. It would
    not have caught them under two names, and nothing else here would have
    either --- the file would carry one fact as two theorems, each with a
    docstring claiming it.

    So this is the rule that
    `test_the_vocabulary_pair_still_costs_two_different_things` applies to the
    one pair it knows about, made general: two theorems may state one
    proposition, and then their proofs have to differ in what they spend. That
    pair passes because the library half costs `propext` and the hand-written
    half costs nothing. A re-proof written by someone who could not find the
    first one costs exactly what the first one costs, and fails here.
    """
    from hypermath_foundations._reports import COUNTERMODEL_DEPENDENCIES

    grouped: dict[tuple[str, str], list[str]] = {}
    for name, statement in _qualified_statements().items():
        namespace, _, _ = name.rpartition(".")
        grouped.setdefault((namespace, _proposition(statement)), []).append(name)

    for (_, proposition), names in sorted(grouped.items()):
        if len(names) == 1:
            continue
        costs = {}
        for name in names:
            assert name in COUNTERMODEL_DEPENDENCIES, (
                f"{name} states what {sorted(set(names) - {name})} states and "
                "is not registered, so nothing compares what they cost")
            costs[name] = tuple(COUNTERMODEL_DEPENDENCIES[name])
        assert len(set(costs.values())) == len(names), (
            f"these state `{proposition}` and cost the same: {costs}")

NOT_SIGN = "\u00ac"
FOR_ALL = "\u2200"
TYPE_BINDER = "\u03b1 : Type"
ARROW_STATEMENT = re.compile(r"\(\u2200 x, [^()]+\)")
TRIANGLE = (
    "\u2200 x, Reach g f S x \u2192 C x x",
    "\u2200 x, C x x \u2192 E x x",
    "\u2200 x, E x x \u2192 Reach g f S x",
)
HUB = (
    "\u2200 x, C x x \u2192 Reach g f S x",
    "\u2200 x, Reach g f S x \u2192 E x x",
)


def _theorem_statement(name: str) -> str:
    """The statement of `name`, whitespace-normalized, with its proof removed."""
    text = (REPO / "lean4" / "Countermodels.lean").read_text(encoding="utf-8")
    opens = [i for i in range(len(text)) if text.startswith("theorem " + name + " :", i)]
    assert len(opens) == 1, f"{name} is declared {len(opens)} times, not once"
    body = text[opens[0]:]
    cuts = [i for i in (body.find(" :=\n"), body.find(" := by\n")) if i != -1]
    assert cuts, f"{name} has no proof"
    return " ".join(body[:min(cuts)].split())


def test_the_two_lists_are_the_same_two_lists_in_both_theorems() -> None:
    """The claim is about two named lists, and Lean cannot check they are named.

    `neither_list_has_a_removable_member` would typecheck if a conjunct dropped
    the same member twice, or dropped a statement that is in neither list, or if
    the lists it quantifies over were not the two that
    `the_two_lists_agree_over_the_six` proves equivalent. Each of those reads as
    though the work had been done. The guard checks the five conjuncts against
    the two lists: three for the triangle and two for the hub, every conjunct
    mentioning its whole list and nothing else, and each member the dropped one
    exactly once.
    """
    agree = _theorem_statement("the_two_lists_agree_over_the_six")
    for member in TRIANGLE + HUB:
        assert "(" + member + ")" in agree, f"{member} is not in the equivalence"

    dropped = _theorem_statement("neither_list_has_a_removable_member")
    conjuncts = dropped.split(NOT_SIGN + " " + FOR_ALL + " (" + TYPE_BINDER + ")")[1:]
    assert len(conjuncts) == 5, f"{len(conjuncts)} conjuncts, not five"

    conclusions = []
    for conjunct, whole in zip(conjuncts, (TRIANGLE,) * 3 + (HUB,) * 2):
        assert "SixSharedClauses g f S C E" in conjunct, "the background is missing"
        arrows = [found[1:-1] for found in ARROW_STATEMENT.findall(conjunct)]
        assert len(arrows) == len(whole), f"{len(arrows)} members, not {len(whole)}"
        assert set(arrows) == set(whole), f"{set(arrows) ^ set(whole)} is off-list"
        conclusions.append(arrows[-1])

    assert sorted(conclusions[:3]) == sorted(TRIANGLE), "a triangle member is dropped twice"
    assert sorted(conclusions[3:]) == sorted(HUB), "a hub member is dropped twice"


IFF = "\u2194"
ARROW = "\u2192"


def test_the_split_conditions_spend_both_biconditionals() -> None:
    """The last connective, and the only one that changes the residue.

    A biconditional counted as one field is two implications, and in this list
    one half of each is free. The guard checks that the two fields which arrive
    are halves of the two which leave --- not new statements wearing their
    names, which is what would make the count look preserved while the content
    moved.
    """
    path = REPO / "lean4" / "Countermodels.lean"
    whole = _clause_statements(path, "FreeFiltration.Conditions")
    split = _clause_statements(path, "FreeFiltration.SplitPrefixConditions")
    assert len(whole) == len(split) == 8

    biconditional = {k: v for k, v in whole.items() if IFF in v}
    assert set(biconditional) == {
        "congruentDiagonalIsReach", "simulationDiagonalIsReach"}
    assert not [k for k, v in split.items() if IFF in v or AND in v]

    kept = {k for k in whole if k in split}
    assert set(whole) - kept == set(biconditional)
    for k in kept:
        assert whole[k] == split[k], f"{k} was reworded, not copied"

    arrived = {k: v for k, v in split.items() if k not in whole}
    assert set(arrived) == {"congruentIntoReach", "reachIntoSimulation"}
    for name, statement in arrived.items():
        assert ARROW in statement, name
        matches = []
        for k, v in biconditional.items():
            left, right = v.split(IFF)
            sides = (left.split(", ")[-1].strip(), right.strip())
            if all(side in statement for side in sides):
                matches.append(k)
        assert len(matches) == 1, f"{name} is not a half of one biconditional: {matches}"


def test_both_halves_that_survive_are_refuted_somewhere() -> None:
    """Each surviving half is one the file already knew it could not derive."""
    path = REPO / "lean4" / "Countermodels.lean"
    text = path.read_text(encoding="utf-8")
    for theorem, model in [
        ("the_descending_half_is_not_derivable", "NeedsCongruentDiagonalIsReach"),
        ("the_rising_half_is_not_derivable", "NeedsSimulationDiagonalIsReach"),
    ]:
        start = text.index(f"namespace {model}")
        body = text[start:text.index(f"end {model}", start)]
        assert f"theorem {theorem}" in body, f"{model} lost {theorem}"


AND = "\u2227"
EXISTS = "\u2203"


def test_a_conjunction_splits_under_forall_and_not_under_exists() -> None:
    """The two kinds of conjunctive clause, told apart by their binder.

    Both kinds read the same to a scan that only looks for the connective, and
    the whole normal form turns on the difference: the first kind is two
    clauses being written as one, the second is one clause that no convention
    can turn into two.
    """
    path = REPO / "lean4" / "Countermodels.lean"
    splittable = {
        "FreeFiltration.ComposeAxioms": "axComposeIdentity",
        "FreeFiltration.ComposeConditions": "unitalUpToCp",
        "FreeFiltration.SharpTransfiniteConditions": "succEscapes",
    }
    for name, field in splittable.items():
        fields = _clause_statements(path, name)
        conjunctive = {k for k, v in fields.items() if AND in v}
        assert conjunctive == {field}, f"{name}: {conjunctive}"
        assert EXISTS not in fields[field], (
            f"{name}.{field} binds a witness and cannot be split")

    ops = _clause_statements(path, "FreeFiltration.OperationConditions")
    assert len(ops) == 3
    for field, statement in ops.items():
        assert AND in statement and EXISTS in statement, (
            f"OperationConditions.{field} is not a witness conjunction")


def test_the_split_lists_have_one_more_field_and_no_conjunction() -> None:
    """Splitting is checked to have happened, not just to have been claimed."""
    path = REPO / "lean4" / "Countermodels.lean"
    pairs = [
        ("FreeFiltration.ComposeAxioms", "FreeFiltration.SplitComposeAxioms"),
        ("FreeFiltration.ComposeConditions", "FreeFiltration.SplitComposeConditions"),
        ("FreeFiltration.SharpTransfiniteConditions",
         "FreeFiltration.SplitTransfiniteConditions"),
    ]
    for whole, split in pairs:
        before = _clause_statements(path, whole)
        after = _clause_statements(path, split)
        assert len(after) == len(before) + 1, f"{split}: {len(after)}"
        assert not [k for k, v in after.items() if AND in v], (
            f"{split} still carries a conjunction")
        kept = {k for k in before if k in after}
        for k in kept:
            assert before[k] == after[k], f"{split}.{k} was reworded, not copied"
        conjunct = next(v for k, v in before.items() if AND in v)
        halves = [h.strip() for h in conjunct.split(AND)]
        arrived = [after[k] for k in after if k not in before]
        assert len(arrived) == 2, f"{split}: {arrived}"
        for half in halves:
            assert any(half in a for a in arrived), f"{split} lost {half!r}"


def test_the_axiom_pair_states_one_fact_in_two_vocabularies() -> None:
    """The exhibit that an axiom report is a report about the proof's words.

    If the two ever stop stating the same thing the pair proves nothing, and
    nothing else in the repository would notice.
    """
    path = REPO / "lean4" / "Countermodels.lean"
    text = path.read_text(encoding="utf-8")
    start = text.index("namespace AxiomsMeasureVocabulary")
    body = text[start:text.index("end AxiomsMeasureVocabulary", start)]
    claims = re.findall(r"theorem (\w+) : (.+?) :=\n(.+?)\n", body)
    assert len(claims) == 2, claims
    (one, said, proof_one), (two, also, proof_two) = claims
    assert said == also, f"{one} and {two} no longer state one fact"
    assert "Nat.succ_ne_zero" in proof_one and "noConfusion" not in proof_one
    assert "noConfusion" in proof_two and "Nat.succ_ne_zero" not in proof_two


DROPS = re.compile(r"^namespace Drops([A-Za-z]+)$", re.M)


def test_each_arrow_of_the_cycle_has_a_model() -> None:
    """Three models, one per arrow, each carrying the six and denying one.

    These are clause models rather than condition models, which is why they are
    named `Drops...` and not `Needs...`: `test_each_condition_is_either_refuted_
    or_derived` requires every `Needs` namespace to be a condition, and an arrow
    of the cycle is not one. Nothing else would have caught a model filed under
    the wrong prefix, so the split is checked here.
    """
    path = REPO / "lean4" / "Countermodels.lean"
    text = path.read_text(encoding="utf-8")
    assert set(DROPS.findall(text)) == {
        "ReachIntoCongruent", "CongruentIntoSimulation", "SimulationIntoReach"}

    nine = _clause_statements(path, "FreeFiltration.SharpPrefixAxioms")
    six = _clause_statements(path, "FreeFiltration.SixSharedClauses")
    assert len(nine) == 9 and len(six) == 6
    assert not set(six) - set(nine)
    for name in six:
        assert nine[name] == six[name], name
    assert set(nine) - set(six) == {
        "axSyntaxRequiresSubstance", "axSubstanceRequiresSemantics",
        "axSemanticsRequiresSyntax"}

    for opened in DROPS.finditer(text):
        name = opened.group(1)
        body = text[opened.end():text.index(f"\nend Drops{name}\n", opened.end())]
        assert "SixSharedClauses" in body, f"Drops{name} does not carry the six"
        assert body.count("\u00ac (\u2200 x") == 1, (
            f"Drops{name} denies {body.count(chr(172) + ' (' + chr(8704) + ' x')}"
            " statements, not one")


def test_the_clause_set_never_mentions_the_path_internals() -> None:
    """What the 39 clauses leave untouched, measured rather than discovered.

    `congruentPath` needed `FullAxiomsWith` to vary it, because three clauses
    name it. These need nothing: every model may read them however it likes and
    all 39 clauses still hold. The documented reading of `congruentPath` ---
    agreement on `(start, end, path trace, quantification)` --- is built out of
    four symbols, and three of them are in the two lists below. That is why
    `tuple_reading_consistent_and_conditional` relocates its missing assumption
    instead of removing one: there is nothing underneath to remove it against.

    What this reads is a scan, and a scan is not the claim. Until 2026-09-21 it
    was the only thing standing at the whole set:
    `the_unmentioned_are_unconstrained` is a theorem about the twenty-four
    clauses of the prefix, and the sentence above is about all of them.
    `the_unmentioned_are_unconstrained_at_thirty_nine` is now the same result
    over the clause set this scans, and the guard below holds the structure it
    is stated over to these clauses one field at a time.
    """
    incidence = _clause_incidence()
    free = tuple(sorted(name for name, hits in incidence.items() if not hits))
    assert free == UNCONSTRAINED, f"unconstrained symbols changed: {free}"

    once = tuple(sorted(name for name, hits in incidence.items() if len(hits) == 1))
    assert once == MENTIONED_ONCE, f"singly-mentioned symbols changed: {once}"

    assert incidence["pathStart"] == ["axLimitDerives"] == incidence["pathEnd"]


#: The four structures `FullAxiomsCarrying` is assembled out of, with the size
#: of each. The prefix is read from the carrying version because that is the
#: text the assembly copied; `carrying_iff_prefix` ties that to `PrefixAxioms`
#: in the kernel, and the field names are compared here as well.
CARRIED_FROM = {
    "PrefixAxiomsCarrying": 24,
    "OperationAxioms": 7,
    "ComposeAxioms": 3,
    "TransfiniteAxioms": 5,
    "ClosingAxioms": 5,
}
#: The zero row, under the names the carrying structures give it.
CARRIED_SYMBOLS = ("pl", "ps", "pt")
CARRIED_PARAMETERS = (
    "(pl : Path → Form) (ps : Form → Form → Path) (pt : Path → Form)")


def test_the_zero_row_is_free_at_every_clause_there_is() -> None:
    """The freedom was proved at 24 and read at 39, and the gap was a scan.

    `the_unmentioned_are_unconstrained` is a theorem about
    `FreeFiltration.PrefixAxioms`: 24 clauses. The sentence it is read as ---
    the one the guard above writes, that every model may read the three
    however it likes and all 39 clauses still hold --- is about fifteen more
    clauses than the theorem mentions. Nothing was false. The scan is right,
    the theorem is right, and neither of them is the claim: a word the scan
    failed to find and a word that is not there look the same from outside,
    which is the reason that file gives for mechanizing the zero row in the
    first place, and it gives another for doing it again here --- a freedom
    proved against 24 clauses has to be re-checked against the rest.

    `FullAxiomsCarrying` is that re-check. What makes it one is that every
    field is the clause it copies, so this compares them: same names, same
    statements, all 44, and none of the three carried symbols occurring in any
    of them. The substitution to beat is bundling: four fields holding the four
    structures rather than 39 holding their clauses. The freedom proof cannot
    see the difference --- `cases` then `constructor <;> assumption` closes it
    either way, because no goal mentions the carried symbols either way, and it
    would then be proving nothing about them at all. The round trip can see it,
    but only while its own proof is left alone: with the bundle in place it
    fails on two prefix fields, and rewriting it to project the four fields out
    is two lines, after which the file compiles with no errors and all three
    theorems are still axiom-free. Lean refuses that substitution in one
    particular proof. This refuses it however the proof is written.

    Two things are not claimed. The statements are compared after the reader
    has normalized whitespace, so a rewrap is invisible and is meant to be.
    And the assembly is held to the four structures, not to the clause files:
    `test_the_five_clause_structures_partition_the_clause_set` is what holds
    those five to the declared clause set, and this stands on it.
    """
    path = REPO / "lean4" / "Countermodels.lean"
    structures = _structures(path)
    home = "HypermathCountermodel.FreeFiltration."
    carrying = structures[home + "FullAxiomsCarrying"]

    sources: dict[str, tuple[str, str]] = {}
    for name, size in CARRIED_FROM.items():
        fields = structures[home + name]
        assert len(fields) == size, (name, len(fields))
        for field, statement in fields.items():
            assert field not in sources, f"two of the four declare {field}"
            sources[field] = (name, statement)
    assert len(sources) == FULL_CLAUSE_COUNT, len(sources)

    assert set(carrying) == set(sources), {
        "assembled and not a clause": sorted(set(carrying) - set(sources)),
        "a clause and not assembled": sorted(set(sources) - set(carrying))}

    drifted = [f"{field}, copied from {sources[field][0]}"
               for field in carrying if carrying[field] != sources[field][1]]
    assert not drifted, ("assembled fields that are no longer the clause they "
                         "copy:\n" + "\n".join(drifted))

    assert (set(structures[home + "PrefixAxiomsCarrying"])
            == set(structures[home + "PrefixAxioms"])), (
        "the prefix the assembly copied is no longer the prefix of the "
        "partition")

    named = sorted(field for field, statement in carrying.items()
                   if set(CARRIED_SYMBOLS) & set(WORD.findall(statement)))
    assert not named, ("clauses naming a carried symbol, which would make the "
                       f"freedom theorem false rather than trivial: {named}")

    lines = path.read_text(encoding="utf-8").split("\n")
    opens = [index for index, line in enumerate(lines)
             if line.startswith("structure FullAxiomsCarrying")]
    assert len(opens) == 1, opens
    closes = next(index for index in range(opens[0], len(lines))
                  if HEADER_ENDS.search(lines[index]))
    signature = " ".join(" ".join(lines[opens[0]:closes + 1]).split())
    assert CARRIED_PARAMETERS in signature, signature

    declared = _lean_names(REPO)
    absent = [name for name in ("carrying_iff_the_whole_clause_set",
                                "carried_symbols_are_free_at_forty_four",
                                "the_unmentioned_are_unconstrained_at_forty_four")
              if name not in declared]
    assert not absent, "the assembly is stated and not used: " + ", ".join(absent)


def test_the_ordinal_application_is_mentioned_by_no_clause() -> None:
    """`ordinalApply` is free at both levels, which is why §IV stays propositions.

    It is a definition rather than a source parameter --- `ordinatics.apply` ---
    so `_clause_incidence` does not report on it, and no clause mentions it
    either. `Ordinatics.Transfinite.apply_is_free` says no law of the interface
    constrains that field, and this says no clause of this repository does.
    Between them, `Hypermath.ordinalApplyUnconstrained` is not a claim about one
    construction: nothing anywhere pins the ordinal application, so the three
    proposed action laws in §IV were never reachable.

    `ordinalLimit` and `ordinalSucc` are the control. They are projections of
    the same instance and clauses do mention them, so a scan that saw nothing
    would fail here before it could report `ordinalApply` free.
    """
    clauses = _clause_statements(REPO / "lean4" / "FullAxiomModel.lean", "FullAxioms")
    assert len(clauses) == FULL_CLAUSE_COUNT, len(clauses)
    words = {name: set(WORD.findall(statement)) for name, statement in clauses.items()}

    applications = sorted(name for name, seen in words.items() if "ordinalApply" in seen)
    assert applications == [], f"a clause now constrains ordinalApply: {applications}"

    limits = sorted(name for name, seen in words.items() if "ordinalLimit" in seen)
    assert limits, "the scan saw no ordinalLimit, so it is reading nothing"
    successors = sorted(name for name, seen in words.items() if "ordinalSucc" in seen)
    assert successors == ["axSuccExtends"], successors


def test_three_clauses_cover_every_path_symbol() -> None:
    """What `PathClauses` has to contain, and why varying it disturbs nothing.

    `HypermathFullAxiomModel.PathClauses` opens `compose`, `pathGround` and
    `congruentPath` together, and concludes that the other 36 clauses are
    untouched. That conclusion is this measurement: the clauses mentioning any
    of the three are the same three clauses, so a fourth one naming any of them
    would put §XIV's reasoning out of date.
    """
    incidence = _clause_incidence()
    covering = sorted(set(incidence["compose"]) | set(incidence["pathGround"])
                      | set(incidence["congruentPath"]))
    assert covering == ["axComposeAssoc", "axComposeIdentity",
                         "axComposeNonempty", "axCongruentPathSymm"], covering


def test_the_incidence_scan_reads_the_whole_clause_set() -> None:
    """A scan that matched nothing would report every symbol free.

    So check the other direction as well: every one of the 44 clauses names at
    least one declared symbol, and `Form` alone accounts for 34 of them. Neither
    number survives a scan that is reading less of the structure than it thinks.
    """
    incidence = _clause_incidence()
    assert len(incidence["Form"]) == 34, len(incidence["Form"])

    named = {name for hits in incidence.values() for name in hits}
    clauses = set(_clause_statements(REPO / "lean4" / "FullAxiomModel.lean", "FullAxioms"))
    assert named == clauses, f"clauses naming no declared symbol: {sorted(clauses - named)}"


ARROW_CONSTRUCTOR = re.compile(r"^  \| ([A-Za-z][A-Za-z0-9_']*)$")
HOLDS_BRANCH = re.compile(r"^  \| \.([A-Za-z][A-Za-z0-9_']*) => (.+)$")
NAMED_ARROW = re.compile(r"Arrow\.([A-Za-z][A-Za-z0-9_']*)")
APPLIED_ARROW = re.compile(r"holds m \.([A-Za-z][A-Za-z0-9_']*)")
# Every hypothesis of the minimality theorem, not the two it happens to have:
# a third exclusion is exactly the way the claim would weaken unnoticed.
EXCLUSION = re.compile(r"\(h[0-9]+ :")


def _block(text: str, opener: str) -> list[str]:
    """The indented run of lines under `opener`, up to the first blank line."""
    start = text.index(opener) + len(opener)
    body = text[start:]
    return body[:body.index(chr(10) + chr(10))].splitlines()


def test_the_arrow_vocabulary_is_the_five_the_six_do_not_give() -> None:
    """Five arrows, because the sixth is already a shared clause.

    Between three diagonal predicates there are six arrows. `filtrationSimCong`
    at `y := x` is one of them and is free at every setting, so a vocabulary of
    five is the whole vocabulary --- and a minimality claim over five arrows
    means nothing if a sixth is quietly missing for a different reason. The
    guard checks the count, that every constructor has a branch and every branch
    a constructor, and that the one arrow `holds` does not name is the one the
    six clauses supply.
    """
    path = REPO / "lean4" / "Countermodels.lean"
    text = path.read_text(encoding="utf-8")

    constructors = [m.group(1) for line in _block(text, "inductive Arrow where" + chr(10))
                    for m in [ARROW_CONSTRUCTOR.match(line)] if m]
    branches = {}
    for line in _block(text, "def holds (m : Setting) : Arrow " + chr(0x2192) + " Prop" + chr(10)):
        m = HOLDS_BRANCH.match(line)
        assert m, f"unreadable branch of holds: {line!r}"
        branches[m.group(1)] = m.group(2)

    assert len(constructors) == 5, constructors
    assert sorted(branches) == sorted(constructors), (sorted(branches), sorted(constructors))

    reach = "Reach m.ground m.step m.S x"
    cong = "m.C x x"
    sim = "m.E x x"
    stated = set()
    for name, statement in branches.items():
        sides = [side for side in (reach, cong, sim) if side in statement]
        assert len(sides) == 2, f"{name} is not an arrow between two diagonals: {statement}"
        head, tail = statement.split(" " + chr(0x2192) + " ")
        stated.add((head.split(", ")[-1].strip(), tail.strip()))

    everything = {(a, b) for a in (reach, cong, sim) for b in (reach, cong, sim) if a != b}
    assert everything - stated == {(sim, cong)}, sorted(everything - stated)
    assert "filtrationSimCong :" in text, "the free arrow is no longer a shared clause"


def test_the_pairs_the_minimality_theorem_excludes_are_the_hub_itself() -> None:
    """The two pairs it refuses to refute are the hub's own two orderings.

    A minimality claim that quietly excluded a third pair would be a weaker
    claim wearing the same name, and the exclusions are hypotheses rather than
    cases, so nothing else in the file would notice. The guard reads them out of
    the theorem and checks against the definition of `Hub`.
    """
    path = REPO / "lean4" / "Countermodels.lean"
    text = path.read_text(encoding="utf-8")

    hub = APPLIED_ARROW.findall(
        text[text.index("def Hub (m : Setting) : Prop :="):].split(chr(10) + chr(10))[0])
    assert len(hub) == 2 and len(set(hub)) == 2, hub

    start = text.index("theorem no_other_pair_of_arrows_is_the_hub")
    statement = text[start:text.index(" := by" + chr(10), start)]
    excluded = set()
    for line in statement.splitlines():
        if not EXCLUSION.search(line):
            continue
        named = NAMED_ARROW.findall(line)
        assert len(named) == 2, line
        excluded.add(tuple(named))

    assert excluded == {tuple(hub), tuple(reversed(hub))}, sorted(excluded)


NUMBER_WORD = {
    2: "two", 3: "three", 11: "eleven", 12: "twelve", 13: "thirteen",
    14: "fourteen",
    41: "forty-one", 44: "forty-four", 49: "forty-nine",
}
#: A key in the audit's command table. The indent used to be written into this
#: pattern as sixteen spaces, which is a claim about where the table sits in its
#: enclosing blocks rather than about what a command is.
COMMAND_KEY = re.compile(r'^\s+"([a-z_]+)": \[executable,')

#: A check the audit writes into the report itself, rather than one it runs. The
#: name is matched where the assignment ends, so updating a field of a check
#: already in the report is not one of these.
DERIVED_CHECK = re.compile(r'report\["checks"\]\["([a-z_]+)"\]\s*=[^=]')

#: Three or more names in code style, run together by the punctuation these
#: notes list with.
CODE_RUN = re.compile(r"`[a-z_]+`(?:[,;)\s]+(?:and\s+)?`[a-z_]+`){2,}")

#: A clause saying it is about some of a set rather than all of it.
NAMING_SOME = re.compile(r"\bof (?:them|those|these|the \w+)\b")

#: A number standing in front of the word this repository uses for both the
#: checks the audit runs and the subset of them that bind a dependency group.
PROCESS_COUNT = re.compile(
    r"(?<![A-Za-z0-9-])([A-Za-z-]+) (?:required |audit )?process(?:es|"
    r" checks?|)(?![A-Za-z])")

#: What the smaller of the two groups is always described as binding. The space
#: is what keeps this off `dependency_output`, which is a check in the larger
#: group and stands two words into every list of it.
BINDS_A_GROUP = re.compile(r"dependency (?:report|group|record)")

#: Anything in code style. This has to be everything rather than a name shape:
#: a guard that reads a list of names out of a sentence compares what it found
#: against what it expected, so a reader that skips what it does not recognise
#: turns a foreign name in that list into a name it never saw. This module held
#: two definitions of it, a narrow one here and a wide one 1,847 lines below,
#: and the later one governed both --- so the guard beneath this ran on a reader
#: its own file contradicted, and the collision was what kept it strict.
BACKTICKED = re.compile(r"`([^`\n]+)`")
MILESTONE_DECLARES = r"^\s*(?:theorem|lemma|def|abbrev|instance)\s+"


def test_the_process_checks_the_note_lists_are_the_ones_the_audit_runs() -> None:
    """A process check added to the audit and to no list is invisible.

    `layered_derivation` was added, wired into the replay gate, given a row in
    the bound-reports table --- and left out of the sentence that says which
    checks a completed native execution requires, which went on saying eleven.
    Nothing compared the sentence to the audit, so the list drifted by exactly
    the check whose failure fails the gate. The guard reads the command table
    out of `audit.py` and the list out of the note, and requires both the names
    and their order to agree.

    It reads one sentence in one file, which is not the claim its name makes and
    is not where the drift it was written for started. The guards below take the
    same question to every document.
    """
    commands = _audit_commands(_audit_source())
    note = (REPO / "docs" / "verification.md").read_text(encoding="utf-8")
    start = note.index("process checks:")
    listed = BACKTICKED.findall(note[start:note.index(".", start)])
    assert listed == commands, (listed, commands)

    sentence = note[note.rindex(chr(10), 0, start):start]
    assert NUMBER_WORD[len(commands)] in sentence, sentence.strip()


def _audit_source() -> str:
    return (REPO / "src" / "hypermath_foundations" / "audit.py").read_text(
        encoding="utf-8")


def _audit_commands(source: str) -> list[str]:
    """The checks the audit runs, in the order it runs them."""
    block = source[source.index("commands = {"):]
    names = [match.group(1) for line in block[:block.index("}" + chr(10))].splitlines()
             for match in [COMMAND_KEY.match(line)] if match]
    assert len(names) == len(set(names)) and len(names) > 1, names
    return names


def _audit_seeded(source: str) -> list[str]:
    """The checks the report is created holding, in the order it holds them.

    A dictionary keeps insertion order, so this is the order anything that walks
    `report["checks"]` sees --- including the handler that decides which check a
    raised error belongs to.
    """
    tail = source[source.index('"checks": {name: _check('):]
    written = tail[tail.index("for name in") + len("for name in"):tail.index("},")]
    names: list[str] = []
    for literal, splat in re.findall(r'"([a-z_]+)"|\*([A-Za-z_]+)', written):
        if literal:
            names.append(literal)
            continue
        assert splat == "PROBE_TARGETS", (splat, "is a group this reader cannot expand")
        names += list(PROBE_TARGETS)
    assert names, written
    return names


def _audit_derived(source: str) -> list[str]:
    """The checks the audit writes into the report rather than running."""
    found = [name for name in DERIVED_CHECK.findall(source)
             if name not in _audit_commands(source)]
    assert found, "no check is written into the report outside the command loop"
    return found


def test_the_failure_handler_walks_the_order_the_run_uses() -> None:
    """Two orderings of the same fourteen names, in one file, never compared.

    The run walks `commands`. The report is seeded from a separate tuple, and
    when a process returns evidence the audit rejects --- a probe with an
    unreviewed axiom dependency --- the handler has to name the check that was
    running. It finds it as the last *attempted* check in `report["checks"]`,
    which is the seed's order, not the run's. The two agree today and nothing
    holds them to it, so a name moved in one list and not the other would mark
    a check that ran and passed as the failure, with its own exit code, output
    and reasons all still saying it succeeded.

    Nine tests raise from inside a probe and name the check they expect to fail,
    which pins parts of the agreement by accident. Measured over every adjacent
    transposition of the seed, they catch ten of the thirteen. The three they do
    not catch are the ones no test raises across, and the last two entries are
    among them: those can be exchanged with all of `tests/test_audit.py` still
    passing.
    """
    source = _audit_source()
    assert 'reversed(report["checks"])' in source, (
        "the handler no longer finds the failing check by walking the report,"
        " so what this compares the run order against is no longer what decides"
    )
    run, seeded = _audit_commands(source), _audit_seeded(source)
    assert run == seeded, (
        "the audit runs its checks in one order and reports them in another,"
        " so a raised error is charged to whichever check is last in the seed:"
        f"\n  runs   : {run}\n  reports: {seeded}"
    )


def test_every_check_the_report_carries_is_named_in_a_document() -> None:
    """The mirror of the group-size guard, at the level of the check itself.

    `test_every_audit_group_size_is_reported` holds every dependency group to
    being written down somewhere. Nothing held the checks: `assumption_policy`
    and `proof_admissibility` are in every report the audit produces, decide
    the gate between them, and are named nowhere in `docs/verification.md` ---
    which is the document that says what a completed execution requires.

    `CHANGELOG.md` is not read, for the reason the roster guard gives: an entry
    describes a release and keeps the names that release had. A check named only
    in an entry is a check nothing current describes, and an entry cannot stop
    being true, so reading it here would make this permanently satisfiable by
    history.
    """
    source = _audit_source()
    carried = _audit_commands(source) + _audit_derived(source)
    lines: list[str] = []
    for path in _prose_files():
        relative = path.relative_to(REPO).as_posix()
        if relative in HISTORICAL or relative == "CHANGELOG.md":
            continue
        lines += path.read_text(encoding="utf-8").split("\n")
    missing = [name for name in carried
               if not any("`" + name + "`" in line for line in lines)]
    assert not missing, ("checks the report carries that no document names: "
                         + ", ".join(missing))


def test_every_list_of_the_audit_checks_is_a_list_the_audit_has() -> None:
    """A count can be right about its list and wrong about its subject.

    `lean4/README.md` said the audit had "seven required processes" when it ran
    fourteen; that was repaired by rewriting the sentence, and the sentence went
    wrong again. It said "fourteen checks" over fourteen names, of which twelve
    were processes and two were checks the audit derives, while the two
    processes added since were absent. Fourteen names, the word "fourteen", and
    every name a real check --- so the count guards passed, because they hold a
    number against the list beside it and the list was the part that was wrong.

    The guard written for the first drift compares one sentence in
    `docs/verification.md` to the command table. This one asks the question of
    every document: a run of names in code style, all of which are checks, is
    the audit's list of checks and has to be one the audit has. A sentence
    naming only some of them says so, in the words it would use anyway.

    A run is three names or more. The two checks the audit derives cannot make
    one, so a sentence listing exactly those two is below this reader's floor and
    is held only by the guard that every check be named somewhere. Admitting that
    pair here would have been an arm nothing could reach, which is the defect the
    increment before this one closed.
    """
    source = _audit_source()
    processes, derived = _audit_commands(source), _audit_derived(source)
    every = set(processes) | set(derived)
    whole = (set(processes), every)
    enumerations = 0
    wrong: list[str] = []
    for path in _prose_files():
        relative = path.relative_to(REPO).as_posix()
        if relative in HISTORICAL:
            continue
        for block in _paragraphs(path):
            for found in CODE_RUN.finditer(block.text):
                names = re.findall(r"`([a-z_]+)`", found.group(0))
                if not set(names) <= every:
                    continue                      # not a list of checks
                if set(names) in whole:
                    enumerations += 1
                    continue
                if NAMING_SOME.search(block.text[max(0, found.start() - 120):found.start()]):
                    continue                      # says it is naming some
                absent = sorted(set(processes) - set(names))
                wrong.append(
                    f"{relative}:{block.line(found.start())}: names {len(names)}"
                    f" checks, leaving out {absent or 'none'} and adding"
                    f" {sorted(set(names) - set(processes)) or 'none'}")
    assert enumerations, (
        "no document lists the audit's checks, so this read nothing --- the"
        " reader, not the documents, is what to look at first")
    assert not wrong, ("lists of the audit's checks that the audit does not"
                       " have:\n" + "\n".join(wrong))


def test_a_number_in_front_of_the_word_process_is_one_of_the_measurements() -> None:
    """These notes call two different things processes, and both are measured.

    The audit runs fourteen checks as processes; twelve of those bind a group of
    exact dependency reports. `CLAUSE_INDEPENDENCE.md` said "Ten processes each
    bind a group of exact dependency reports" and that `docs/verification.md`
    "now carries the ten sizes as a table" --- ten was the count at the boundary
    the paragraph records, the table has twelve rows, and both sentences are
    written in the present tense. Nothing read them: the totals scan binds
    numbers to assumptions, admissions, milestones and declarations, and a
    process is none of those.

    Which of the two measurements a number answers to is decided by whether a
    dependency report is named beside it, so the guard does not have to assume
    the two words are used consistently. It cannot tell that a sentence means
    the other one; what it refuses is a number that is neither.

    It also cannot tell a claim from a record: "the audit ran twelve processes
    then" is a true sentence this rejects. A quotation is exempt, which is this
    repository's convention for citing a number some other text wrote, and a
    record with no quotation in it has to be phrased without putting a number in
    front of the word --- which the entry about this drift is, and says so here
    rather than leaving the next writer to discover it from a failure.
    """
    source = _audit_source()
    sizes = {"processes": len(_audit_commands(source)),
             "groups": len(PROBE_TARGETS)}
    read = 0
    wrong: list[str] = []
    for path in _prose_files():
        relative = path.relative_to(REPO).as_posix()
        if relative in HISTORICAL:
            continue
        for block in _paragraphs(path):
            mask = block.quoted()
            for found in PROCESS_COUNT.finditer(block.text):
                word = found.group(1).lower()
                if word not in NUMBER_NAMES or mask[found.start(1)]:
                    continue
                read += 1
                near = block.text[found.end():found.end() + 70]
                about = "groups" if BINDS_A_GROUP.search(near) else "processes"
                if _spelled(word) != sizes[about]:
                    wrong.append(
                        f"{relative}:{block.line(found.start())}:"
                        f" {found.group(0)!r} against {sizes[about]} {about}")
    assert read, "no sentence counts the audit's processes, so this read nothing"
    assert not wrong, ("counts of the audit's processes that are neither"
                       " measurement:\n" + "\n".join(wrong))


def test_the_milestone_declarations_partition_by_the_file_that_declares_them() -> None:
    """The total is measured; the eleven inside it never was.

    `FINITE_ARITHMETIC.md` has said "including eleven finite-orbit/action
    results" while the only pinned number was the total, so the eleven could
    have been any eleven. They are the declarations in `FiniteAction.lean`, and
    the whole partition falls out of the same measurement: every milestone name
    is declared in exactly one file, and the four parts sum to the total.
    """
    counts: dict[str, int] = {}
    for full in PROVED_DECLARATIONS:
        pattern = re.compile(MILESTONE_DECLARES + re.escape(full.split(".")[-1]) + r"\b", re.M)
        declaring = [path.name for path in sorted(LAYERS.glob("*.lean"))
                     if pattern.search(path.read_text(encoding="utf-8"))]
        assert len(declaring) == 1, f"{full} is declared in {declaring}"
        counts[declaring[0]] = counts.get(declaring[0], 0) + 1

    assert counts == {"L3Ordinatics.lean": 49, "L1Relations.lean": 13,
                      "FiniteAction.lean": 11, "L2Operations.lean": 3}, counts
    assert sum(counts.values()) == len(PROVED_DECLARATIONS)

    # The claim wraps across lines in the note, so compare against one line.
    note = " ".join(
        (REPO / "docs" / "research" / "FINITE_ARITHMETIC.md").read_text(encoding="utf-8").split())
    for name, count in counts.items():
        claim = f"{NUMBER_WORD.get(count, count)} in `{name}`"
        assert claim in note or f"{count} in `{name}`" in note, claim

    # The same eleven are quoted in the verification note's finite-action row.
    verification = " ".join((REPO / "docs" / "verification.md").read_text(encoding="utf-8").split())
    part = counts["FiniteAction.lean"]
    assert (f"{NUMBER_WORD[part].capitalize()} production milestone results "
            "(`FiniteAction.lean`)") in verification, part


CHOICE = "Classical.choice"
AUTOMATION_PAIR = ("Quot.sound", "propext")
CHOICE_CENSUS = {
    "COUNTERMODEL_DEPENDENCIES": 5,
    "FULL_MODEL_DEPENDENCIES": 22,
    "OBSERVATION_DEPENDENCIES": 2,
    "PROVED_DEPENDENCIES": 4,
    "RECORD_ENCODING_DEPENDENCIES": 1,
}
CHOICE_UNACCOMPANIED = {
    "Hypermath.Observation.chosenDecoder_correct",
    "Hypermath.Observation.compatible_iff_decoder",
    "Hypermath.finiteOrbitDecode_spec",
    "Hypermath.finiteOrbitEquivalence_laws",
}
OBSERVATION_COSTS = {(): 22, (CHOICE,): 2}


def _dependency_tables() -> dict[str, dict[str, object]]:
    from hypermath_foundations import _reports

    return {name: table for name in dir(_reports)
            for table in [getattr(_reports, name)]
            if name.endswith("_DEPENDENCIES") and isinstance(table, dict)}


def test_where_the_choice_principle_enters() -> None:
    """Which tables name choice, how often, and the four that name it alone.

    Every dependency table is pinned to exact costs now, so the footprint of the
    choice principle is a measurement rather than a reading. The census holds
    both halves: a table gaining or losing a choice report fails here, and so
    does a report joining or leaving the four that name choice without naming
    `Quot.sound` or `propext`. Those four are the only ones about which anything
    can be concluded --- whatever brings the other two axioms into the rest, it
    is not what brought choice into these.
    """
    tables = _dependency_tables()
    counts = {name: sum(1 for deps in table.values() if CHOICE in deps)
              for name, table in tables.items()}
    assert {k: v for k, v in counts.items() if v} == CHOICE_CENSUS, counts
    assert sum(counts.values()) == 34

    alone = {report for table in tables.values() for report, deps in table.items()
             if CHOICE in deps and not any(axiom in deps for axiom in AUTOMATION_PAIR)}
    assert alone == CHOICE_UNACCOMPANIED, sorted(alone)


def test_the_observation_row_reports_the_costs_it_claims() -> None:
    """An exact cost claim in prose, made before a table could check it.

    `docs/verification.md` has said "24 observation reports: 22 axiom-free, two
    with classical choice" since before the dependency tables were pinned. It is
    true, and until now nothing compared it to anything.
    """
    from hypermath_foundations._reports import OBSERVATION_DEPENDENCIES

    shapes: dict[tuple[str, ...], int] = {}
    for dependencies in OBSERVATION_DEPENDENCIES.values():
        shapes[tuple(dependencies)] = shapes.get(tuple(dependencies), 0) + 1
    assert shapes == OBSERVATION_COSTS, shapes

    note = " ".join((REPO / "docs" / "verification.md").read_text(encoding="utf-8").split())
    total = sum(OBSERVATION_COSTS.values())
    free = OBSERVATION_COSTS[()]
    assert (f"{total} observation reports: {free} axiom-free, "
            f"{NUMBER_WORD[OBSERVATION_COSTS[(CHOICE,)]]} with classical choice") in note


SWEEP = REPO / "lean4" / "LayerConsumptionChecks.lean"
SWEPT = re.compile(r"^#print axioms (\S+)$", re.M)
PUBLIC_DECLARES = re.compile(
    r"^(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance)"
    r"\s+([A-Za-z_][A-Za-z0-9_'.]*)")
OPENS = re.compile(r"^namespace (\S+)$")
CLOSES = re.compile(r"^end (\S+)$")
SIGNATURE = frozenset({"Hypermath.Form", "Hypermath.f2f", "Hypermath.ground"})
SIBLINGS = ("L1Relations", "L2Operations")
MEETING_PLACE = "L3Ordinatics"
# Declared names the sweep found nothing consuming. Measured, then pinned:
# spending one of them and adding a sixth are both real changes.
UNCONSUMED_COUNT = 5


def _public_declarations() -> dict[str, str]:
    """Every declaration the sweep can name, with the file that declares it.

    A `private` declaration carries a mangled name and cannot be reported from
    another file, so it is out of scope here and out of scope for the sweep.
    """
    found: dict[str, str] = {}
    for path in sorted(LAYERS.glob("*.lean")):
        stack: list[str] = []
        for line in path.read_text(encoding="utf-8").splitlines():
            opened = OPENS.match(line)
            if opened:
                stack.append(opened.group(1))
                continue
            closed = CLOSES.match(line)
            if closed and stack and stack[-1] == closed.group(1):
                stack.pop()
                continue
            declared = PUBLIC_DECLARES.match(line)
            if declared:
                found[".".join(stack + [declared.group(1)])] = path.stem
        assert not stack, f"{path.name}: unbalanced namespaces {stack}"
    return found


def test_the_sweep_covers_every_public_declaration() -> None:
    """A declaration that is not swept is a declaration nothing measures.

    The process-check list had already drifted once by exactly the check whose
    failure fails the gate, and for the same reason: the audit grew and the
    thing naming its parts did not. The sweep is a list of names, so it can
    drift the same way --- silently, and in the direction that loses coverage.
    This regenerates the list from the sources and requires the two to agree,
    which makes a new theorem's axiom report a consequence of writing it.
    """
    from hypermath_foundations._reports import LAYER_CONSUMPTION_TARGETS

    sources = _public_declarations()
    swept = SWEPT.findall(SWEEP.read_text(encoding="utf-8"))
    assert len(swept) == len(set(swept)), "a declaration is swept twice"
    assert set(swept) == set(sources), sorted(set(swept) ^ set(sources))
    assert set(LAYER_CONSUMPTION_TARGETS) == set(sources)


def test_the_layer_stack_consumes_downwards_and_never_upwards() -> None:
    """The layering is an architecture claim; this is the measurement of it.

    Four files declare the theory's own symbols and clauses, and the stack says
    they are ordered. What the reports say is which of them each file's content
    actually consumes. The claim checked here is the one the order is for: no
    file consumes a declaration from a layer that comes after it. It holds, and
    it had never been measured --- the import graph was the only evidence, and
    an import is permission to use, not use.
    """
    from hypermath_foundations._reports import (
        LAYER_CONSUMPTION_SUPPORT, LAYER_FILE_ORDER)

    for site, sources in LAYER_CONSUMPTION_SUPPORT.items():
        assert sources, f"{site} is listed with no sources"
        assert list(sources) == sorted(sources, key=LAYER_FILE_ORDER.index)
        if site in LAYER_FILE_ORDER:
            reach = LAYER_FILE_ORDER.index(site)
            above = [s for s in sources if LAYER_FILE_ORDER.index(s) > reach]
            assert not above, f"{site} consumes {above}"
        assert LAYER_FILE_ORDER[0] in sources, f"{site} avoids the ground layer"


def test_the_layer_stack_is_a_chain_and_the_measure_says_so() -> None:
    """The stack is drawn as a chain. The content is a chain too.

    The prose used to say the middle two layers were siblings, and the
    measurement said otherwise: `L2Operations` consumes `L1Relations`, and
    `L3Ordinatics` consumes both. The two claims disagreed and the prose was
    the one that was wrong, so this reads the table and says what it says.

    What the table says is a strict chain over the ground layer, and it says
    so in one row per layer: `L0Ground` consumes only itself, `L1Relations`
    consumes `L0Ground` and itself, `L2Operations` consumes the two beneath
    it, and `L3Ordinatics` consumes all three. The support table is
    per-layer, so it can see a dependency that crosses a layer boundary, which
    an import graph cannot --- an import is permission to use, not use.

    The claim this replaces was not wrong about the two layers individually.
    It was wrong about the shape, and the shape is what a reader of the
    stack needs. The sibling reading was carried by a scan that only asked
    whether `L1Relations` reached `L2Operations` and not whether the reverse
    held.
    """
    from hypermath_foundations._reports import (
        LAYER_CONSUMPTION_SUPPORT, LAYER_FILE_ORDER)

    order = LAYER_FILE_ORDER
    for index, layer in enumerate(order):
        sources = LAYER_CONSUMPTION_SUPPORT[layer]
        assert sources, f"{layer} is listed with no sources"
        # Every layer reaches the ground layer and nothing below it.
        assert order[0] in sources, f"{layer} avoids the ground layer"
        for other in sources:
            assert other in order, other
            assert order.index(other) <= index, (
                f"{layer} consumes {other}, which is above it")
        # And it reaches every layer at or below itself.
        for other in order[:index + 1]:
            assert other in sources, f"{layer} does not consume {other}"


def test_five_declared_clauses_are_consumed_by_nothing() -> None:
    """Independence is a lower bound; consumption is an upper one.

    The independence results say a clause cannot be dropped, by exhibiting a
    model that satisfies the others and denies it. They say nothing about
    whether anything uses it. The sweep says the other half, and for five of
    the sixty-one declared names the answer is nothing anywhere: no statement
    and no proof in `lean4/Hypermath/` mentions them. Three are clauses the
    theory asserts and has not spent; two are symbols it declares and never
    reasons about.

    That is a gap between the parts rather than a fault in either. This holds
    the list so that spending one of them, or adding a sixth, is deliberate.
    """
    from hypermath_foundations._reports import LAYER_AXIOM_HOME, LAYER_UNCONSUMED

    assert set(LAYER_UNCONSUMED) <= set(LAYER_AXIOM_HOME)
    assert len(LAYER_UNCONSUMED) == UNCONSUMED_COUNT, LAYER_UNCONSUMED
    statements = {}
    for path in sorted(LAYERS.glob("*.lean")):
        statements.update(
            {"Hypermath." + name: text
             for name, text in _axiom_statements(path).items()})
    missing = [n for n in LAYER_UNCONSUMED if n not in statements]
    assert not missing, missing

    # The sweep is the authority and it only runs under Lean. Every other
    # pinned table is a record of what some proof named, so a name appearing in
    # one of them is consumed, and listing it here would be a contradiction
    # between two things already in the repository.
    named = {axiom for table in _dependency_tables().values()
             for dependencies in table.values() for axiom in dependencies
             if axiom in LAYER_AXIOM_HOME}
    contradicted = sorted(set(LAYER_UNCONSUMED) & named)
    assert not contradicted, contradicted


def test_the_finite_action_results_rest_on_the_signature_alone() -> None:
    """The eleven were named by their file; this is what they are.

    The milestone partition put eleven of the sixty-eight proved declarations
    in `FiniteAction.lean` and said nothing about their content. Their reports
    do: every one of the eleven names `Form`, `f2f` and `ground` and no other
    declaration --- the bare signature, and not one clause of the theory. The
    development is written that way on purpose, parametrically over a pointed
    map, and the specializations inherit it.

    So the finite-orbit results hold of an arbitrary self-map on a pointed
    type. No hypermath clause can be refuted by them and none is needed for
    them, which is why no countermodel in the independence program touches
    them.
    """
    from hypermath_foundations._baseline import PROVED_DECLARATIONS, PROVED_DEPENDENCIES
    from hypermath_foundations._reports import LAYER_CONSUMPTION_SUPPORT

    declared = _public_declarations()
    eleven = [name for name in PROVED_DECLARATIONS
              if declared.get(name) == "FiniteAction"]
    assert len(eleven) == 11, sorted(eleven)
    for name in eleven:
        own = {a for a in PROVED_DEPENDENCIES[name] if a.startswith("Hypermath.")}
        assert own == SIGNATURE, (name, sorted(own))
    assert LAYER_CONSUMPTION_SUPPORT["FiniteAction"] == ("L0Ground",)


def test_the_milestone_costs_stay_inside_the_layers_they_may_consume() -> None:
    """Two tables measured apart, crossed for the first time.

    `PROVED_DEPENDENCIES` pins one list per milestone and knows nothing about
    layers. `LAYER_CONSUMPTION_SUPPORT` records layers and knows nothing about
    milestones. Each milestone is declared in one file, so the layers its list
    names have to be among the layers that file consumes. Nothing required
    that before, and a table regenerated against a stale sweep would show up
    here rather than in neither.
    """
    from hypermath_foundations._baseline import PROVED_DEPENDENCIES
    from hypermath_foundations._reports import (
        LAYER_AXIOM_HOME, LAYER_CONSUMPTION_SUPPORT)

    declared = _public_declarations()
    for name, dependencies in PROVED_DEPENDENCIES.items():
        sources = {LAYER_AXIOM_HOME[a] for a in dependencies
                   if a in LAYER_AXIOM_HOME}
        if not sources:
            continue
        allowed = set(LAYER_CONSUMPTION_SUPPORT[declared[name]])
        assert sources <= allowed, (name, sorted(sources - allowed))


# The relation `axComposeAssoc` asserts associativity up to. A transitivity
# clause applies a relation three times; a clause that applies it once or twice
# cannot chain, so counting occurrences is enough to say that nothing declares
# this relation transitive --- which is the premise the result below rests on.
COMPOSITION_RELATION = "congruentPath"
COMPOSITION_CLAUSES = ("axComposeAssoc", "axComposeIdentity",
                        "axComposeNonempty", "axCongruentPathSymm")
TRANSITIVITY_NEEDS = 3

# The clause the sweep found idle, and the block that says why.
IDLE_CLAUSE = "Hypermath.axComposeAssoc"
MISSING_STEP = "transitivity_is_exactly_the_missing_step"
COMPOSE_BLOCK = tuple(
    "HypermathCountermodel.FreeFiltration.ComposeNeedsTransitivity." + name
    for name in ("fourFold_of_transitive", "related_satisfies_the_clauses",
                 "related_denies_the_four_fold", "related_is_reflexive",
                 "four_fold_without_transitivity",
                 MISSING_STEP))
TRANSITIVITY_HYPOTHESIS = "(∀ x y z : Path, cp x y → cp y z → cp x z) → "


def test_nothing_declares_the_composition_relation_transitive() -> None:
    """The premise of the result, measured rather than asserted.

    `axComposeAssoc` cannot be chained because nothing says its relation is
    transitive, and the whole explanation of why the clause is idle depends on
    that staying true. Four clauses mention the relation and the most any of
    them applies it is twice --- the two halves of a conjunction about a single
    path, which share no endpoint and so compose into nothing. Two
    occurrences is the shape of a chaining clause, and there are none.

    The fourth is the closing clause `axCongruentPathSymm`, which mentions the
    relation twice --- once in each direction --- and chains nothing.
    """
    statements = _clause_statements(REPO / "lean4" / "FullAxiomModel.lean", "FullAxioms")
    pattern = re.compile(r"\b" + COMPOSITION_RELATION + r"\b")
    occurrences = {name: len(pattern.findall(statement))
                   for name, statement in statements.items()}

    mentioning = tuple(sorted(name for name, count in occurrences.items() if count))
    assert mentioning == tuple(sorted(COMPOSITION_CLAUSES)), mentioning

    chained = sorted(name for name, count in occurrences.items()
                     if count >= TRANSITIVITY_NEEDS)
    assert not chained, chained


def test_the_missing_step_is_the_only_difference_between_the_two_halves() -> None:
    """The result is that one hypothesis decides it, so the halves must agree.

    `transitivity_is_exactly_the_missing_step` would typecheck if its negative
    half denied something weaker than its positive half proves --- a different
    carrier, a different clause structure, a four-fold law over other
    arguments. Each of those reads as though transitivity had been isolated
    when something else had been. The two halves are compared here directly:
    delete the transitivity hypothesis from the derivable one and what is left
    must be the underivable one, character for character.
    """
    statement = _theorem_statement(MISSING_STEP)
    head, tail = statement.split(" ∧ ¬ (", 1)
    positive = head.split(" : (", 1)[1]
    assert positive.endswith(")"), positive
    assert tail.endswith(")"), tail

    assert positive[:-1].replace(TRANSITIVITY_HYPOTHESIS, "", 1) == tail[:-1], statement
    assert TRANSITIVITY_HYPOTHESIS in positive, positive
    assert TRANSITIVITY_HYPOTHESIS not in tail, tail


def test_the_explained_clause_is_one_the_sweep_found_idle() -> None:
    """The explanation and the thing it explains, held together.

    The block is about a clause nothing consumes. If `axComposeAssoc` is ever
    spent the block stops explaining anything, and if the block is deleted
    while the clause is still idle the reason is lost --- so each is required
    to exist while the other does. The five reports are free of every axiom,
    which is what lets the explanation be read as part of the development
    rather than as something bought with a principle.
    """
    from hypermath_foundations._reports import (
        COUNTERMODEL_DEPENDENCIES, LAYER_UNCONSUMED)

    assert IDLE_CLAUSE in LAYER_UNCONSUMED, LAYER_UNCONSUMED

    missing = [name for name in COMPOSE_BLOCK if name not in COUNTERMODEL_DEPENDENCIES]
    assert not missing, missing

    costly = {name: COUNTERMODEL_DEPENDENCIES[name] for name in COMPOSE_BLOCK
              if COUNTERMODEL_DEPENDENCIES[name]}
    assert not costly, costly


# The two clauses that speak form closure. One is consumed and one is not, and
# the idle one is the stronger --- so the reason it is idle cannot be that it
# says nothing. `FormClosure` is the antecedent of no arrow in any clause,
# which is where the strength it adds has nowhere to go.
FORM_CLOSURE = "FormClosure"
CLOSURE_CLAUSES = ("axFormClosesLoop", "closeFormClosureOpaque")
IDLE_CLOSURE = "Hypermath.closeFormClosureOpaque"
SPENT_CLOSURE = "Hypermath.axFormClosesLoop"
CLOSURE_BLOCK = tuple(
    "HypermathCountermodel.FreeFiltration.FormClosureIsOneDirection." + name
    for name in ("the_ground_closure_needs_only_the_loop",
                 "the_close_clause_is_exactly_its_converse",
                 "the_other_clauses_do_not_give_the_close"))


def test_the_idle_form_closure_clause_is_the_stronger_of_the_two() -> None:
    """The third idle clause, and the third reason a clause goes unspent.

    `axSeqIdentityL` duplicates a clause and `axComposeAssoc` cannot be
    chained. This one is strictly stronger than `axFormClosesLoop`, which is
    consumed --- so it is not idle for want of content. What it adds over the
    weaker clause is one implication *out of* `FormClosure`, and `FormClosure`
    is the antecedent of no arrow in any clause of the theory. A clause can
    carry real strength and still be unspent when the strength points in a
    direction nothing travels.
    """
    statements = _clause_statements(REPO / "lean4" / "FullAxiomModel.lean", "FullAxioms")
    mentioning = tuple(sorted(name for name, statement in statements.items()
                              if FORM_CLOSURE in statement))
    assert mentioning == tuple(sorted(CLOSURE_CLAUSES)), mentioning

    used = sorted(name for name in mentioning
                  if FORM_CLOSURE + " x →" in statements[name])
    assert not used, used


def test_the_consumed_form_closure_clause_is_the_weaker_one() -> None:
    """Which of the pair the sweep found idle, held against the pair itself.

    If the idle one were `axFormClosesLoop` the block above would be explaining
    the wrong clause, and nothing in Lean can notice that: both are declared,
    both are clauses about form closure, and the equivalence between them holds
    whichever is spent.
    """
    from hypermath_foundations._reports import (
        COUNTERMODEL_DEPENDENCIES, LAYER_UNCONSUMED)

    assert IDLE_CLOSURE in LAYER_UNCONSUMED, LAYER_UNCONSUMED
    assert SPENT_CLOSURE not in LAYER_UNCONSUMED, LAYER_UNCONSUMED

    missing = [name for name in CLOSURE_BLOCK if name not in COUNTERMODEL_DEPENDENCIES]
    assert not missing, missing

    costly = {name: COUNTERMODEL_DEPENDENCIES[name] for name in CLOSURE_BLOCK
              if COUNTERMODEL_DEPENDENCIES[name]}
    assert not costly, costly


# The names a single declaration holds in play. Seven of the sixty-one, and
# five of the seven are held by two theorems --- so the boundary between the
# idle set and the rest is one theorem thick for most of the names near it.
SPENT_ONCE_COUNT = 9
HELD_BY_A_PLURAL_HOLDER = 5
HOLDERS = {
    "Hypermath.groundIsFormClosed": 3,
    "Hypermath.dischargeIsAbstractionTier": 2,
}
FORM_CLOSURE_VOCABULARY = (
    "Hypermath.FormClosure", "Hypermath.axFormClosesLoop",
    "Hypermath.axGroundSyntaxAx", "Hypermath.closeFormClosureOpaque")


def test_no_declared_name_is_both_idle_and_spent_once() -> None:
    """The two tables are the zero row and the one row of the same count.

    Both come out of one reduction of one sweep, so a name in both would mean
    the reduction disagreed with itself. Worth holding because the tables are
    reviewed by hand and read as independent facts.
    """
    from hypermath_foundations._reports import (
        LAYER_AXIOM_HOME, LAYER_DECLARATION_HOME, LAYER_SPENT_ONCE,
        LAYER_UNCONSUMED)

    assert len(LAYER_SPENT_ONCE) == SPENT_ONCE_COUNT, LAYER_SPENT_ONCE
    assert set(LAYER_SPENT_ONCE) <= set(LAYER_AXIOM_HOME), LAYER_SPENT_ONCE
    both = sorted(set(LAYER_SPENT_ONCE) & set(LAYER_UNCONSUMED))
    assert not both, both

    # Every sole consumer is a declaration the sweep actually swept, and no
    # name is its own consumer.
    outside = sorted(set(LAYER_SPENT_ONCE.values()) - set(LAYER_DECLARATION_HOME))
    assert not outside, outside
    selves = sorted(a for a, c in LAYER_SPENT_ONCE.items() if a == c)
    assert not selves, selves


def test_two_theorems_hold_five_names_out_of_the_idle_set() -> None:
    """What the sweep measures is the development, not the theory.

    `LAYER_UNCONSUMED` reads like a property of the clauses. It is not. Five
    of the seven singly-spent names are held by two theorems ---
    `groundIsFormClosed` holds three and `dischargeIsAbstractionTier` holds two
    --- so deleting those two proofs would take the idle set from five to ten
    without changing a single clause of the theory.

    That is the sense in which idle and spent are not properties of a name.
    They are properties of a name relative to a set of proofs, and for most of
    the names near the boundary the set is one proof deep.
    """
    from hypermath_foundations._reports import LAYER_SPENT_ONCE

    held = Counter(LAYER_SPENT_ONCE.values())
    plural = {name: count for name, count in held.items() if count > 1}
    assert plural == HOLDERS, plural
    assert sum(plural.values()) == HELD_BY_A_PLURAL_HOLDER, held


def test_the_form_closure_vocabulary_rests_on_one_theorem() -> None:
    """The join of the idleness result with the incidence measurement.

    Four declared names speak form closure: the symbol, the two clauses about
    it, and the ground hypothesis the one consumed clause needs. One of the
    four is already idle, and `the_close_clause_is_exactly_its_converse` says
    why. This says what holds the other three: a single theorem, the same one
    `the_ground_closure_needs_only_the_loop` proves with the carrier left open.

    So the form-closure fragment is not half-used. It is one three-line proof
    away from being wholly unused, and the analysis of the idle clause applies
    verbatim to the rest of the fragment the moment that proof goes.
    """
    from hypermath_foundations._reports import LAYER_SPENT_ONCE, LAYER_UNCONSUMED

    idle = [n for n in FORM_CLOSURE_VOCABULARY if n in LAYER_UNCONSUMED]
    assert idle == ["Hypermath.closeFormClosureOpaque"], idle

    holders = {n: LAYER_SPENT_ONCE.get(n) for n in FORM_CLOSURE_VOCABULARY
               if n not in LAYER_UNCONSUMED}
    assert set(holders.values()) == {"Hypermath.groundIsFormClosed"}, holders
    assert len(holders) == HOLDERS["Hypermath.groundIsFormClosed"], holders


# The idle set counts mentions. One declared name is mentioned only by a
# statement whose proof does not exist, which is a different thing from being
# spent, and a different thing again from being unmentioned.
ADMISSION_HELD = "Hypermath.axSeqAsymm"
IDLE_BY_PROOF = 5
DECLARATION_START = re.compile(
    r"^(?:theorem|lemma|def|abbrev|instance|example)\s+(\S+)", re.M)


def _declaration_body(path: Path, name: str) -> str:
    """The source of one top-level declaration, up to the next one."""
    text = path.read_text(encoding="utf-8")
    starts = [(m.start(), m.group(1)) for m in DECLARATION_START.finditer(text)]
    for index, (offset, found) in enumerate(starts):
        if found == name:
            end = starts[index + 1][0] if index + 1 < len(starts) else len(text)
            return text[offset:end]
    raise AssertionError(f"{name} not found in {path.name}")


def test_one_declared_name_is_held_only_by_an_admission() -> None:
    """Applied, inside a proof that is not finished.

    `axSeqAsymm` has exactly one consumer and that consumer is admitted. The
    clause is genuinely applied there --- `exact axSeqAsymm _ _ (by ... sorry)`
    --- so the sweep is right to count it; what is admitted is the hypothesis
    the application needs. No finished proof in the development spends it.

    That is a fifth thing "unspent" can mean, and the only one the sweep cannot
    see unaided, because `#print axioms` reports an application whether or not
    the proof around it is closed. The idle set is five counted by mention and
    six counted by proof, and the difference is this name.
    """
    from hypermath_foundations._reports import (
        LAYER_AXIOM_HOME, LAYER_HELD_ONLY_BY_ADMISSION, LAYER_SPENT_ONCE,
        LAYER_UNCONSUMED)

    assert set(LAYER_HELD_ONLY_BY_ADMISSION) <= set(LAYER_AXIOM_HOME)
    overlap = sorted(set(LAYER_HELD_ONLY_BY_ADMISSION) & set(LAYER_UNCONSUMED))
    assert not overlap, overlap
    assert (len(LAYER_UNCONSUMED) + len(LAYER_HELD_ONLY_BY_ADMISSION)
            == IDLE_BY_PROOF), LAYER_HELD_ONLY_BY_ADMISSION

    # The claim is about the source, so it is checked against the source.
    for axiom in LAYER_HELD_ONLY_BY_ADMISSION:
        consumer = LAYER_SPENT_ONCE.get(axiom)
        assert consumer is not None, axiom
        home = LAYERS / (_reports_layer_home(consumer) + ".lean")
        body = _declaration_body(home, consumer.removeprefix("Hypermath."))
        assert re.search(r"\bsorry\b", body), consumer
        # The clause is applied, not merely named by the statement: it
        # stands in the proof, after the turnstile.
        proof = body.split(":= by", 1)
        assert len(proof) == 2, consumer
        assert axiom.removeprefix("Hypermath.") in proof[1], (axiom, consumer)

    # And a name held by a real proof must not be listed here.
    for axiom, consumer in LAYER_SPENT_ONCE.items():
        if axiom in LAYER_HELD_ONLY_BY_ADMISSION:
            continue
        home = LAYERS / (_reports_layer_home(consumer) + ".lean")
        body = _declaration_body(home, consumer.removeprefix("Hypermath."))
        assert not re.search(r"\bsorry\b", body), (axiom, consumer)


def test_no_clause_is_held_only_by_an_admission() -> None:
    """Nothing in the theory rests on an unproved step.

    The row this guard reads was populated when `axSeqAsymm` had one consumer
    and that consumer was admitted: the clause was applied at a point no proof
    reached, so it was held by nothing but an admission. The closing clause
    `axDiffCongruent` supplies the incongruence that consumer had been
    admitted for, `plusAndAdditionallyAreDistinct` is proved from it, and the
    row emptied.

    The two halves of the older guard are kept, because each is a fact about
    the sources and neither is implied by the row being empty.
    `no_incongruence_is_derivable` gives a carrier satisfying every clause in
    which `Congruent` is total, and `sequencing_asymmetry_never_applies`
    reads off that the clause's antecedent holds of no pair there --- so the
    clause is discharged by vacuity in that model, and the model is refuted
    by `transport_violates_axDiffCongruent`, which is what makes the
    independence result and the closing clause consistent.

    What is *not* claimed is that the clause set is now free of
    independence. The closing clauses are assertions, not derivations, and
    `axDiffCongruent` in particular is the kind of clause a countermodel
    refutes.
    """
    from hypermath_foundations._reports import LAYER_HELD_ONLY_BY_ADMISSION

    source = (LAYERS / "TransportCountermodel.lean").read_text(encoding="utf-8")
    declared = tuple(line.split(" ")[1].rstrip(":")
                     for line in source.splitlines()
                     if line.startswith("theorem "))
    for name in ("no_incongruence_is_derivable", "sequencing_asymmetry_never_applies",
                 "transport_violates_axDiffCongruent"):
        assert name in declared, name

    assert LAYER_HELD_ONLY_BY_ADMISSION == (), LAYER_HELD_ONLY_BY_ADMISSION


def _reports_layer_home(name: str) -> str:
    from hypermath_foundations._reports import LAYER_DECLARATION_HOME
    return LAYER_DECLARATION_HOME[name]


# How the vocabulary is distributed over files. Fourteen of the twenty-four
# consume nothing and are pinned by their absence from the support table; of
# the ten that remain, five contain nothing else and five are the seam.
SWEPT_FILES = 25
BRIDGE_FILES = ("FiniteAction", "GroundDerivation", "GroundSyntax",
                "PathLayers", "PathTransport")


def test_the_theory_is_confined_to_five_files() -> None:
    """No layer file contains anything that is not about the theory.

    Every declaration in `L0Ground`, `L1Relations`, `L2Operations`,
    `L3Ordinatics` and `QuadrilateralFiltration` consumes a declared name ---
    no arithmetic helper, no generic lemma, nothing that would still typecheck
    with the clause list deleted. Five further files reach the vocabulary at a
    thin seam and are otherwise silent, and the remaining fourteen never touch
    it at all.

    The silence of the fourteen is already held, because a file that consumes
    nothing cannot appear in `LAYER_CONSUMPTION_SUPPORT` and the audit compares
    that dict by equality. What that cannot see is the difference between the
    other two groups: a support row says a file consumes `L0Ground`, not
    whether everything in it does. A generic helper drifting into a layer file
    would leave every previously pinned fact intact.
    """
    from hypermath_foundations._reports import (
        LAYER_CONSUMPTION_SUPPORT, LAYER_DECLARATION_HOME, LAYER_FILE_ORDER,
        LAYER_WHOLLY_CONSUMING)

    assert len(set(LAYER_DECLARATION_HOME.values())) == SWEPT_FILES

    # A layer file is the theory, so it may not hold anything else.
    generic = sorted(set(LAYER_FILE_ORDER) - set(LAYER_WHOLLY_CONSUMING))
    assert not generic, generic

    # Wholly consuming implies consuming, and the rest of the support table is
    # the bridge. Those two groups exhaust it.
    assert set(LAYER_WHOLLY_CONSUMING) <= set(LAYER_CONSUMPTION_SUPPORT)
    bridge = tuple(sorted(set(LAYER_CONSUMPTION_SUPPORT) - set(LAYER_WHOLLY_CONSUMING)))
    assert bridge == BRIDGE_FILES, bridge

    # The one wholly-consuming file that is not a layer. It is the surprise in
    # the list, and dropping it would leave a true but much weaker statement.
    extra = sorted(set(LAYER_WHOLLY_CONSUMING) - set(LAYER_FILE_ORDER))
    assert extra == ["QuadrilateralFiltration"], extra


# The seam, measured against the clause list rather than against the layers.
# `LAYER_BRIDGE_VOCABULARY` says which declared names each of the five bridge
# files reaches; splitting those into clauses and symbols is what turns a list
# of names into an interface.
CLAUSES_REACHED_FROM_OUTSIDE = 8
CLAUSES_NEVER_REACHED_FROM_OUTSIDE = 31
SEAM_SIGNATURE = ("Hypermath.Form", "Hypermath.f2f")
REACH_NO_CLAUSE = ("FiniteAction", "PathTransport")


def _clause_names() -> frozenset[str]:
    """The declared names that are clauses, as opposed to symbols.

    The thirty-nine fields of the model's clause structure, intersected with
    the names the sweep knows. A prefix test on `ax` and `close` gets this
    wrong: `structContinues`, `structDistinct` and `structOrbits` are symbols
    the clauses constrain, not clauses.
    """
    from hypermath_foundations._reports import LAYER_AXIOM_HOME

    fields = _clause_statements(REPO / "lean4" / "FullAxiomModel.lean", "FullAxioms")
    return frozenset("Hypermath." + field for field in fields) & frozenset(LAYER_AXIOM_HOME)


def test_no_operations_clause_is_reached_from_outside_the_theory() -> None:
    """The clause list is confined further than the theory is.

    `LAYER_WHOLLY_CONSUMING` says the theory lives in five files. That is a
    statement about declarations, and most declarations outside those files
    that reach the vocabulary reach only the signature. Splitting the seam by
    clause and symbol sharpens it: eight of the thirty-four clauses are
    consumed from outside and twenty-six never are, and every clause
    `L2Operations` declares is in the second group.

    This is the fact that makes the L1/L2 incomparability usable. Nothing
    outside the theory rests on an operations clause, so the whole of
    `L2Operations` can be restated without touching a proof anywhere else in
    the development --- which is a much stronger licence than the sweep's
    layer-level support table can give, since that table only says which layer
    a file reaches.
    """
    from hypermath_foundations._reports import LAYER_AXIOM_HOME, LAYER_BRIDGE_VOCABULARY

    clauses = _clause_names()
    reached = {name for vocabulary in LAYER_BRIDGE_VOCABULARY.values()
               for name in vocabulary if name in clauses}
    assert len(reached) == CLAUSES_REACHED_FROM_OUTSIDE, (len(reached), sorted(reached))
    assert len(clauses - reached) == CLAUSES_NEVER_REACHED_FROM_OUTSIDE, len(clauses)

    homes = sorted({LAYER_AXIOM_HOME[name] for name in reached})
    assert homes == ["L0Ground", "L1Relations"], homes

    operations = sorted(name for name in clauses
                        if LAYER_AXIOM_HOME[name] == "L2Operations")
    assert operations, "no operations clauses found, so the guard proves nothing"
    assert not [name for name in operations if name in reached], operations


def test_the_seam_goes_through_the_signature_in_every_file() -> None:
    """What the thirty-three symbol-only declarations have in common.

    Every one of the five bridge files reaches `Form` and `f2f`, and two of
    them reach nothing else that is a clause. That is the shape of a signature
    interface rather than a theory interface: the machinery is written against
    the carrier and its map, and the clauses stay behind the seam except where
    a file is building a model of the ground theory and has to discharge them.
    """
    from hypermath_foundations._reports import LAYER_BRIDGE_VOCABULARY

    clauses = _clause_names()
    for site, vocabulary in LAYER_BRIDGE_VOCABULARY.items():
        missing = [name for name in SEAM_SIGNATURE if name not in vocabulary]
        assert not missing, (site, missing)

    silent = tuple(sorted(site for site, vocabulary in LAYER_BRIDGE_VOCABULARY.items()
                          if not any(name in clauses for name in vocabulary)))
    assert silent == REACH_NO_CLAUSE, silent


# `LAYER_AXIOM_HOME` maps each declared name to the file that declares it. Every
# *name* in it is anchored to the source three ways over --- as a source
# parameter, as a field of the model's clause structure, or, for `ordinatics`
# alone, by its own guard. Every *home* was anchored by nothing at all.
def test_every_declared_name_is_homed_where_the_source_declares_it() -> None:
    """The index is read through for every number in the sweep, so anchor it.

    A home is used only when the name it belongs to turns up in a report, and
    an idle name turns up in no report: the support table, the seam and the
    wholly-consuming set all compute over names that something consumes. So the
    home of a consumed name is checked constantly and by accident --- move one
    and the support rows stop matching the sweep --- while the home of an idle
    name is checked nowhere. `LAYER_UNCONSUMED` has five entries, and before
    this guard each of their five homes could be changed to any other layer
    file with the whole suite and the audit still green.

    That is the wrong way round. The idle names are the ones this repository
    reasons about hardest --- three of the five have a countermodel written to
    explain why nothing spends them, and those explanations are all about which
    layer the clause sits in.

    Reading the map back out of the source costs one glob and closes it for all
    sixty-one at once, consumed and idle alike.
    """
    from hypermath_foundations._reports import LAYER_AXIOM_HOME

    source: dict[str, str] = {}
    for path in sorted(LAYERS.glob("*.lean")):
        for line in path.read_text(encoding="utf-8").splitlines():
            found = AXIOM.match(line)
            if found:
                source["Hypermath." + found.group(1)] = path.stem
    assert source == dict(LAYER_AXIOM_HOME), {
        name: (home, source.get(name))
        for name, home in LAYER_AXIOM_HOME.items() if source.get(name) != home
    } or sorted(set(source) ^ set(LAYER_AXIOM_HOME))


# What the five theory files import. `LAYER_BRIDGE_VOCABULARY` pins what the
# development takes from the theory; this is the other direction, and it is not
# symmetric.
THEORY_IMPORTS = {
    "L0Ground": (),
    "L1Relations": ("Hypermath.L0Ground", "Hypermath.Trace"),
    "L2Operations": ("Hypermath.L1Relations",),
    "L3Ordinatics": ("Hypermath.L2Operations", "Ordinatics"),
    "QuadrilateralFiltration": ("Hypermath.L2Operations",),
}
OUTSIDE_IMPORTS = {"L1Relations": "Hypermath.Trace", "L3Ordinatics": "Ordinatics"}
IMPORT = re.compile(r"^import\s+(\S+)", re.M)


def test_the_theory_takes_two_things_from_outside_its_own_files() -> None:
    """The theory is confined by name and not by import, at exactly two places.

    `LAYER_WHOLLY_CONSUMING` says every declaration in these five files is about
    the theory. It does not say the five are self-contained, and they are not:
    `L1Relations` imports `Hypermath.Trace`, which is one of the fourteen files
    that consume nothing, and `L3Ordinatics` imports `Ordinatics`, which is a
    different repository. Three of the five import nothing but theory files.

    Pinning the map matters because the first of those two is easy to add by
    accident --- the machinery is right there and it typechecks --- and because
    the second is a real dependency edge between repositories, not a citation.
    """
    found = {}
    for site in THEORY_IMPORTS:
        text = (LAYERS / (site + ".lean")).read_text(encoding="utf-8")
        found[site] = tuple(IMPORT.findall(text))
    assert found == THEORY_IMPORTS, found

    outside = {site: tuple(name for name in imports
                           if name.removeprefix("Hypermath.") not in THEORY_IMPORTS)
               for site, imports in found.items()}
    assert {s: v[0] for s, v in outside.items() if v} == OUTSIDE_IMPORTS, outside


def test_no_clause_is_stated_in_a_word_from_outside_the_theory() -> None:
    """The language is closed even though the proofs are not.

    `L1Relations` uses `Trace` eleven times, so the theory's *proofs* leave its
    five files. Its *statements* do not: no field of the model's clause
    structure mentions `Trace`, and neither does the type of any of the
    sixty-one declared names. The clause list can therefore be read, and a
    countermodel for it built, without `Hypermath.Trace` existing --- which is
    what makes every countermodel in this document able to declare its own
    carrier and its own `FullAxioms` and stay a countermodel for the real
    theory.

    Stated about `Trace` by name rather than about outside names in general,
    because two of those would be wrong for uninteresting reasons: the clause
    statements are read out of `TransportCountermodel.lean`, whose own
    re-declarations of the vocabulary are not outside anything, and
    `ContextualComposition` declares a `compose` on `Evidence` that collides
    with the theory's declared `compose` on paths.
    """
    from hypermath_foundations._reports import LAYER_AXIOM_HOME

    traced = re.compile(r"\bTrace\b")
    fields = _clause_statements(REPO / "lean4" / "FullAxiomModel.lean", "FullAxioms")
    assert fields, "no clause statements read"
    assert not [name for name, statement in fields.items() if traced.search(statement)]

    declaration = re.compile(
        r"^axiom\s+([A-Za-z_][A-Za-z0-9_']*)\s*:?(.*?)(?=^\S|\Z)", re.M | re.S)
    types: dict[str, str] = {}
    for path in sorted(LAYERS.glob("*.lean")):
        for found in declaration.finditer(path.read_text(encoding="utf-8")):
            types["Hypermath." + found.group(1)] = found.group(2)
    assert set(types) == set(LAYER_AXIOM_HOME), sorted(set(types) ^ set(LAYER_AXIOM_HOME))
    assert not [name for name, text in types.items() if traced.search(text)]


# Two rows of the evidence table in `docs/verification.md` cite counts that are
# derivable from `PROVED_DEPENDENCIES` and were joined to it by nothing. Both
# are correct. Neither could have stopped being correct visibly.
TRACE_PRODUCTION_SIGNATURE = frozenset(
    {"Hypermath.Congruent", "Hypermath.Form", "Hypermath.f2f"})
TRACE_PRODUCTION = (
    "Hypermath.dEntryEndpointIteration",
    "Hypermath.dEntryNoSteps",
    "Hypermath.dEntryStepLength",
    "Hypermath.dIsReflexive",
    "Hypermath.dIsTransitive",
    "Hypermath.reflexionTraceComposeIdentity",
    "Hypermath.selfReadLength",
)
ARITHMETIC_SOURCE_RELATIVE = (
    "Hypermath.finiteActionCompatible_iff_exists_exact",
    "Hypermath.finiteOrbitDecode_spec",
    "Hypermath.finiteOrbitEquivalence_laws",
    "Hypermath.hostFiniteAction_exact",
)
ARITHMETIC_PARAMETER_ONLY_COUNT = 13
BARE_SIGNATURE = (frozenset({"Hypermath.Form", "Hypermath.f2f", "Hypermath.ground"}),
                  frozenset({"Hypermath.Form", "Hypermath.f2f"}))
NUMBER_WORDS = {4: "four", 7: "Seven", 13: "Thirteen"}
VERIFICATION = REPO / "docs" / "verification.md"


def test_the_finite_trace_row_counts_what_the_table_says() -> None:
    """The seven are a group in the dependency table, not a tally in prose.

    `docs/verification.md` says the finite-trace surface rests on seven
    parameter-relative production proofs. It does, and the seven are exactly
    the declarations whose report is `Congruent`, `Form` and `f2f` and nothing
    else --- one equivalence class of the table, not a hand count. Rewriting
    one of them to reach a fourth name would leave the row saying seven.
    """
    from hypermath_foundations._baseline import PROVED_DEPENDENCIES

    found = tuple(sorted(name for name, deps in PROVED_DEPENDENCIES.items()
                         if frozenset(deps) == TRACE_PRODUCTION_SIGNATURE))
    assert found == TRACE_PRODUCTION, found
    row = [line for line in VERIFICATION.read_text(encoding="utf-8").splitlines()
           if line.startswith("| Finite traces ")]
    assert len(row) == 1, row
    assert NUMBER_WORDS[len(found)] + " parameter-relative" in row[0], row[0]


def test_the_finite_arithmetic_row_splits_where_the_reports_split() -> None:
    """Thirteen and four, and what actually separates them.

    The row reads as though "parameter-only" and "source-relative" were two
    kinds of result. In the table they are one kind of result under two
    conditions: every one of the seventeen rests on the signature parameters,
    and the four are the ones whose report also names an axiom of Lean's
    foundation --- `Classical.choice` for two of them and `Classical.choice`
    with `Quot.sound` and `propext` for the other two.

    Worth holding because the split is the interesting half of the row and is
    the half a rewrite moves. A proof that stops needing choice moves from four
    to thirteen and changes both numbers at once.
    """
    from hypermath_foundations._baseline import PROVED_DEPENDENCIES

    foundation = frozenset({"Classical.choice", "Quot.sound", "propext", "sorryAx"})
    relative = tuple(sorted(name for name, deps in PROVED_DEPENDENCIES.items()
                            if frozenset(deps) & foundation))
    assert relative == ARITHMETIC_SOURCE_RELATIVE, relative
    for name in relative:
        assert frozenset(PROVED_DEPENDENCIES[name]) - foundation in BARE_SIGNATURE, name

    only = [name for name, deps in PROVED_DEPENDENCIES.items()
            if frozenset(deps) in BARE_SIGNATURE]
    assert len(only) == ARITHMETIC_PARAMETER_ONLY_COUNT, sorted(only)

    row = [line for line in VERIFICATION.read_text(encoding="utf-8").splitlines()
           if line.startswith("| Finite arithmetic observations ")]
    assert len(row) == 1, row
    assert NUMBER_WORDS[len(only)] + " parameter-only" in row[0], row[0]
    assert NUMBER_WORDS[len(relative)] + " source-relative" in row[0], row[0]


# The remaining rows of the evidence table that cite a number. Each is the size
# of a pinned dependency table, or a split of one by whether the report names an
# axiom of Lean's foundation. Two rows needed their own guards above because the
# split in them is worth explaining; these three only needed joining.
EVIDENCE_ROWS = {
    "Observation boundary and full model": (
        "OBSERVATION_DEPENDENCIES", ("24 observation reports", "22 axiom-free")),
    "Finite ground syntax": (
        "GROUND_SYNTAX_DEPENDENCIES", ("23 exact dependency reports",)),
    "Composed ground calculus": (
        "GROUND_DERIVATION_DEPENDENCIES", ("26 exact dependency reports",)),
}
EVIDENCE_SIZES = {"OBSERVATION_DEPENDENCIES": (24, 22),
                  "GROUND_SYNTAX_DEPENDENCIES": (23, 13),
                  "GROUND_DERIVATION_DEPENDENCIES": (26, 11)}
FOUNDATION = frozenset({"Classical.choice", "Quot.sound", "propext", "sorryAx"})


def test_every_count_in_the_evidence_table_is_computed() -> None:
    """`docs/verification.md` is the summary; make it an artifact, not a memo.

    Each of these rows cites the size of a dependency table the audit already
    compares against a live Lean run, so the table cannot drift. The row could,
    and in both directions: a report added to a group leaves the prose saying
    the old number, and a number edited in the prose is answerable to nothing.

    The observation row also cites its split, which is the same shape as the
    arithmetic row above --- twenty-four reports, twenty-two of them naming no
    axiom of Lean's foundation and two naming choice. The other two rows cite
    only a size, and their splits are pinned here so that a report gaining an
    axiom is visible even where the prose does not mention one.
    """
    import hypermath_foundations._reports as reports

    text = VERIFICATION.read_text(encoding="utf-8").splitlines()
    for label, (table_name, phrases) in EVIDENCE_ROWS.items():
        table = getattr(reports, table_name)
        size, free = EVIDENCE_SIZES[table_name]
        assert len(table) == size, (table_name, len(table))
        assert sum(1 for deps in table.values()
                   if not (frozenset(deps) & FOUNDATION)) == free, table_name

        row = [line for line in text if line.startswith("| " + label + " ")]
        assert len(row) == 1, (label, row)
        for phrase in phrases:
            assert phrase in row[0], (label, phrase, row[0])


def test_no_declared_name_is_used_only_across_the_seam():
    """The bridge asks for nothing the theory does not already use.

    The seam table says what each of the five bridge files reaches. It does not
    say whether any of it is reached only there. A name the theory declares,
    never uses in its own five files, and that only a bridge file consumes
    would be unspent in a way none of the reasons already recorded covers: not
    idle, since something consumes it, but idle the moment the bridge is
    deleted --- which would make it a name the theory carries for an
    application rather than for itself.

    There are none, so the four classes partition the declared names: idle,
    consumed only inside the theory, consumed on both sides, and empty. The
    empty cell is the whole content of the claim that the bridge is an
    application of the theory and not a part of it.

    An empty pinned tuple proves nothing on its own, so the second half of this
    builds a sweep in which one name *is* seam-only and requires the reduction
    to say so. Without that, deleting the computation would pass.
    """
    from hypermath_foundations._reports import (
        LAYER_AXIOM_HOME, LAYER_BRIDGE_VOCABULARY, LAYER_DECLARATION_HOME,
        LAYER_SEAM_ONLY, LAYER_UNCONSUMED, LAYER_WHOLLY_CONSUMING,
        layer_consumption_shape)

    assert LAYER_SEAM_ONLY == (), LAYER_SEAM_ONLY

    reached = {axiom for names in LAYER_BRIDGE_VOCABULARY.values() for axiom in names}
    idle = set(LAYER_UNCONSUMED)
    assert not reached & idle, sorted(reached & idle)
    assert reached <= set(LAYER_AXIOM_HOME), sorted(reached - set(LAYER_AXIOM_HOME))
    assert (len(idle), len(reached), len(LAYER_AXIOM_HOME)) == (5, 18, 66), (
        len(idle), len(reached), len(LAYER_AXIOM_HOME))

    bridges = [site for site in LAYER_BRIDGE_VOCABULARY]
    assert not set(bridges) & set(LAYER_WHOLLY_CONSUMING), bridges
    carrier = next(name for name, home in LAYER_DECLARATION_HOME.items()
                   if home == bridges[0])
    lonely = sorted(reached)[0]
    other = sorted(set(LAYER_AXIOM_HOME) - {lonely})[0]
    made = {name: [] for name in LAYER_DECLARATION_HOME}
    made[carrier] = [lonely]
    # A file counts as wholly consuming only if every declaration in it
    # consumes, so the theory side of this sweep has to be a whole file.
    for name, home in LAYER_DECLARATION_HOME.items():
        if home == LAYER_WHOLLY_CONSUMING[0]:
            made[name] = [other]
    assert layer_consumption_shape(made)[6] == (lonely,), (
        lonely, layer_consumption_shape(made)[6])


def test_no_probe_group_can_end_the_audit_without_a_report():
    """An unreviewed axiom has to fail a check, not stop the run.

    The audit's contract is a report: every check gets a status and a reason,
    including the checks that fail because the evidence is not what the review
    says it is. That holds because each group decides validity by comparing the
    records against a reviewed table, and a comparison cannot raise.

    `layer_consumption` is the exception --- it reads its records through
    `LAYER_AXIOM_HOME` --- and a `KeyError` from that lookup is not one of the
    failures the audit catches, so a sweep naming an axiom nobody had reviewed
    ended the run with no report at all. The most ordinary way to produce one
    is to add a clause to the theory and not add it to the home table.

    So this asks the question of every group rather than of the one that had
    the hole: feed each a record set naming an axiom that appears in no
    reviewed table, and require the answer to be a rejection --- either False,
    or a failure of a kind the audit is written to catch. The caught kinds are
    read out of the audit's own source, so narrowing that tuple fails here.
    """
    import ast

    from hypermath_foundations import _reports
    from hypermath_foundations._reports import PROBE_TARGETS, probe_dependencies_valid

    source = (REPO / "src" / "hypermath_foundations" / "audit.py").read_text(encoding="utf-8")
    handlers = [node for node in ast.walk(ast.parse(source))
                if isinstance(node, ast.ExceptHandler) and node.type is not None]
    caught: set[str] = set()
    for handler in handlers:
        kinds = (handler.type.elts if isinstance(handler.type, ast.Tuple)
                 else [handler.type])
        caught.update(kind.id for kind in kinds if isinstance(kind, ast.Name))
    assert "ValueError" in caught, sorted(caught)
    catchable = tuple(getattr(__builtins__, name, None)
                      if not isinstance(__builtins__, dict)
                      else __builtins__.get(name)
                      for name in sorted(caught))
    catchable = tuple(kind for kind in catchable if isinstance(kind, type))
    assert ValueError in catchable, sorted(caught)

    unreviewed = "Lean.ofReduceBool"
    assert unreviewed not in _reports.LAYER_AXIOM_HOME
    assert unreviewed not in _reports.LAYER_FOUNDATION

    for group, targets in PROBE_TARGETS.items():
        records = {name: [] for name in targets}
        records[targets[0]] = [unreviewed]
        try:
            verdict = probe_dependencies_valid(group, records)
        except catchable as failure:
            assert unreviewed in str(failure), (group, str(failure))
            continue
        except Exception as failure:  # pragma: no cover - the defect this holds
            raise AssertionError(
                (group, "raises a kind the audit does not catch",
                 type(failure).__name__, str(failure))) from None
        assert verdict is False, (group, verdict)


def test_the_guard_roster_names_guards_that_exist() -> None:
    """The document that holds every other number to a computation held its own
    by hand.

    Each increment here ends by naming its new guards in the roster and raising
    the total by one or two. Nothing checked either half. A guard could be named
    and never written, a written guard could be renamed and the pointer left
    behind, and the total could drift the way every hand-kept number in this
    repository has drifted --- which is the failure the whole document is about.

    One pointer had already gone stale:
    `test_each_condition_has_a_model_named_for_it` became
    `test_each_condition_is_either_refuted_or_derived` when a condition could
    first be answered by a derivation instead of a model. The claim it backs was
    never unheld, since the renamed guard does the same coverage check and more;
    what was wrong was the name a reader would have gone looking for.

    So the rule this fixes is a convention: a guard's name in code style in the
    documents below asserts that the guard exists under that name now, which is
    why the note describes the rename above without spelling the retired name.
    This file is not one of those documents, so the history can be concrete here.

    `CHANGELOG.md` is deliberately not read. A changelog entry describes a
    release, and the name a guard had then is the right name for it to use ---
    the rename above is itself recorded there under the old name. Holding
    history to today's names would be the error, not the fix.
    """
    here = sorted(REPO.glob("docs/**/*.md")) + [REPO / "README.md"]
    defined: set[str] = set()
    for path in sorted((REPO / "tests").glob("*.py")):
        defined |= set(re.findall(r"^def (test_[a-z0-9_]+)",
                                  path.read_text(encoding="utf-8"), re.M))
    assert len(defined) > 100, len(defined)

    cited: dict[str, list[str]] = {}
    for path in here:
        if not path.exists():
            continue
        for name in re.findall(r"`(test_[a-z0-9_]+)`",
                               path.read_text(encoding="utf-8")):
            cited.setdefault(name, []).append(path.name)
    assert cited, "no document cites a guard by name"
    stale = {name: sorted(set(where)) for name, where in cited.items()
             if name not in defined}
    assert not stale, stale

    note = REPO / "docs" / "research" / "CLAUSE_INDEPENDENCE.md"
    text = note.read_text(encoding="utf-8").splitlines()
    opens = [index for index, line in enumerate(text)
             if re.fullmatch(r"[A-Z][a-z-]+(?: [a-z-]+)* guards hold the measurement\.",
                             line)]
    assert len(opens) == 1, opens
    start = opens[0]
    end = next(index for index, line in enumerate(text[start:], start)
               if line.startswith("### "))
    roster = "\n".join(text[start:end])
    named = re.findall(r"`(test_[a-z0-9_]+)`", roster)
    twice = sorted({name for name in named if named.count(name) > 1})
    assert not twice, twice
    claimed = _spelled(text[start].split(" guards")[0])
    assert claimed == len(named), (claimed, len(named), sorted(named))

    # Each heading inside the roster counts the guards under it, and those
    # counts drift the same way the total does --- one of them said "One" over
    # a pair. A heading's block runs to the next heading, so a block that
    # mentions a guard belonging to another block will fail here and has to be
    # phrased without naming it. That is the cost of making the counts mean
    # something, and it is the reason the total alone was not enough: the sum
    # was right while one of its parts was wrong.
    heading = re.compile(r"^([A-Z][a-z]+) holds? (?:the|this) .+\.$")
    heads = [(index, match.group(1))
             for index, line in enumerate(text[start:end], start)
             if (match := heading.match(line)) and match.group(1).lower() in NUMBER_NAMES]
    assert len(heads) >= 10, heads
    bounds = [index for index, _ in heads] + [end]
    for position, (index, word) in enumerate(heads):
        block = "\n".join(text[index:bounds[position + 1]])
        under = sorted(set(re.findall(r"`(test_[a-z0-9_]+)`", block)))
        assert _spelled(word) == len(under), (text[index], len(under), under)
    counted = sum(_spelled(word) for _, word in heads)
    assert counted <= claimed, (counted, claimed)


# A name in code style is used two ways in these notes. Most uses point at
# something --- a symbol, a field, a file, a term of art --- and the note may
# well be pointing outside this repository: CompCert's `simulation_star`, the
# hyper-grammar interpreter's `closed_form`, the verifier package's
# `recheck_assurance_log`. Requiring every such name to exist here would be
# wrong about all three. The other use is a claim: the note says the name
# *does* something, and that is checkable, because the doing happens here.
CREDITED = (r"(?:proves|checks|establishes|derives|states|constructs|shows|"
            r"gives|records|pins|reads|extends|refutes|holds|counts|splits|names)")
# What the notes put between a credited name and the verb that credits it. The
# reader admitted nothing here at all until 2026-09-21 --- the verb had to
# follow the backtick with only spaces in between --- and English does not
# oblige. `check_seq` also proves, `congruentPath_is_not_an_equivalence`
# already refutes, the `joint_state` theorem proves,
# `Hypermath.commonWitnessesComeFromCommutativity` (L2 §VII.b) proves: seven
# names are credited across one of these and every one stood outside the guard.
# Only the words the notes actually write are listed, and the four shapes are
# each asserted to occur below, so a word in here that reaches nothing is a
# thing this file will say rather than carry.
CARRIED = (r"(?:\s+(?:also|already|then|nevertheless|separately"
           r"|theorem|clause|row"
           r"|\([^)]{0,40}\)|\[[^\]]{0,40}\]))?")
#: Not admitted: a second verb sharing one subject --- "`X` counts the rows and
#: holds every row to it" --- occurs once and credits a name the first verb
#: already credited, so reading it would add nothing to the check while making
#: the subject of `and holds` a guess whenever the first verb is not one of
#: these. Recorded because the shape is here, not because it is read.
DECLARES = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom"
    r"|namespace)\s+([A-Za-z_][A-Za-z0-9_'.!?]*)")


#: A `structure`, `inductive` or `class`, whose members are declared inside it
#: rather than by `DECLARES`.
OPENS_MEMBERS = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:structure|inductive|class)\s+([A-Za-z_][A-Za-z0-9_'.]*)")
#: A field of a structure, and a constructor of an inductive.
MEMBER_FIELD = re.compile(r"^\s+([A-Za-z_][A-Za-z0-9_']*)\s*(?:\{|\(|\[|:)")
MEMBER_CTOR = re.compile(r"^\s*\|\s*([A-Za-z_][A-Za-z0-9_']*)")


def _lean_names(root: Path) -> set[str]:
    """Every name a reader could reach in a Lean checkout: what it declares,
    the namespaces it opens, the members those declarations carry, and the
    files themselves.

    The members were missing for as long as this function existed.
    `DECLARES` reads the line a declaration starts on, and a structure's
    fields and an inductive's constructors are not on it --- so the eight
    `Conditions` fields that `CLAUSE_INDEPENDENCE.md` cites more than any other
    names in the project, `imageSimilar` and `congIntoSim` and the rest, were
    names this function said did not exist. 219 names were invisible, and
    nothing noticed because the guard that uses this set only asks about a name
    when a crediting verb follows it, and no sentence credits a field.
    """
    found: set[str] = set()
    for path in sorted(root.glob("lean4/**/*.lean")):
        if {".lake", "build"} & set(path.parts):
            continue
        found |= {path.name, path.stem}
        inside: str | None = None
        for line in path.read_text(encoding="utf-8").splitlines():
            if match := DECLARES.match(line):
                found |= {match.group(1), match.group(1).split(".")[-1]}
            if opened := OPENS_MEMBERS.match(line):
                inside = opened.group(1)
                continue
            if not line.strip() or line.strip().startswith("--"):
                continue
            if not line[0].isspace() and not line.lstrip().startswith("|"):
                inside = None
            if inside and (member := MEMBER_CTOR.match(line)
                           or MEMBER_FIELD.match(line)):
                found.add(member.group(1))
    return found


def _package_names() -> set[str]:
    """Every name `hypermath_foundations` offers a document to cite.

    This read one module. `_reports.py` holds the pinned report vocabularies,
    so its constants were the ones a note was expected to name --- but
    `PROVED_DECLARATIONS` is in `_baseline.py`, `add_surface` is a method of
    `layer_graph.py`, and a note citing either was citing something this set
    said did not exist. The package is the unit a document cites, not whichever
    module happened to be read first.
    """
    found: set[str] = set()
    for module in sorted((REPO / "src" / "hypermath_foundations").glob("*.py")):
        body = module.read_text(encoding="utf-8")
        found |= set(re.findall(r"^([A-Z][A-Z0-9_]+)\s*[:=]", body, re.M))
        found |= set(re.findall(r"^\s*(?:async\s+)?def\s+([a-z_][a-z0-9_]*)",
                                body, re.M))
        found |= set(re.findall(r"^class\s+([A-Za-z_][A-Za-z0-9_]*)", body, re.M))
    return found


def test_every_name_the_notes_credit_with_a_result_exists() -> None:
    """A note said a theorem proved something, and the theorem was gone.

    `CYCLE_WITNESSES.md` carried a table row for
    `full_clauses_and_target_without_nonzero_D`, which had become
    `full_clauses_without_nonzero_D` --- and not by a rename. The theorem's
    subject changed: the deriver moved to the limit, where its cycle is three
    steps rather than two, so the model that used to satisfy the original
    target now refutes it. The note went on asserting the old result, and the
    section built on it went on arguing from a witness it no longer had.

    The tempting guard is that every name in code style in these documents must
    exist in this repository. That guard would be wrong, and the sweep that
    found this row is what shows it: of the fourteen names it could not
    resolve, every one was legitimate. `simulation_star` is CompCert's, cited
    with a link. `closed_form` belongs to the hyper-grammar interpreter a dated
    probe ran against. `recheck_assurance_log` is the verifier package's.
    `apply_is_free` is the ordinatics dependency's. `driverCycle_FRAME` sits in
    a column headed *Previous declaration*, where being gone is the point, and
    `self_derivation_target_holds` names a theorem a numbered plan proposes to
    write. `K_n` is a subscript. Pointing outward, backward or forward are all
    things these notes correctly do.

    What separates this row from all of those is the grammar around it. The
    note does not point at the name, it credits it: the name proves, checks,
    records, refutes. A claim of that shape is about work done here, so it can
    be held to the sources here --- together with the one Lean dependency,
    whose path is read from the lakefile rather than assumed, since a name like
    `apply_is_free` is credited exactly this way and does exist. A column
    headed `Declaration` makes the same claim by position rather than by verb,
    which is where this started.

    What the reader would not do until 2026-09-21 is let anything stand between
    the name and the verb, and prose does: seven names in these notes were
    credited across an adverb, an appositive noun or a parenthesized citation,
    and all seven stood outside this guard. Sixteen credits reach their verb
    that way now. None of them is missing, so nothing was wrong --- which is
    the whole difficulty, because the floor at the bottom was the only thing
    said to notice a reader losing reach, and 233 against 140 is not a thing
    that notices.
    """
    known = _known_names()
    assert len(known) > 1500, len(known)

    credited = re.compile(r"`([A-Za-z_][A-Za-z0-9_'.]*)`" + CARRIED + r"\s+"
                          + CREDITED + r"\b")
    column = re.compile(r"^\|\s*Declaration\s*\|")
    across: Counter[str] = Counter()
    checked, missing = 0, []
    for path in sorted((REPO / "docs" / "research").glob("*.md")):
        text = path.read_text(encoding="utf-8")
        claimed: list[str] = []
        # A sentence wraps, so the verb can land on the line after its subject.
        for line in re.sub(r"\n(?=[A-Za-z`])", " ", text).splitlines():
            for found in credited.finditer(line):
                claimed.append(found.group(1))
                # What the match crossed to get from the name to the verb.
                rest = found.group(0)[len(found.group(1)) + 2:].split()
                across["nothing" if len(rest) < 2
                       else "a citation" if rest[0][0] in "(["
                       else "an appositive" if rest[0].isalpha()
                       and rest[0] in {"theorem", "clause", "row"}
                       else "an adverb"] += 1
        rows = False
        for line in text.splitlines():
            if column.match(line):
                rows = True
            elif rows and line.startswith("|"):
                if not set(line) <= set("| -"):
                    claimed += re.findall(r"^`([A-Za-z_][A-Za-z0-9_'.]*)`$",
                                          line.split("|")[1].strip())
            elif rows:
                rows = False
        for name in claimed:
            # A lowercase word with no underscore is an English word in code
            # style --- "`false` gives" --- and a single letter is a variable.
            if ("_" not in name and "." not in name
                    and (name.islower() or len(name) == 1)):
                continue
            checked += 1
            if name not in known and name.split(".")[-1] not in known:
                missing.append(f"{path.name}: {name}")
    assert not missing, missing
    # Each shape has to be reached, or a branch of the reader is a word this
    # file says and does not carry. This is the part the count cannot do: the
    # floor below catches a reader that matched nothing, and nothing else.
    for shape in ("nothing", "an adverb", "an appositive", "a citation"):
        assert across[shape], f"no credit across {shape} was read"
    # A floor, and only a floor. Prose drifting out of the regex's reach would
    # make the count fall and this fail, which is true of a drift of more than
    # a third and of no smaller one. The reach is measured in the notes
    # instead, because it is a fact about the corpus and not about this number.
    #
    # Both numbers of that comparison are in the docstring, where they can be
    # held. This one said 214 against 140 while `checked` stood at 231, which
    # is the failure this whole guard is about, one level up and in its own
    # prose; the figure was in a comment as well, where nothing can read it.
    floor = 140
    _states(test_every_name_the_notes_credit_with_a_result_exists.__doc__,
            r"and ([\d,]+) against ([\d,]+) is not a thing that notices",
            checked, floor)
    _states(test_every_name_the_notes_credit_with_a_result_exists.__doc__,
            r"([A-Za-z-]+) credits reach their verb that way now",
            sum(count for shape, count in across.items() if shape != "nothing"))
    assert checked >= floor, checked


#: Suffixes of the files these documents cite by path.
CITED_SUFFIXES = (".lean", ".hm", ".md", ".py", ".toml", ".json", ".yml",
                  ".yaml", ".txt", ".sh", ".cfg")
#: A path in code style, and a relative markdown link target.
CITED_PATH = re.compile(r"`([A-Za-z0-9_][A-Za-z0-9_./-]*(?:"
                        + "|".join(s.replace(".", r"\.") for s in CITED_SUFFIXES)
                        + r"))`")
CITED_LINK = re.compile(r"\[[^\]]*\]\(([^)\s#]+)(?:#[^)]*)?\)")
#: Generated or vendored trees. A document citing something inside one is
#: citing an output or a dependency, not this project's sources.

#: The cited paths no readable checkout carries, and why each one does not.
#: Everything else a document cites is the tail of a path that exists.
UNREADABLE_CITED_PATHS = {
    "build/RootedContinuationDraft.lean": "a build output",
    "build/live-closure-probe.json": "a build output",
    "build/verification/audit.json": "a build output",
    "src/verifier/core/kernel.py": "in the verifier-standard sources",
    "lean4/Hypermath/ConstructiveQuine.lean": "not written",
}
#: How a document says a path it cites has not been written yet.
UNWRITTEN_WORD = re.compile(r"has not been written|does not yet exist"
                            r"|is not written|remains unwritten")


def _imported_documents() -> set[str]:
    """The documents this project did not write.

    `references/precursor/manifest.json` pins each imported file by sha256, so
    those documents are evidence of what arrived, not claims this project
    makes. Their five broken links arrived with them and repairing one would
    break its provenance. Read out of the manifest rather than by directory
    name, so that dropping a snapshot from the manifest puts the document back
    under this guard instead of quietly leaving it out.
    """
    manifest = json.loads((REPO / "references" / "precursor" / "manifest.json")
                          .read_text(encoding="utf-8"))
    return {record["destination"] for record in manifest["records"]
            if record["disposition"] == "reference_snapshot"}


def _readable_path_tails() -> dict[str, str]:
    """Every tail of every path in the checkouts a document can cite, and which
    checkout carries it.

    A citation names a file by as much of its path as the sentence needs, so
    `L2Operations.lean`, `Hypermath/L2Operations.lean` and
    `lean4/Hypermath/L2Operations.lean` are all the same claim. Each checkout
    is indexed under its own directory name as well, because
    `HYPERSET_THEORY_ORDINATICS.md` gives a `Repository Coordinate` line and
    then cites `ordinatics/paper/ordinal_arithmetic.md` from it.
    """
    found: dict[str, str] = {}
    roots = [(REPO, "this checkout")]
    dependency = re.search(r'path\s*=\s*"([^"]+)"',
                           (REPO / "lean4" / "lakefile.toml")
                           .read_text(encoding="utf-8"))
    assert dependency, "the lakefile no longer declares the dependency's path"
    sibling = (REPO / "lean4" / dependency.group(1)).resolve().parent
    if sibling.exists():
        roots.append((sibling, "the " + sibling.name + " checkout"))
    for root, label in roots:
        inner: dict[str, str] = {root.name: label}
        for path in root.rglob("*"):
            if UNREAD_TREES & set(path.parts):
                continue
            parts = path.relative_to(root).parts
            for length in range(1, len(parts) + 1):
                inner.setdefault("/".join(parts[-length:]), label)
        for tail, carrier in inner.items():
            found.setdefault(tail, carrier)
            found.setdefault(root.name + "/" + tail, carrier)
    return found


def _known_names() -> set[str]:
    """Every name this project offers a document to cite.

    The Lean declarations here and in the one Lean dependency, whose path is
    read from the lakefile rather than assumed; the package's names; the guard
    names; and the file names, because a cited file name is a claim about a
    file. Three guards ask a document whether the name it wrote down exists,
    and they were each building this set themselves --- two of them already,
    in two orders, with one carrying a comment the other needed. A set assembled
    in more than one place is the same error as a count kept by hand.
    """
    dependency = re.search(
        r'path\s*=\s*"([^"]+)"',
        (REPO / "lean4" / "lakefile.toml").read_text(encoding="utf-8"))
    assert dependency, "the lakefile no longer declares the dependency's path"
    sibling = (REPO / "lean4" / dependency.group(1)).resolve().parent
    if not sibling.exists():                      # pragma: no cover
        pytest.skip(f"OPTIONAL_DEPENDENCY_ABSENT: no ordinatics checkout at {sibling}")

    known = _lean_names(REPO) | _lean_names(sibling)
    known |= set(PROBE_TARGETS) | set(SOURCE_PARAMETERS) | _package_names()
    # A cited name that is a file is a claim about a file, which
    # `test_every_path_the_documents_cite_is_one_that_exists` holds. This set
    # carried the `.lean` file names, from `_lean_names`, and carried no others
    # for no reason: "`README.md` records" and "`Countermodels.lean` records"
    # are the same shape and only one of them resolved here.
    known |= {tail for tail in _readable_path_tails()
              if "/" not in tail and "." in tail}
    known |= {entry.name for entry in REPO.iterdir() if entry.is_file()}
    # Every name a module here defines at the top level, not only the ones
    # starting `test_`. The docstring above has always said "the guard
    # names" and the pattern read the guards, which is a smaller thing: a
    # helper is a name a document can cite and be wrong about in exactly
    # the way a theorem is. The narrowing was invisible until a note cited
    # `_states` and nothing in this project could say it existed, with 114
    # more helpers standing behind it in the same condition.
    #
    # It narrowed twice. The line above said "every name a module defines at
    # the top level" and read `def`, which is every *function*: a table like
    # `CORNER_STRUCTURES` is a name a note can cite and be wrong about in the
    # same way again, and the second reading was found the same way as the
    # first, by a note citing one. A class is here for the same reason and for
    # no current citation: this is a supply of names a document may cite, so
    # an entry nothing cites costs nothing where a missing one is a hole.
    for path in sorted((REPO / "tests").glob("*.py")):
        text = path.read_text(encoding="utf-8")
        known |= set(re.findall(r"^(?:def|class) ([A-Za-z_][A-Za-z0-9_]*)",
                                text, re.M))
        known |= set(re.findall(r"^([A-Za-z_][A-Za-z0-9_]*)(?::[^=\n]+)? = ",
                                text, re.M))
    # A skip rubric category is a name too. `AGENTS.md` declares that
    # vocabulary the way the Lean sources declare theirs, and a document citing
    # `QUARANTINED_DEFECT` is citing something that exists.
    known |= set(agents_rubric()) | set(template_rubric())
    # So is a check the gate runs. `scripts/` is where this project keeps the
    # code that enforces its own policy, and a document naming
    # `check_lineage_claims` names something as real as a theorem.
    # And so is a name the layer language introduces. The four `.hm` files
    # are the specification; a document citing `ax-semantics-requires-syntax`
    # is citing the axiom that declares the closing edge of the triangle.
    known |= layer_names()
    for path in sorted((REPO / "scripts").glob("*.py")):
        known |= set(re.findall(r"^def ([a-z_][a-z0-9_]*)",
                                path.read_text(encoding="utf-8"), re.M))
    return known


def _cited_paths() -> dict[str, list[str]]:
    """Every path this project's own documents cite, and which cite it."""
    imported = _imported_documents()
    cited: dict[str, list[str]] = {}
    for doc in sorted(REPO.glob("**/*.md")):
        if UNREAD_TREES & set(doc.parts):
            continue
        where = doc.relative_to(REPO).as_posix()
        if where in imported:
            continue
        body = doc.read_text(encoding="utf-8")
        targets = set(CITED_PATH.findall(body))
        for target in CITED_LINK.findall(body):
            if re.match(r"^[a-z][a-z0-9+.-]*:", target) or target.startswith("//"):
                continue
            resolved = (doc.parent / target).resolve()
            targets.add(resolved.relative_to(REPO).as_posix()
                        if resolved.is_relative_to(REPO) else target)
        for target in targets:
            cited.setdefault(target.strip("/").removeprefix("./"), []).append(where)
    return cited


def test_every_path_the_documents_cite_is_one_that_exists() -> None:
    """A document citing a path claims the repository has it, and nothing
    checked that.

    `test_every_name_the_notes_credit_with_a_result_exists` holds the *names*
    the notes credit. It says nothing about where those names live, and it says
    nothing at all about the 208 paths the documents cite --- so a file that
    moved, or was renamed, or was never at the coordinate given, would leave
    every sentence citing it silently wrong. That is the same failure as
    `full_clauses_and_target_without_nonzero_D`, one level up: not a name that
    stopped existing but a location that stopped being the location.

    The naive guard is that every cited path resolves from the repository root,
    and it is wrong five ways over, which is why the sweep matters more than the
    assertion it ends in. A citation names a file by as much of its path as the
    sentence needs, so `L2Operations.lean` is a citation of `lean4/Hypermath/`
    and `stdlib/hyperordinal.hm` one of `references/precursor/hypermath_frame/`:
    a tail of a real path is what a citation is. The imported documents under
    `references/precursor/` are pinned by sha256 in their own manifest, so their
    five broken links are part of the evidence and not defects to repair. Three
    cited paths name build outputs, absent from a clean checkout on purpose.
    One names a file in the verifier-standard sources, which this project
    depends on and does not contain. And one is cited by three documents
    precisely because it does not exist, which the guard below holds.

    So 207 of the 212 paths the documents cite resolve, and each of the five
    that do not is classified. Five are pinned below with the reason. The sixth
    arrived afterwards and is classified by a different mechanism, because it
    is a different kind of thing: `P0_shadow_ground.hm` is a file `hyperlogic`
    carries, cited by the first document here whose subject is what this
    repository does *not* have. It is excused by the sentence that says which
    tree holds it, read out of the document by `test_family_neighbourhood`,
    rather than by an entry in this file. Once the repository has said where a
    foreign name lives, any document may cite it; what may not happen is a
    citation that resolves nowhere and says nothing.
    """
    readable = _readable_path_tails()
    cited = _cited_paths()
    elsewhere = foreign_citations()
    # The two regexes are the guard, and this is a floor under them and not a
    # measurement of them: `cited` is 208, so a document may start citing paths
    # in a shape neither regex reaches, and go on doing it until fifty-seven
    # citations have gone, before the count falls far enough to say so. The
    # comment here claimed the stronger thing for as long as it stood.
    assert len(cited) > 150, len(cited)

    unresolved = {path for path in cited
                  if path not in readable and path not in elsewhere}
    assert unresolved == set(UNREADABLE_CITED_PATHS), sorted(unresolved)
    _states(test_every_path_the_documents_cite_is_one_that_exists.__doc__,
            r"So ([\d,]+) of the ([\d,]+) paths the documents cite "
            r"resolve, and each of the ([a-z]+) that do not",
            len(cited) - len(unresolved), len(cited), len(unresolved))
    for path, reason in UNREADABLE_CITED_PATHS.items():
        if reason == "a build output":
            assert path.startswith("build/"), path


def test_the_construction_the_documents_call_unwritten_is_still_unwritten() -> None:
    """Three documents say a Lean file has not been written. If it ever is,
    all three become false and nothing would say so.

    Every other guard in this module catches a document that fell behind its
    sources. This one catches the opposite: a document the sources caught up
    to. `README.md` records that `lean4/Hypermath/ConstructiveQuine.lean` has
    not been written, `CYCLE_BOUNDARY.md` says the construction it schedules
    does not yet exist "so self-closure remains an open obligation", and
    `CONSTRUCTIVE_QUINE_SELF_CLOSURE.md` schedules it as Stage 2 of a plan.
    Those are claims about an absence, and an absence is the one kind of claim
    that expires when the work is *done*.

    Both halves are held, because either one alone fails open. If only the file
    were checked, deleting the sentences would leave the pin above asserting a
    reason no document gives. If only the sentences were checked, writing the
    file would leave three documents calling it unwritten.
    """
    unwritten = [path for path, reason in UNREADABLE_CITED_PATHS.items()
                 if reason == "not written"]
    assert unwritten == ["lean4/Hypermath/ConstructiveQuine.lean"], unwritten
    for path in unwritten:
        assert not (REPO / path).exists(), path
        said = False
        for doc in sorted(_cited_paths()[path]):
            flat = " ".join((REPO / doc).read_text(encoding="utf-8").split())
            for sentence in re.split(r"(?<=[.!?]) ", flat):
                if path in sentence and UNWRITTEN_WORD.search(sentence):
                    said = True
        assert said, "no document says " + path + " has not been written"


#: The name shape inside a span in code style. `BACKTICKED` is defined once,
#: with the guard that first reads it.
CITED_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*$")

#: The names the research notes cite in code style that this repository does
#: not declare, and what each one is instead. Pointing outward, backward and
#: forward are all things these notes correctly do; what was missing is that
#: nothing said which was which.
UNDECLARED_CITED_NAMES = {
    # Lean core, beyond the roots `FOREIGN_ROOTS` already names.
    "True": "Lean core",
    "sorryAx": "Lean core",
    # Names withdrawn from the sources, cited because they are gone. Each is
    # named in a Lean comment that says so, which the guard checks.
    "dSpansGround": "withdrawn",
    "driverCycleIsClosed": "withdrawn",
    "driverCycle_FRAME": "withdrawn",
    "simulationPairExists": "withdrawn",
    "L3Ordinatics.simulationPairExists": "withdrawn",
    # Replaced by a declaration that does exist and extends the name. The
    # sources retain the proposition under a `Claim` suffix when the theorem
    # over it stops being provable, so the replacement is what to check for.
    "ordinalZeroIdentity": "superseded",
    "ordinalSuccApplies": "superseded",
    "pathLengthArithmetic": "superseded",
    # Retired together with the inductive they were stated over, in one
    # sentence that spans three lines of `QuadrilateralFiltration`.
    "Abstraction": "withdrawn",
    "abstractionTransitive": "withdrawn",
    "syntaxToAbstraction": "withdrawn",
    "conditionalRetrace": "withdrawn",
    "driverInDAtSimulation": "superseded",
    # Scheduled rather than written, like the file it would live in.
    "CombinatorForm": "not written",
    # Other projects, cited in comparisons and with links.
    "AssuranceLedger.record_trust": "another project",
    "HypergrammarInterpreter.evaluate_source": "another project",
    "VerificationSession": "another project",
    "closed_form": "another project",
    "derivation_chain": "another project",
    "is_valid": "another project",
    "recheck_assurance_log": "another project",
    "simulation_star": "another project",
    "SIMULATION_STEP": "another project",
    "UNJUSTIFIED_STEP": "another project",
    "ordinal_wrap": "another project",
    "set.mm": "another project",
    "vstd.graph.support": "another project",
    "hypermath_form": "another project",
    "KeyError": "another project",
    "Valid": "another project",
    # Values, labels and notation that look like names.
    "PASS": "a value, not a name",
    "UNKNOWN": "a value, not a name",
    "FORM": "a value, not a name",
    "VIII": "a value, not a name",
    "Drops": "a value, not a name",
    "Needs": "a value, not a name",
    "Claim": "a value, not a name",
    "K_n": "a value, not a name",
    "U_n": "a value, not a name",
    "v1.3.0": "a value, not a name",
    "self_derivation": "a value, not a name",
    "admissions.source": "a value, not a name",
    "admissions.transitive_targets": "a value, not a name",
    # Bound in a statement rather than declared by one: `Step` and `Related`
    # are `variable` binders in `PathTransport.lean` and `copyStart` is bound
    # inside the type of `StepTransfer`.
    "Step": "a binder",
    "copyStart": "a binder",
}


def test_every_name_the_notes_cite_resolves_or_is_classified() -> None:
    """The guard above reads a sixth of the names in these notes, and a
    vocabulary of seventeen verbs decides which sixth.

    `test_every_name_the_notes_credit_with_a_result_exists` asks about a name
    only when one of `proves`, `checks`, `records` and fourteen others follows
    it. That vocabulary reached 171 of the 940 words that followed a name in
    these notes, and among the 769 it does not reach are `says`, `satisfies`,
    `requires`, `supplies`, `retains`, `preserves`, `exhibits` and `asks` ---
    about ninety sentences that credit a name with a result in words nobody
    wrote down. A name in one of those could be deleted from the sources and
    nothing here would notice. The count that stood in for this is a floor, and
    a floor cannot see a leak; that lesson is one increment old and this is the
    guard it was learned on.

    What the vocabulary was really for is false positives: of the names these
    notes cite, some are Lean's, some are other projects', some are values in a
    table, and some were withdrawn from the sources and are cited *because*
    they are gone. Restricting to credited names was a cheap way to miss those
    --- and it missed the real ones too. So the vocabulary goes, all 944 cited
    identifiers are held, and the 47 that do not resolve are classified one by
    one. Five kinds, and each has to be written down before it can exist.

    Widening what counts as resolved was most of the work.
    `_lean_names` had never read a structure's fields or an inductive's
    constructors, so the eight `Conditions` fields this project cites more than
    any other names did not exist as far as this module was concerned; and the
    Python names came from one module of the package because that is the module
    the first such citation happened to be in. Neither omission could be seen
    through the vocabulary, because no sentence credits a field with proving
    anything. A narrower reader and a narrower question hid each other.
    """
    known = _known_names()

    cited: set[str] = set()
    for path in sorted((REPO / "docs" / "research").glob("*.md")):
        for span in BACKTICKED.findall(path.read_text(encoding="utf-8")):
            if not CITED_NAME.match(span):
                continue
            # A lowercase word with no underscore is an English word in code
            # style --- "`false` gives" --- and a single letter is a variable.
            if ("_" not in span and "." not in span
                    and (span.islower() or len(span) == 1)):
                continue
            cited.add(span)
    assert len(cited) > 700, len(cited)

    unresolved = {name for name in cited
                  if name not in known and name.split(".")[-1] not in known
                  and name.split(".")[0] not in FOREIGN_ROOTS}
    assert unresolved == set(UNDECLARED_CITED_NAMES), sorted(unresolved)
    _states(test_every_name_the_notes_cite_resolves_or_is_classified.__doc__,
            r"all ([\d,]+) cited identifiers are held, and the ([\d,]+) "
            r"that do not resolve", len(cited), len(unresolved))

    # A name called withdrawn has to be called that by the sources too, or the
    # classification is this file's opinion rather than the project's record.
    # This asked the question of one line at a time and got five of the eight:
    # the sentence retiring `Abstraction`, `abstractionTransitive` and
    # `syntaxToAbstraction` runs across three lines and names them on the first
    # two, so no single line both names one and says it is gone. `retired_names`
    # reads the sentence, and the sentence before it, and is the measurement
    # this check was approximating.
    retired = retired_names([Source(path) for path in _lean_files()])
    for name, reason in UNDECLARED_CITED_NAMES.items():
        bare = name.rpartition(".")[2]
        if reason == "withdrawn":
            assert bare in retired, "no source retires " + bare
        # A superseded name is one the sources replaced rather than dropped,
        # which this project does by extending it --- `simulationPairExists`
        # became `simulationPairExistsClaim`. So the replacement has to be
        # there, or the name was withdrawn and should say so.
        if reason == "superseded":
            assert any(other != bare and other.startswith(bare)
                       for other in known), "nothing replaces " + bare


def _cited_in_lean_prose() -> dict[str, tuple[str, int]]:
    """Every declaration this project's Lean comments cite, and where first.

    The filter is the one the guard above uses on the documents, for the same
    reason: a lowercase word with no underscore inside backticks is English set
    in code style, and a single letter is a variable.
    """
    found: dict[str, tuple[str, int]] = {}
    for source in map(Source, _lean_files()):
        for number, text in source.comment_lines():
            for span in BACKTICKED.findall(text):
                if not CITED_NAME.match(span):
                    continue
                if ("_" not in span and "." not in span
                        and (span.islower() or len(span) == 1)):
                    continue
                found.setdefault(span, (source.relative, number))
    return found


def test_every_name_the_sources_cite_resolves_or_is_classified() -> None:
    """The guard above reads the documents. This reads the other prose.

    Every name check in this repository reads `docs/**/*.md` and `README.md`,
    and `lean4/` carries 3,707 lines of comment prose, most of them inside doc
    comments, which are rendered as this project's API documentation and are
    the first thing a reader of the sources meets.

    That prose was not unread, and the first draft of this said it was. Five
    guards in `tests/test_discharge_pointers.py` reach into it, each keyed to a
    narrow trigger: a line carrying the word "discharge", which is 40 of the
    3,707; a name qualified by one of this project's namespace roots; or the
    prose inside an admission's own docstring. Between them they reached 55 of
    the names these comments cite. The other 254 were read by nothing, and
    a count of what is covered cannot see what is not --- the same floor that
    cannot see a leak, arriving here as a boundary between file types that no
    document states, so there was no claim to check and no failure to notice.

    Two names had gone stale there. `conditions_iff_conditions` appeared once
    in the whole repository and named nothing; the theorem it meant is
    `prefixAxioms_iff_conditions`. `L0Ground.derivesIsDirectional` named a
    theorem that does exist --- in `L1Relations`, not `L0Ground`, and the
    docstring's whole point was that the two layers admit the same statement,
    so citing one of them twice lost exactly the fact being reported.

    What this does *not* do is keep its own list of exceptions. The
    classification the documents needed --- withdrawn, superseded, another
    project's, a value, a binder --- turns out to be the classification this
    prose needs, with not one entry added: of 323 names cited here, eight
    do not resolve and all eight are already written down. That is worth stating,
    because it is evidence the table is about the project rather than about the
    documents, and a second table would have been a second thing to keep true.
    """
    known = _known_names()
    cited = _cited_in_lean_prose()
    assert len(cited) > 250, len(cited)

    unresolved = {name for name in cited
                  if name not in known and name.split(".")[-1] not in known
                  and name.split(".")[0] not in FOREIGN_ROOTS}
    unknown = {name: cited[name] for name in unresolved
               if name not in UNDECLARED_CITED_NAMES}
    assert not unknown, sorted(
        f"{where}:{line} `{name}`" for name, (where, line) in unknown.items())

    prose = [text for source in map(Source, _lean_files())
             for _, text in source.comment_lines()]
    doc = test_every_name_the_sources_cite_resolves_or_is_classified.__doc__
    _states(doc, r"carries ([\d,]+) lines of comment prose", len(prose))
    _states(doc, r"the word .discharge., which is ([\d,]+) of the ([\d,]+);",
            sum(1 for text in prose if "ischarge" in text), len(prose))
    _states(doc, r"of ([\d,]+) names cited here, ([a-z]+) do not resolve",
            len(cited), len(unresolved))


def test_a_name_qualified_by_a_file_is_declared_in_that_file() -> None:
    """A citation that names the file it lives in has to be right about that.

    Both guards above resolve a dotted name by its last component, because Lean
    writes a name at whatever depth the surrounding namespace makes unambiguous
    and a reader that demanded the full path would reject correct prose. The
    cost is that the qualifier goes unread: `L0Ground.derivesIsDirectional`
    resolved because `derivesIsDirectional` exists --- in `L1Relations`. What
    `L0Ground` has is `derivesIsDirectional_FRAME`. Nothing in that sentence
    was false about the theorem; it was false about where the theorem is, which
    is the only thing the qualifier was there to say, and the sentence's own
    subject was that two layers admit the same statement.

    So where the qualifier is a file of this project, it is read. Twenty-eight
    names are qualified that way across both surfaces, and the rule is the
    narrow one: the name must be declared in that file, or the citation must be
    classified like any other --- `L3Ordinatics.simulationPairExists` is a
    withdrawn name that two documents cite precisely because it is gone, and it
    stays classified rather than becoming an exception here.

    A qualifier that is a namespace is not read, because a namespace spans
    files and the question has no answer there. One name is both: `Hypermath`
    is this project's top namespace and also the stem of the file that imports
    the layers, which declares nothing --- so reading it as a file would have
    failed every correctly written `Hypermath.foo` in the notes. Thirty-nine of
    the forty files are read; that one is not.
    """
    sources = [Source(path) for path in _lean_files()]
    home = {source.path.stem: {simple for simple, _, _ in source.declarations}
            for source in sources}

    # A name is qualified in Lean by the namespace it sits in, and `Hypermath`
    # is both this project's top namespace and the stem of the file that
    # imports the layers --- a file that declares nothing, so reading it as a
    # qualifier makes every correctly written `Hypermath.foo` a failure. Where
    # a stem is also a namespace the qualifier is ambiguous and is not read.
    # The namespaces come out of the qualified names `Source` already builds:
    # every dotted prefix of one is a namespace it was written inside.
    namespaces = {".".join(qualified.split(".")[:cut])
                  for source in sources
                  for _, qualified, _ in source.declarations
                  for cut in range(1, qualified.count(".") + 1)}
    home = {stem: names for stem, names in home.items()
            if stem not in namespaces}

    written: dict[str, tuple[str, int]] = {}
    for path in sorted(REPO.glob("docs/**/*.md")) + [REPO / "README.md"]:
        if any(part in UNREAD_TREES for part in path.relative_to(REPO).parts):
            continue
        relative = path.relative_to(REPO).as_posix()
        for number, line in enumerate(
                path.read_text(encoding="utf-8").split("\n"), start=1):
            for span in BACKTICKED.findall(line):
                written.setdefault(span, (relative, number))
    for name, where in _cited_in_lean_prose().items():
        written.setdefault(name, where)

    checked = 0
    wrong: list[str] = []
    for name, (relative, number) in written.items():
        stem, _, short = name.partition(".")
        # `Countermodels.lean` names the file itself, not a declaration in it.
        if not short or "." in short or short == "lean" or stem not in home:
            continue
        checked += 1
        if short in home[stem] or name in UNDECLARED_CITED_NAMES:
            continue
        elsewhere = sorted(other for other, names in home.items()
                           if short in names)
        wrong.append(f"{relative}:{number} `{name}` is in "
                     + (", ".join(elsewhere) or "no file"))
    assert len(home) == len(sources) - 1, sorted(set(home) & namespaces)
    assert checked > 25, checked
    assert not wrong, sorted(wrong)


def test_no_reader_in_these_guards_is_defined_twice() -> None:
    """A guard is only as wide as the reader it happens to get.

    `BACKTICKED` was assigned twice in this file. The first, at the top, matched
    a name shape; the second, 1,847 lines below, matched anything between
    backticks. Python keeps the last one, so both guards ran on the wide
    reader --- including the one written directly beneath the narrow
    definition, whose docstring describes a reader its own module had already
    contradicted. Nothing failed, and nothing could have: the surviving reader
    was the stricter of the two, so the collision was what kept the guard
    honest, and the mitigation for the defect was the defect.

    That is the worst version of the shape this series looks for, because the
    usual repair --- make the reader wider --- is the thing that would have
    turned the collision into a hole. The guard is therefore not about
    backticks. It is that no name in these files is bound at module level
    twice, so a reader can be read by reading it.

    Reassignment inside a function is ordinary and is not read; `try`/`except
    ImportError` and `if TYPE_CHECKING` are the two shapes that legitimately
    bind one name twice at module level, and neither is in these files today.
    """
    duplicated: list[str] = []
    files = sorted((REPO / "tests").glob("*.py"))
    files += sorted((REPO / "src" / "hypermath_foundations").glob("*.py"))
    assert len(files) > 20, len(files)

    for path in files:
        tree = ast.parse(path.read_text(encoding="utf-8"))
        first: dict[str, int] = {}
        for node in tree.body:
            names: list[tuple[str, int]] = []
            if isinstance(node, ast.Assign):
                names = [(target.id, node.lineno) for target in node.targets
                         if isinstance(target, ast.Name)]
            elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
                names = [(node.target.id, node.lineno)]
            elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                names = [(node.name, node.lineno)]
            for name, line in names:
                if name == "_":
                    continue
                if name in first:
                    duplicated.append(
                        f"{path.relative_to(REPO).as_posix()}: {name} is bound "
                        f"at line {first[name]} and again at line {line}")
                else:
                    first[name] = line
    assert not duplicated, duplicated


#: Status labels the documents write in code style on a line about a discharge.
#: `Prop` and `sorryAx` are Lean's; the rest are verdicts a report prints.
UNDECLARED_ON_DISCHARGE_LINES = {
    "FORM": "a layer verdict",
    "FRAME": "a layer verdict",
    "OPEN": "an admission verdict",
    "UNKNOWN": "an audit verdict",
    "Prop_k": "notation for the layer-k proposition",
    "sorryAx": "Lean core",
}


def _documents_that_claim_a_discharge() -> dict[str, list[tuple[int, str]]]:
    """Every line of this project's own prose that carries the word.

    Not every line making the claim, which is what this said until
    2026-09-21 and is a narrower set: some of these are prose about the
    counting rather than a claim being counted. Wide is right here,
    because the only consumer asks each line whether the names on it
    exist, and a line naming none costs nothing while a line missed is a
    hole. The word was the defect, not the reader.
    """
    imported = _imported_documents()
    found: dict[str, list[tuple[int, str]]] = {}
    for path in sorted(REPO.rglob("*.md")):
        if UNREAD_TREES & set(path.parts):
            continue
        relative = path.relative_to(REPO).as_posix()
        # An imported snapshot is someone else's prose, pinned by sha256, and a
        # changelog entry keeps the words that were true at that release.
        if relative in imported or relative == "CHANGELOG.md":
            continue
        claims = [(number, line) for number, line
                  in enumerate(path.read_text(encoding="utf-8").splitlines(), 1)
                  if "ischarge" in line]
        if claims:
            found[relative] = claims
    return found


def test_the_documents_claim_more_discharges_than_the_sources_do() -> None:
    """The reason the guard below has to exist, stated as a measurement.

    `test_discharge_claims_name_declarations_that_exist` has held the Lean
    comments since this project started checking pointers at all, and the
    module it lives in says so in its first line: *cross-module discharge
    pointers in the Lean sources*. That was where the rot had been found, so
    that was where the guard went. It was never where most of the claims are.
    The Lean comments carry the word on 40 lines; this project's own documents
    carry it on 108 lines, across 20 files. Both readers take every line with
    the word on it rather than every line making the claim, so both numbers are
    upper bounds on claims and the comparison between them is the honest part:
    a majority of the lines are outside the subject of the only guard that
    checks them, and that was true at every figure this sentence has carried.

    Those three numbers are read back out of this docstring and held to the
    sources, because the three that stood here before them were written the
    same way and every one had gone wrong by the time anything looked. It said
    52, 89 and 22. The lines had grown, the claims had grown faster, and the
    file count had *fallen* --- and the guard floored all three, at forty, at
    each other, and at fifteen, so no one of the three drifts was reportable
    and the one that ran backwards was the least reportable of them. A sentence
    that opens by calling itself a measurement is a claim like any other.
    """
    lean = sum(1 for source in map(Source, _lean_files())
               for _, text in source.comment_lines() if "ischarge" in text)
    documents = _documents_that_claim_a_discharge()
    written = sum(len(claims) for claims in documents.values())

    doc = " ".join((test_the_documents_claim_more_discharges_than_the_sources_do
                    .__doc__ or "").split())
    said = re.search(r"carry the word on (\d+) lines; this project's own "
                     r"documents carry it on (\d+) lines, across (\d+) files\.",
                         doc)
    assert said, "the sentence this guard measures is no longer in its docstring"
    assert tuple(int(group) for group in said.groups()) \
        == (lean, written, len(documents)), (
            "the docstring says " + said.group(0) + " --- the sources have "
            f"{lean}, {written} and {len(documents)}")
    assert written > lean, (written, lean)


def test_every_discharge_the_documents_claim_names_something_that_exists() -> None:
    """A document naming its proof is making the same claim a comment does.

    The two invariants are the Lean module's, applied where the claims
    outnumber it: a name cited on a line that claims a discharge has to be a
    declaration that exists, and it must not be one the sources retired. The
    second half is the half that has already gone wrong once in this project
    --- a withdrawn theorem cited as a discharge is what the Lean module was
    written to catch --- and the documents were free of it by luck rather than
    by anything checking.
    """
    known = _known_names()
    retired = retired_names([Source(path) for path in _lean_files()])
    unresolved: dict[str, str] = {}
    withdrawn: list[str] = []
    for relative, claims in _documents_that_claim_a_discharge().items():
        for number, line in claims:
            for name in cited_names(line):
                # A lowercase word in code style is this project's vocabulary,
                # not a citation: `derives` and `graduation` have glossary
                # entries of their own, and a glossary entry is where a word is
                # defined rather than where a theorem is named.
                if name.islower() and "_" not in name:
                    continue
                if name in retired:
                    withdrawn.append(f"{relative}:{number}: {name}"
                                     f" (retired at {retired[name]})")
                if name not in known and name not in FOREIGN_ROOTS:
                    unresolved.setdefault(name, f"{relative}:{number}")
    assert not withdrawn, ("retired names cited as discharges in prose:\n"
                           + "\n".join(withdrawn))
    assert set(unresolved) == set(UNDECLARED_ON_DISCHARGE_LINES), sorted(unresolved)


# Which models satisfy the self-derivation target and which refute it, read out
# of the Lean *types* rather than the theorem names. A name can say `fails` and
# state anything; the type cannot.
TARGET_NAMES = ("selfDerivationTarget", "selfDerivation", "driverCycleClaim")
TARGET_DECL = re.compile(r"^theorem\s+([A-Za-z_][A-Za-z0-9_']*)\s*:\s*(¬\s*)?("
                         + "|".join(TARGET_NAMES) + r")\s*(?:$|∧|:=)", re.M)
MODEL_NAMESPACE = re.compile(r"^namespace\s+(\S+)", re.M)
TARGET_VERDICTS = {
    "HypermathFiniteActionCountermodel": "fails",
    "HypermathFullAxiomModel": "fails",
    "HypermathTransportCountermodel": "holds",
    "HypermathTargetAtLimitModel": "holds",
}
# Crediting a model with a property, in the present tense.
TARGET_WORD = re.compile(r"self-derivation target|the same self-derivation|the target\b"
                         r"|\$S\$|selfDerivationTarget|selfDerivation\b")
MODEL_CREDITS = re.compile(r"\bsatisf(?:ies|y|ying)\b|\bcarries\b|\bproves\b"
                           r"|\bwitnesses\b|\bsupplies\b|\bgives\b")
# ...and the ways a note says a model no longer has it.
CREDIT_WITHDRAWN = re.compile(r"used to|no longer|previously|stopped|ceased|credited"
                              r"|had it|refut|fails|failed|does not|did not|before the"
                              r"|is not|has gone")


def test_no_note_credits_a_model_with_a_target_it_refutes() -> None:
    """A model's verdict on the target moved, and three notes went on crediting it.

    `test_every_name_the_notes_credit_with_a_result_exists` holds every *name*
    the notes credit to something that is declared. It cannot hold this: all
    three sentences credited a model with a *property*, and two of them named no
    declaration at all --- "the separate six-form model in
    `lean4/FiniteActionCountermodel.lean` satisfies all 39 clauses **and** the
    same self-derivation target". Every name in that sentence still exists. What
    stopped being true is the verdict, which `axDeriverAtLimit` moved by putting
    the deriver on a three-step cycle.

    So this reads the verdicts out of the Lean types --- a theorem's conclusion
    is `selfDerivationTarget` or its negation, whatever the theorem is called ---
    and refuses any present-tense sentence that credits a refuting model with
    the target. Past-tense and withdrawn credits are what the corrected notes
    are made of, so they are excluded by phrase rather than by file.
    """
    found = {}
    for lean in sorted((REPO / "lean4").rglob("*.lean")):
        text = lean.read_text(encoding="utf-8")
        hits = TARGET_DECL.findall(text)
        if not hits:
            continue
        namespace = MODEL_NAMESPACE.findall(text)[0]
        found[namespace] = "fails" if any(neg for _, neg, _ in hits) else "holds"
    # Pinned, so a model changing its verdict fails here and not only in prose.
    assert found == TARGET_VERDICTS, found

    refuting = {name for name, verdict in found.items() if verdict == "fails"}
    bad = []
    for note in sorted((REPO / "docs").rglob("*.md")):
        flat = re.sub(r"\s*\n\s*", " ", note.read_text(encoding="utf-8"))
        for sentence in re.split(r"(?<=[.:])\s+", flat):
            if not (MODEL_CREDITS.search(sentence) and TARGET_WORD.search(sentence)):
                continue
            if CREDIT_WITHDRAWN.search(sentence):
                continue
            for namespace in refuting:
                short = namespace.removeprefix("Hypermath") + ".lean"
                if namespace in sentence or short in sentence:
                    bad.append(f"{note.name}: {sentence.strip()[:120]}")
    assert not bad, bad


PAIRING_CLAIM = re.compile(
    r"independent\s+of\s+(?:the\s+)?(?:current\s+|declared\s+)?(?:39\s+)?(?:logical\s+)?clauses"
    r"|independent\s+of\s+the\s+declared\s+clauses"
    r"|not\s+decidable\s+from\s+the\s+declared\s+clauses"
    r"|not\s+decided\s+(?:by|from)\s+the\s+(?:39\s+)?clauses",
    re.I)
PAIRING_DECLARES = re.compile(
    r"^\s*(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*"
    r"(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)")

#: A `namespace` or a `section`, either of which `end` closes.
DECLARES_SCOPE = re.compile(r"^(namespace|section)(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\s*$")


def _before_proof(declaration: str) -> str:
    """`declaration` up to where its proof starts.

    Which is the first `:=` or `where` outside every bracket. Cutting at the
    first `:=` anywhere is not the same thing: `ComposeAxioms (Form := Path)`
    passes a named argument, and twenty-eight statements in `lean4/` were being
    read as far as that argument and no further. A statement cut mid-bracket is
    still a string, still splits, and still answers a question about its shape
    --- with the wrong answer, and, for a right-hand side cut down to the head
    of a structure application, with the answer a guard wants to hear.
    """
    depth = 0
    index = 0
    while index < len(declaration):
        character = declaration[index]
        if character in "([{⟨":
            depth += 1
        elif character in ")]}⟩":
            depth -= 1
        elif depth == 0 and (declaration.startswith(" := ", index)
                             or declaration.startswith(" where ", index)
                             or declaration[index:] == " where"):
            return declaration[:index]
        index += 1
    return declaration


def _lean_sources() -> list[Path]:
    """The Lean sources of the project, excluding anything a build produced."""
    return [lean for lean in sorted((REPO / "lean4").rglob("*.lean"))
            if not ({".lake", "build"} & set(lean.parts))]


def _theorem_declarations() -> dict[str, str]:
    """Every theorem in `lean4/`, statement and proof, keyed by module,
    namespace and full name.

    It used to be keyed by the bare name and it lost 89 of 1052 declarations
    that way, quietly, by two separate mechanisms. The regex stopped at the
    first dot, so the four theorems named `Alignment.<something>` were all
    recorded as `Alignment`; and 55 bare names are declared more than once
    across `lean4/`, some of them eight times, so the dictionary kept whichever
    came last. Nothing announced either loss. The guards reading this
    dictionary were therefore reading five sixths of the sources they named,
    including the one that checks statements are not cut inside a bracket, and
    a reader that fails open is worse than no reader.

    `test_the_statement_reader_sees_every_declaration` holds the repair: the
    key carries the module and the enclosing namespaces, so it is unique by
    construction rather than by luck, and the count is checked against the
    sources instead of floored.
    """
    statements: dict[str, str] = {}
    for lean in _lean_sources():
        module = lean.relative_to(REPO / "lean4").with_suffix("").as_posix()
        module = module.replace("/", ".")
        lines = lean.read_text(encoding="utf-8").split("\n")
        scopes: list[str | None] = []
        for index, line in enumerate(lines):
            opened = DECLARES_SCOPE.match(line)
            if opened:
                scopes.append(opened.group(2))
                continue
            if re.match(r"^end\b", line) and scopes:
                scopes.pop()
                continue
            found = PAIRING_DECLARES.match(line)
            if not found:
                continue
            block = [line]
            for following in lines[index + 1:]:
                if following and not following[0].isspace():
                    break
                block.append(following)
            body = " ".join(" ".join(block).split())
            key = ".".join([module, *[s for s in scopes if s], found.group(1)])
            assert key not in statements, "two declarations share a key: " + key
            statements[key] = body
    return statements


def _theorem_statements() -> dict[str, str]:
    """Every theorem in `lean4/` with its proof stripped, keyed the same way."""
    return {key: _before_proof(body)
            for key, body in _theorem_declarations().items()}


def _theorem_proofs() -> dict[str, str]:
    """Every theorem in `lean4/` with its statement stripped, keyed the same
    way. The text after the statement, which is `:= ...` or `where ...`."""
    proofs: dict[str, str] = {}
    for key, body in _theorem_declarations().items():
        proofs[key] = body[len(_before_proof(body)):].strip()
    return proofs


def _statement_named(name: str) -> str:
    """The statement of the one theorem in `lean4/` with this bare name.

    A lookup by bare name is a question about the whole project, so it says so
    and fails when the answer is not one theorem.
    """
    found = [statement for key, statement in _theorem_statements().items()
             if key.rpartition(".")[2] == name]
    assert len(found) == 1, (name, len(found))
    return found[0]


def _pairing_statements() -> dict[str, str]:
    """Every theorem whose name says it is an independence result, keyed by its
    bare name.

    The bare name is safe here and is not safe in general, so the safety is
    asserted rather than assumed: no two independence results may share one.
    """
    bare: dict[str, str] = {}
    for key, statement in _theorem_statements().items():
        name = key.rpartition(".")[2]
        if "independent" not in name:
            continue
        assert name not in bare, "two independence results share a name: " + name
        bare[name] = statement
    return bare


def _top_level_conjuncts(statement: str) -> list[str]:
    """`statement` split at every conjunction outside a bracket."""
    depth = 0
    parts: list[str] = []
    current = ""
    index = 0
    while index < len(statement):
        character = statement[index]
        if character in "([{":
            depth += 1
        elif character in ")]}":
            depth -= 1
        if depth == 0 and statement.startswith(" ∧ ", index):
            parts.append(current.strip())
            current = ""
            index += 3
            continue
        current += character
        index += 1
    parts.append(current.strip())
    return parts


def test_the_statement_reader_sees_every_declaration() -> None:
    """Every theorem in `lean4/` reaches the dictionary the guards read.

    The reader was keyed by the bare name until 2026-09-21 and lost 89 of 1052
    declarations, by two mechanisms neither of which said anything. Its regex
    stopped at the first dot, so four theorems named `Alignment.<something>`
    shared the key `Alignment`; and 55 bare names are declared more than once
    across `lean4/`, `reach` eight times, so the dictionary kept whichever came
    last. Every guard built on it was reading five sixths of what it named,
    including the one directly below, whose whole subject is readers that fail
    open.

    What makes this checkable and not merely fixed is that the count comes from
    the sources on both sides. A floor would have passed throughout: the reader
    returned 963 entries while losing 89, and `> 500` is true of both numbers.
    The loss was invisible precisely because nothing compared the reader to
    what it read.
    """
    declared = [line for lean in _lean_sources()
                for line in lean.read_text(encoding="utf-8").split("\n")
                if PAIRING_DECLARES.match(line)]
    statements = _theorem_statements()
    assert len(statements) == len(declared), (len(statements), len(declared))

    names = {PAIRING_DECLARES.match(line).group(1) for line in declared}
    unnamed = [name for name in sorted(names)
               if not any(key == name or key.endswith("." + name)
                          for key in statements)]
    assert not unnamed, "declarations the reader did not key by name: " + ", ".join(unnamed)


#: Sets of declarations that state one proposition with one proof under several
#: names. Every one of them is wanted: the clause set names its clauses
#: separately, and a model discharging three clauses or a graduation section
#: reporting four source obligations wants a declaration per clause name even
#: where two clause names are one clause. What was missing is that nothing said
#: so, so a reader counted eleven facts where there are five.
ALIAS_FAMILIES = (
    (
        "FullAxiomModel.HypermathFullAxiomModel.model_axCoop",
        "FullAxiomModel.HypermathFullAxiomModel.model_axSeq",
    ),
    (
        "FullAxiomModel.HypermathFullAxiomModel.model_axCoopIdentity",
        "FullAxiomModel.HypermathFullAxiomModel.model_axSeqIdentityL",
        "FullAxiomModel.HypermathFullAxiomModel.model_axSeqIdentityR",
    ),
    (
        "Hypermath.L2Operations.Hypermath.additionallyStaysSimilar",
        "Hypermath.L2Operations.Hypermath.nc2_L2",
    ),
    (
        "Hypermath.L2Operations.Hypermath.nc1_L2",
        "Hypermath.L2Operations.Hypermath.plusStaysSimilar",
    ),
    (
        "Hypermath.L2Operations.Hypermath.nc3_L2",
        "Hypermath.L2Operations.Hypermath.pathGroundIsIdentity",
    ),
)


def test_the_alias_families_are_the_declared_ones() -> None:
    """Eleven declarations across `lean4/` carry five propositions.

    `test_no_proposition_is_proved_twice_for_the_same_price` asked this of
    `Countermodels.lean` alone, because the reader available to it could not be
    asked about anywhere else. It can now, and the rest of the project has the
    same shape in two files. `L2Operations.lean` states each of three source
    obligations twice, once under the operation it belongs to and once under
    the `nc<n>_L2` name of the graduation section; `FullAxiomModel.lean`
    discharges five clause names with two proofs, because three of those clause
    names are one clause and two more are another.

    None of that is an error and none of it should be deleted --- a model that
    discharges `axSeqIdentityL` should say so under that name whether or not
    `axSeqIdentityR` is the same statement. The defect is that nothing said the
    names were fewer facts than they look. `sequencingClausesAreCooperationClauses`
    says it for one file, in prose and by elaborating both sides, and the
    number eleven appears nowhere.

    So the set is pinned rather than the count, and pinned by qualified name:
    a twelfth alias has to be added here before it can exist, and a family that
    stops being one --- because a proof changed, or a statement did --- fails
    here too. The cheap version of this guard would have been an upper bound on
    duplicates, which would have passed while the set drifted underneath it.
    """
    statements = _theorem_statements()
    proofs = _theorem_proofs()
    grouped: dict[tuple[str, str], list[str]] = {}
    for key, statement in statements.items():
        grouped.setdefault((key.rpartition(".")[0], _proposition(statement)),
                           []).append(key)

    found: list[tuple[str, ...]] = []
    for names in grouped.values():
        if len(names) == 1:
            continue
        by_proof: dict[str, list[str]] = {}
        for name in names:
            by_proof.setdefault(proofs[name], []).append(name)
        found.extend(tuple(sorted(same)) for same in by_proof.values()
                     if len(same) > 1)

    assert sorted(found) == sorted(ALIAS_FAMILIES), sorted(found)
    declared = [name for family in ALIAS_FAMILIES for name in family]
    assert len(declared) == len(set(declared)), "a name is in two families"
    assert len(declared) == 11, len(declared)


def test_every_statement_the_guards_read_is_a_whole_statement() -> None:
    """Three guards below read statements out of the Lean source, and the
    reader used to cut them at the first `:=` in the text.

    Lean spells a named argument `(Form := Path)`, so twenty-eight statements
    were cut inside a bracket: `ComposeAxioms (Form` was the whole of what
    `four_fold_without_transitivity` was taken to say. None of the three guards
    could have reported that, because a truncated statement is a perfectly good
    string. The corner guard *passed* on one, which was checked by writing it:
    give the upper corner the right-hand side `TotalSimilarConditions (C := C) E
    ∧ (∀ x, C x x)`, which needs no parentheses because `↔` binds looser than
    `∧`, and the old reader cut it to `TotalSimilarConditions (C` --- a
    structure at the head, no conjunction in it, an unmeasured condition waved
    through. A reader that fails open is worse than no reader.

    A statement that was cut in the right place has balanced brackets and does
    not still contain the keyword that opens a proof. Both are cheap, neither
    depends on what any particular theorem says, and together they are what
    makes the three guards below readings of Lean rather than of a prefix.
    """
    statements = _theorem_statements()
    assert len(statements) > 500, len(statements)
    unbalanced = []
    for name, statement in statements.items():
        depth = 0
        for character in statement:
            if character in "([{⟨":
                depth += 1
            elif character in ")]}⟩":
                depth -= 1
            if depth < 0:
                break
        if depth != 0:
            unbalanced.append(name)
    assert not unbalanced, "statements cut inside a bracket: " + ", ".join(unbalanced)
    trailing = [name for name, statement in statements.items()
                if statement.endswith(" where") or " where " in statement]
    assert not trailing, "statements that run into a proof: " + ", ".join(trailing)


def test_an_independence_claim_names_a_pairing() -> None:
    """Independence is a shape, and two places kept asserting it without one.

    A countermodel is half of an independence result. The other half is a model
    that satisfies the same statement, and the conjunction of the two is what
    licenses the word. Twice this repository wrote the word over one half: the
    self-derivation target was called independent while both cited models
    *satisfied* it, and four rows of the admission table above were called
    independent while naming only the refuting model. Both readings are wrong in
    the same way and neither is visible to a guard over names, because every
    name in them exists and every theorem they name is true.

    So this reads the shape instead, in both directions.

    Forward: a theorem whose name contains `independent` has to *state* a
    pairing --- two parenthesized halves joined by the only conjunction at depth
    zero, with the negation in exactly one of them. Both historical errors fail
    that shape and neither fails anything weaker. Conjoining two satisfying
    models gives two halves and no negation. Naming the refuting model alone
    gives a statement with both a conjunction and a negation in it, which is why
    "has a negation somewhere" is not enough: `PrefixAxioms` and the countermodel
    it satisfies would pass that reading while being one half of the claim its
    name makes.

    Backward: a paragraph in the notes that claims independence *from the
    clauses* and cites any Lean declaration at all has to cite one whose name
    says it is a pairing. A paragraph that cites nothing is left alone --- prose
    may summarize --- and so is a paragraph about independence in some other
    sense. The narrowness is deliberate: the wide version of this guard would
    demand a declaration behind every sentence that mentions a `.lean` file, and
    twenty of the twenty-eight such sentences here credit a file rather than a
    result.
    """
    statements = _pairing_statements()
    assert len(statements) >= 8, sorted(statements)
    unshaped: list[str] = []
    for name, statement in sorted(statements.items()):
        halves = _top_level_conjuncts(statement.split(" : ", 1)[1])
        negated = [half for half in halves if NOT_SIGN in half]
        if len(halves) != 2 or not all(half.startswith("(") for half in halves):
            unshaped.append(f"{name}: not two parenthesized halves")
        elif len(negated) != 1:
            unshaped.append(f"{name}: {len(negated)} halves carry the negation, not one")
    assert not unshaped, ("named as an independence result, stated as something "
                          "else:\n" + "\n".join(unshaped))

    names = _lean_names(REPO)
    unbacked: list[str] = []
    for path in sorted((REPO / "docs").rglob("*.md")) + [REPO / "README.md"]:
        if path.relative_to(REPO).as_posix() in HISTORICAL:
            continue
        for block in path.read_text(encoding="utf-8").split("\n\n"):
            flat = " ".join(block.split())
            if not PAIRING_CLAIM.search(flat):
                continue
            cited = [token.split(".")[-1] for token in re.findall(r"`([^`]+)`", flat)]
            cited = [token for token in cited if token in names]
            if cited and not any("independent" in token for token in cited):
                unbacked.append(f"{path.name}: {flat[:110]}")
    assert not unbacked, ("independence claimed over declarations that are not "
                          "pairings:\n" + "\n".join(unbacked))


GRID_RELATIONS = ("similar", "congruent", "simulation")
GRID_PROPERTIES = ("reflexivity", "symmetry", "transitivity")


def test_the_nine_cell_grid_is_nine_pairings() -> None:
    """A table wrote one word in nine cells and four declarations stood behind
    them.

    The grid section of `CLAUSE_INDEPENDENCE.md` says the filtration has three
    relations, a relation has three basic properties, and all nine of the
    resulting cells are independent of the 24 clauses. That is true and it was
    argued well --- the freedom theorems settle whole rows at once, which is
    stronger than settling cells. But five cells had no declaration, and the
    table gave no way to tell those five from the four that did. A reading that
    is sound today is not a checked claim, and this repository's whole subject
    is the difference.

    The names are built here rather than listed, so what is checked is the
    convention `<relation>_<property>_independent` and not a copy of the table.
    A tenth cell would need a name of that shape and a theorem of the pairing
    shape, both, before it could be written down.

    The reader carried the defect it was written to catch, until 2026-09-21.
    It found the grid by scanning the whole note for lines beginning with one
    of the three relations, which named the table only for as long as no other
    table used those as its row labels. One did, and the guard reported six
    rows where the grid has three --- a true count of a table it had no way to
    tell apart from its own. It now finds the section by its heading and reads
    rows only inside it, so a table elsewhere in the note is another table and
    not a sixth cell.
    """
    statements = _pairing_statements()
    missing = [f"{relation}_{prop}_independent"
               for relation in GRID_RELATIONS for prop in GRID_PROPERTIES
               if f"{relation}_{prop}_independent" not in statements]
    assert not missing, "grid cells with no pairing: " + ", ".join(missing)

    note = (REPO / "docs" / "research" / "CLAUSE_INDEPENDENCE.md").read_text(encoding="utf-8")
    heading = "## The whole grid: three relations, three properties"
    assert note.count(heading) == 1, heading
    section: list[str] = []
    for line in note.split(heading, 1)[1].splitlines():
        if line.startswith("## "):
            break
        section.append(line)
    heads = ("| `~~` |", "| `=~` |", "| `≡` |")
    rows = [line for line in section if line.startswith(heads)]
    assert len(rows) == 3, rows
    cells = [name for row in rows for name in re.findall(r"`([a-z_]+_independent)`", row)]
    assert sorted(cells) == sorted(f"{relation}_{prop}_independent"
                                   for relation in GRID_RELATIONS
                                   for prop in GRID_PROPERTIES), sorted(cells)


CORNER_STRUCTURES = {
    "total_similar_leaves_exactly_three_conditions": "TotalSimilarConditions",
    "minimal_upper_relations_leave_five_conditions_on_similar":
        "SimilarConditions",
}

NUMERALS = ("zero", "one", "two", "three", "four", "five", "six", "seven",
            "eight", "nine")


def _unwrapped(statement: str) -> str:
    """`statement` with any parentheses that wrap the whole of it removed."""
    while statement.startswith("(") and statement.endswith(")"):
        depth = 0
        for index, character in enumerate(statement):
            if character == "(":
                depth += 1
            elif character == ")":
                depth -= 1
                if depth == 0 and index != len(statement) - 1:
                    return statement
        statement = statement[1:-1].strip()
    return statement


def test_each_corner_condition_has_a_model_that_drops_it() -> None:
    """A characterization says what the conditions are, never how many there are.

    Both corners of `FreeFiltration.prefixAxioms_iff_conditions` are iffs, so
    each is exactly as true when one of its conditions follows from the rest.
    The count only becomes a measurement once every condition has a pair of
    relations that drops it, and the note built on both counts --- five
    conditions on the bottom relation against three at the other corner ---
    before either set of models existed.

    The drop names are built from each structure's own field names and from how
    many fields it has, so a new condition, a renamed one, or a condition that
    turns out to be derivable all need work in Lean before this passes again.
    """
    structures = _structures(REPO / "lean4" / "Countermodels.lean")
    declared = _lean_names(REPO)
    missing: list[str] = []
    for structure in CORNER_STRUCTURES.values():
        fields = structures["HypermathCountermodel.FreeFiltration." + structure]
        remaining = NUMERALS[len(fields) - 1]
        missing += [f"{remaining}_hold_without_{field}" for field in fields
                    if f"{remaining}_hold_without_{field}" not in declared]
    assert not missing, "conditions no model drops: " + ", ".join(missing)


# The ten fields of a `*Conditions` structure that no `Needs` model and no
# `<n-1>_hold_without_` theorem drops, and the declaration that accounts for
# each. There are two kinds and the difference between them matters: the first
# eight are members the layer's own models cannot separate one at a time, and
# the last two are not independent members at all.
SEPARATED_NOT_DROPPED = {
    # A split claims a count. It says the conjunction it replaced was two
    # conditions rather than one, and `WitnessConjunctionDoesNotSplit` is this
    # file's own proof that a conjunction can fail to be two. No single model
    # drops one half, because the halves are stated over the same relations and
    # a model of the layer carries both; what stands in its place is a pair of
    # models separating the halves from each other, which is the same claim a
    # drop model makes and the only form this position admits.
    ("SharpConditions", "congruentDiagonalReaches"):
        "the_rising_half_is_not_derivable",
    ("SharpConditions", "reachedIsSelfSimulating"):
        "the_descending_half_is_not_derivable",
    ("SplitComposeConditions", "unitalOnTheRight"):
        "neither_unital_half_implies_the_other",
    ("SplitComposeConditions", "unitalOnTheLeft"):
        "neither_unital_half_implies_the_other",
    ("SplitPrefixConditions", "congruentIntoReach"):
        "no_two_of_the_triangle_suffice",
    ("SplitPrefixConditions", "reachIntoSimulation"):
        "no_two_of_the_triangle_suffice",
    ("SplitTransfiniteConditions", "succIsDerived"):
        "neither_succ_half_implies_the_other",
    ("SplitTransfiniteConditions", "succIsNotSimulated"):
        "neither_succ_half_implies_the_other",
}
IMPLIED_BY_ANOTHER_LAYER = {
    # These two are not members. No model drops them because no model of the
    # whole can: they are theorems of the prefix and the operations, proved for
    # every limit and every successor at once. `TransfiniteConditions` is still
    # five conditions read on its own, which is all
    # `transfinite_clauses_are_five_conditions` claims; it is the joint count
    # that loses two, and the file says so where the joint count is made.
    ("TransfiniteConditions", "someStartAtGround"):
        "two_of_the_nineteen_are_theorems_of_the_others",
    ("TransfiniteConditions", "someEndAtLimit"):
        "two_of_the_nineteen_are_theorems_of_the_others",
}


def test_every_condition_field_is_dropped_separated_or_implied() -> None:
    """The guard above reads two structures. This reads all eleven.

    `test_each_corner_condition_has_a_model_that_drops_it` states the rule this
    project measures its counts by --- a field count is a measurement only once
    every field has a model that drops it --- and applies it to the two
    structures named in `CORNER_STRUCTURES`. There are twelve structures named
    `*Conditions` in `Countermodels.lean`, carrying sixty fields between
    them, and the other ten were outside the subject of the only guard that
    states the rule. Nothing was false: each of those ten is the right side of
    an iff, and an iff is exactly as true when one of its conditions follows
    from the rest.

    Read across all twelve, fifty fields have a model that drops them and
    ten do not, and the ten are not a residue. Eight are halves of a split, and
    a split is the one place where a drop model cannot exist even in principle:
    both halves are stated over the same relations, so every model of the layer
    carries both, and what a split needs instead is a pair of models separating
    the halves from each other. Two are not members at all --- they are
    theorems of two other layers, so no model of the whole drops them and none
    can be written.

    That the residue sorts into exactly those two kinds with nothing left over
    is the part worth stating. It is also what makes this a guard rather than a
    list: a new split with no separating pair lands in neither table and fails
    here, which is the shape the composition and transfinite splits were in
    until the models below `unitalUpToCp_iff_the_two_halves` and
    `succEscapes_iff_the_two_halves` were written.
    """
    source = REPO / "lean4" / "Countermodels.lean"
    structures = _structures(source)
    declared = _lean_names(REPO)
    namespaces = set(re.findall(r"^namespace\s+(\S+)",
                                source.read_text(encoding="utf-8"), re.M))

    conditions = {name.split(".")[-1]: fields
                  for name, fields in structures.items()
                  if name.split(".")[-1].endswith("Conditions")}
    dropped, bare = set(), set()
    for structure, fields in conditions.items():
        remaining = NUMERALS[len(fields) - 1]
        for field in fields:
            needs = "Needs" + field[0].upper() + field[1:]
            without = f"{remaining}_hold_without_{field}"
            place = dropped if (needs in declared or needs in namespaces
                                or without in declared) else bare
            place.add((structure, field))

    accounted = dict(SEPARATED_NOT_DROPPED) | dict(IMPLIED_BY_ANOTHER_LAYER)
    assert bare == set(accounted), (
        "conditions no model drops and no table accounts for: "
        + ", ".join(f"{structure}.{field}"
                    for structure, field in sorted(bare - set(accounted)))
        + "; accounted for but dropped by a model: "
        + ", ".join(f"{structure}.{field}"
                    for structure, field in sorted(set(accounted) - bare)))
    absent = sorted({name for name in accounted.values()
                     if name not in declared})
    assert not absent, "accounts that name nothing: " + ", ".join(absent)

    doc = test_every_condition_field_is_dropped_separated_or_implied.__doc__
    _states(doc, r"There are ([a-z]+) structures named", len(conditions))
    _states(doc, r"carrying ([a-z-]+) fields between them",
            sum(len(fields) for fields in conditions.values()))
    _states(doc, r"([a-z-]+) fields have a model that drops them and "
                 r"([a-z]+) do not", len(dropped), len(bare))
    _states(doc, r"([A-Za-z]+) are halves of a split",
            len(SEPARATED_NOT_DROPPED))
    _states(doc, r"([A-Za-z]+) are not members at all",
            len(IMPLIED_BY_ANOTHER_LAYER))


def test_a_corner_states_its_conditions_as_a_structure() -> None:
    """The shape that let an unmeasured condition in, closed.

    `total_similar_leaves_exactly_three_conditions` spent a long time stating
    four conjuncts under a name that said three, because the right side of its
    iff was a bare conjunction and the prose that read it off said "both
    reflexive" --- two conditions spoken as one. Nothing was false: the fourth
    conjunct is `congruent_reflexivity_is_not_a_fourth_condition`, a consequence
    of two of the others, so the iff held either way and so did the sentence.

    A conjunction on the right of an iff can grow a conjunct with no other
    change anywhere. A structure cannot: its fields are named, they are counted
    by the guard above, and every one of them needs a model that drops it. So
    both corners are required to state their conditions as one, and the
    `∧`-free right side is what this checks.
    """
    for theorem, structure in CORNER_STRUCTURES.items():
        right = _unwrapped(_statement_named(theorem).rsplit("↔", 1)[-1].strip())
        assert _top_level_conjuncts(right) == [right], (theorem, right)
        assert right.split()[0] == structure, (theorem, right)


def test_the_roster_states_its_own_shape() -> None:
    """The roster's total is a count of its own list, and nothing said so.

    `test_the_guard_roster_names_guards_that_exist` walks every file in `tests/`
    to build the set it checks the roster's names against, and then asserts that
    the set has more than a hundred members. It has two hundred and forty-two.
    It collects the roster's entry headings and asserts there are at least ten.
    There are forty. It sums what those headings claim and asserts the sum does
    not exceed the total, which permits any difference whatever; the difference
    is twenty-four, and those twenty-four are guards the roster names in the
    prose between entries and files under none of them.

    Each of those three is true. None of them is the number, and the document
    said none of them either, so the roster's reach could double or halve with
    every line of it still reading correctly. That is this repository's own
    subject occurring in the document that keeps the list of it.

    What is held here is a paragraph that states the reach, so it is a claim the
    document makes rather than a bound its checker happens to clear. It settles
    nothing about which of the hundred and thirty unnamed guards belong here:
    most are the audit's and the meta layer's own unit tests, thirty-four are in
    the two files this roster draws most of its entries from, and deciding
    between them is work this does not do. It makes the question countable.
    """
    text = (REPO / "docs" / "research"
            / "CLAUSE_INDEPENDENCE.md").read_text(encoding="utf-8").splitlines()
    start = next(index for index, line in enumerate(text)
                 if re.fullmatch(
                     r"[A-Z][a-z-]+(?: [a-z-]+)* guards hold the measurement\.",
                     line))
    end = next(index for index, line in enumerate(text[start:], start)
               if line.startswith("### "))
    region = text[start:end]
    said = " ".join(" ".join(region).split())

    def stated(pattern: str) -> tuple[int, ...]:
        found = re.search(pattern, said)
        assert found, "the roster no longer states its shape: " + pattern
        return tuple(_spelled(word[0].upper() + word[1:])
                     for word in found.groups())

    suite, mine = stated(
        r"The suite defines ([a-z][a-z\- ]*?) guards in all, and this roster "
        r"names ([a-z][a-z\- ]*?) of them\.")
    entries, = stated(r"Below stand ([a-z][a-z\- ]*?) entries;")
    under, loose = stated(
        r"; ([a-z][a-z\- ]*?) of the names here stand under one of them and "
        r"([a-z][a-z\- ]*?) stand under none")
    unnamed, drawn, drawn_files, never, never_files = stated(
        r"The ([a-z][a-z\- ]*?) guards this roster does not name at all are "
        r"([a-z][a-z\- ]*?) in the ([a-z][a-z\- ]*?) files it does draw "
        r"entries from and ([a-z][a-z\- ]*?) in ([a-z][a-z\- ]*?) files it "
        r"has never cited once\.")

    named = set(re.findall(r"`(test_[a-z0-9_]+)`", "\n".join(region)))
    heading = re.compile(r"^([A-Z][a-z]+) holds? (?:the|this) .+\.$")
    heads = [index for index, line in enumerate(region)
             if (match := heading.match(line))
             and match.group(1).lower() in NUMBER_NAMES]
    blocks = heads + [len(region)]
    covered: set[str] = set()
    for position, index in enumerate(heads):
        covered |= set(re.findall(r"`(test_[a-z0-9_]+)`",
                                  "\n".join(region[index:blocks[position + 1]])))

    files = {path.name: set(re.findall(r"^def (test_[a-z0-9_]+)",
                                       path.read_text(encoding="utf-8"), re.M))
             for path in sorted((REPO / "tests").glob("*.py"))}
    files = {name: guards for name, guards in files.items() if guards}
    defined = set().union(*files.values())
    cited = {name for name, guards in files.items() if guards & named}
    absent = {name for name, guards in files.items() if not guards & named}

    assert (suite, mine) == (len(defined), len(named)), (
        "the roster says it names {} of {} guards; it names {} of {}".format(
            mine, suite, len(named), len(defined)))
    assert entries == len(heads), (entries, len(heads))
    assert (under, loose) == (len(covered), len(named - covered)), (
        "the roster says {} of its names stand under an entry and {} do not; "
        "the counts are {} and {}".format(
            under, loose, len(covered), len(named - covered)))
    assert unnamed == len(defined - named), (unnamed, len(defined - named))
    assert (drawn, drawn_files) == (
        len({guard for name in cited for guard in files[name] - named}),
        len(cited)), (drawn, drawn_files, sorted(cited))
    assert (never, never_files) == (
        sum(len(files[name]) for name in absent), len(absent)), (
        never, never_files, sorted(absent))
    assert drawn + never == unnamed, (drawn, never, unnamed)
    assert under + loose == mine, (under, loose, mine)
