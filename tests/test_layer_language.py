"""The layer language, which nothing in this suite had ever read.

`L0_ground.hm` through `L3_ordinatics.hm` are the specification the Lean
development formalises and the audit hashes.  Every other guard here holds a
document to the Lean sources, or the Lean sources to a document.  The four
files in between were the input to a sha256 and nothing else: no reader in
this repository had ever opened one and asked what it declares.

So a document could name a layer axiom that no layer declares, and nothing
would say so.  Three did.  `docs/terms/` cited `ax-sem-nec`, `ax-sub-nec` and
`ax-syn-nec`, and the search for them ends in the commit that added the
dictionary --- they were short forms written in prose for axioms whose real
names are `ax-semantics-requires-syntax`, `ax-substance-requires-semantics`
and `ax-syntax-requires-substance`.  Every sentence around them was true.  The
triangle is the triangle, each cited edge is the edge the declaration states,
and the only thing wrong was that the names did not exist.

Reading the language is the whole repair, and reading it required getting the
grammar right in both directions.  A reader that knows only `axiom` misses the
eighty-five names `derive` introduces and reports them as undeclared.  A
reader that matches names anywhere in the text finds
`ax-syntax-precedes-semantics`, which exists only in the comment recording its
own retirement, and reports it as declared.  Neither is a smaller mistake than
the other.
"""

from __future__ import annotations

import re
from pathlib import Path

from test_family_neighbourhood import foreign_citations

from test_discharge_pointers import UNREAD_TREES

REPO = Path(__file__).resolve().parents[1]

#: Imported specifications belonging to other projects.  They are pinned by
#: sha256 in their own manifest and are not this repository's vocabulary.
IMPORTED = "references/precursor/"

_NAME = r"([A-Za-z_][A-Za-z0-9_'-]*)"

#: Every statement form in the layer language that introduces a name.  A form
#: absent from this table is a form nothing reads, which is the condition the
#: first guard below exists to prevent, so the table is the grammar and not a
#: sample of it.
INTRODUCES = {
    "axiom": re.compile(r"^axiom\s+" + _NAME + r"\s*:"),
    "derive": re.compile(r"^derive\s+" + _NAME + r"\s+as\s+\w+"),
    "opaque": re.compile(r"^opaque\s+" + _NAME + r"\s*::"),
    # `primitive deriver : Form` uses one colon where the rest use two.
    "primitive": re.compile(r"^primitive\s+" + _NAME + r"\s*::?"),
    "relation": re.compile(r"^relation\s+" + _NAME + r"\s*::"),
    "close": re.compile(r"^close\s+" + _NAME + r"\b"),
}

#: A statement about the layers rather than about a Form.  It introduces no
#: name, and saying so here is what keeps it from counting as unparsed.
CARRIES_NO_NAME = ("graduation",)

STATEMENT = re.compile(r"^([a-z][a-z-]*)\b")

#: A layer comment recording that a name is gone.  The layer files retire a
#: name the way the Lean sources do -- in the prose beside the thing that
#: replaced it -- so the retirement is read, not listed.
RETIREMENT = re.compile(
    r"\b(?:previously stated as|renamed from|retired|withdrawn|superseded by"
    r"|no longer)\b[^.]{0,60}?\b((?:ax|close)-[a-z0-9-]+)")

#: Short forms the dictionary carried for axioms that were never declared
#: under those names, each mapped to the name that does exist.  A note
#: recording the drift has to be able to write down what it corrected -- the
#: same reason the prose counters exempt a quoted number -- so these may be
#: cited anywhere except the dictionary, which is where citing them was the
#: claim.  The replacement is held to being real, so the record cannot rot
#: into a pair of names that both mean nothing.
NEVER_INTRODUCED = {
    "ax-sem-nec": "ax-semantics-requires-syntax",
    "ax-sub-nec": "ax-substance-requires-semantics",
    "ax-syn-nec": "ax-syntax-requires-substance",
}

#: Where citing one of them is the claim rather than the record of it.
DICTIONARY = "docs/terms/"

#: A name shaped like one the layers introduce.  The prefixes are the ones the
#: layer language actually uses for hyphenated names, so this asks a document
#: "you appear to be citing a layer name" and nothing wider.
LAYER_SHAPED = re.compile(r"\b((?:ax|close)-[a-z0-9-]+)\b")


def layer_files() -> list[Path]:
    """This repository's own layer files, not the ones it has imported."""
    found = []
    for path in sorted(REPO.rglob("*.hm")):
        if UNREAD_TREES & set(path.parts):
            continue
        if path.relative_to(REPO).as_posix().startswith(IMPORTED):
            continue
        found.append(path)
    assert found, "no layer files: the reader is looking in the wrong place"
    return found


def _statements(path: Path):
    """Left-margin lines. Indentation is a statement's body, not a statement."""
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line or line[0] in " \t-#":
            continue
        yield number, line


def layer_declarations() -> dict[str, tuple[str, str, int]]:
    """Every name the layers introduce, with the form that introduced it."""
    declared: dict[str, tuple[str, str, int]] = {}
    for path in layer_files():
        for number, line in _statements(path):
            head = STATEMENT.match(line)
            if head is None or head.group(1) in CARRIES_NO_NAME:
                continue
            rule = INTRODUCES.get(head.group(1))
            if rule is None:
                continue
            found = rule.match(line)
            if found:
                declared[found.group(1)] = (head.group(1), path.name, number)
    return declared


def layer_names() -> set[str]:
    """The layer vocabulary, for readers that ask whether a name resolves."""
    return set(layer_declarations())


def retired_layer_names() -> dict[str, tuple[str, int]]:
    """Names the layer comments record as gone, read out of the comments."""
    retired: dict[str, tuple[str, int]] = {}
    for path in layer_files():
        for number, line in enumerate(
                path.read_text(encoding="utf-8").splitlines(), 1):
            if not line.lstrip().startswith("--"):
                continue
            for found in RETIREMENT.finditer(line):
                retired[found.group(1)] = (path.name, number)
    return retired


def test_every_statement_in_the_layer_language_is_one_the_reader_knows() -> None:
    """A form nothing parses is a form nothing can hold to anything.

    This is the anti-vacuity guard for the two below it.  Both of them ask
    whether a cited name was introduced, and both answer "no" for free if the
    reader cannot see the statement that introduces it -- which is exactly how
    `derive` was nearly missed, eighty-five names in one keyword.  So every
    left-margin line in a layer file has to be a statement this module knows,
    and has to yield the name it introduces.
    """
    unread: list[str] = []
    for path in layer_files():
        for number, line in _statements(path):
            head = STATEMENT.match(line)
            if head is None:
                unread.append(f"{path.name}:{number}: {line[:50]}")
                continue
            keyword = head.group(1)
            if keyword in CARRIES_NO_NAME:
                continue
            rule = INTRODUCES.get(keyword)
            if rule is None:
                unread.append(f"{path.name}:{number}: unknown form {keyword!r}")
            elif not rule.match(line):
                unread.append(f"{path.name}:{number}: unparsed {line[:44]}")
    assert not unread, "statements the layer reader cannot read:\n" + "\n".join(
        unread)
    declared = layer_declarations()
    assert len(declared) > 100, len(declared)
    forms = {form for form, _, _ in declared.values()}
    assert forms == set(INTRODUCES), sorted(forms ^ set(INTRODUCES))


def test_every_layer_name_a_document_cites_is_one_a_layer_introduces() -> None:
    """A name in a document is a claim that the system has a thing by it.

    The claim is cheap to make and was uncheckable, so the dictionary carried
    three axiom names that no layer ever declared, in sentences whose content
    was correct.  Nothing in the prose was false; the artifact simply did not
    have the thing the prose named.
    """
    declared = layer_declarations()
    retired = retired_layer_names()
    elsewhere = foreign_citations()
    unresolved: dict[str, str] = {}
    seen: set[str] = set()
    for suffix in ("*.md", "*.lean"):
        for path in sorted(REPO.rglob(suffix)):
            if UNREAD_TREES & set(path.parts):
                continue
            relative = path.relative_to(REPO).as_posix()
            if relative.startswith(IMPORTED):
                continue
            for number, line in enumerate(
                    path.read_text(encoding="utf-8").splitlines(), 1):
                for name in LAYER_SHAPED.findall(line):
                    seen.add(name)
                    if name in declared or name in retired:
                        continue
                    if (name in NEVER_INTRODUCED
                            and not relative.startswith(DICTIONARY)):
                        continue
                    # A name the repository has said lives in another tree.
                    # `ax-no-return` is a gate the precursor's draft declares,
                    # named in a paragraph that says so; the claim is true and
                    # this reader had no way to tell "elsewhere" from "wrong".
                    if name in elsewhere:
                        continue
                    unresolved.setdefault(name, f"{relative}:{number}")
    for short, real in NEVER_INTRODUCED.items():
        assert real in declared, (
            short + " was corrected to " + real + ", which no layer declares")
    # A reader that has stopped finding documents resolves nothing and
    # reports nothing, which reads exactly like a repository in good order.
    assert len(seen) > 10, sorted(seen)
    assert not unresolved, (
        "layer names the documents cite and no layer introduces: "
        + str(sorted(unresolved.items())))


def test_a_name_a_layer_retires_is_not_a_name_a_layer_introduces() -> None:
    """A retirement recorded beside its replacement has to mean something.

    `ax-semantics-requires-syntax` carries the line saying it was once stated
    as `ax-syntax-precedes-semantics`.  That sentence is the only reason the
    old name may appear in a document at all, and it is worth nothing if the
    old name is also still declared somewhere: then the document citing it is
    citing a live axiom and the comment is describing a rename that did not
    happen.
    """
    declared = layer_declarations()
    retired = retired_layer_names()
    assert retired, "no layer records a retirement, so the reader is stale"
    both = sorted(name for name in retired if name in declared)
    assert not both, "names retired and still introduced: " + str(both)


def test_the_dictionary_keeps_the_shape_its_own_template_states() -> None:
    """`docs/terms/__template__.md` is a form this project states about itself.

    Twenty-one entries follow it exactly, which is why it is worth holding: a
    form kept by hand stays kept until it does not, and the twenty-second
    entry is the one nobody checks.  The template's own headings are the
    specification -- the shape is read from it rather than repeated here, so
    changing the template changes what the entries must be.
    """
    terms = REPO / "docs" / "terms"
    template = terms / "__template__.md"
    assert template.exists(), "the dictionary no longer states a template"
    heading = re.compile(r"^## (.+?)\s*$", re.M)
    shape = heading.findall(template.read_text(encoding="utf-8"))
    assert len(shape) >= 4, shape

    entries = sorted(p for p in terms.glob("*.md") if p != template)
    assert len(entries) > 10, len(entries)
    off: list[str] = []
    for path in entries:
        text = path.read_text(encoding="utf-8")
        if heading.findall(text) != shape:
            off.append(f"{path.name}: {heading.findall(text)}")
        # The title is the term, and the term is the filename: an entry
        # titled something else is an entry no link can be checked against.
        first = text.splitlines()[0] if text.strip() else ""
        if first != "# " + path.stem:
            off.append(f"{path.name}: titled {first!r}")
    assert not off, "dictionary entries off the template:\n" + "\n".join(off)


#: An operator written infix: a symbol bound to a suffix, like `+_ord`. Every
#: declaration form in this language introduces a word, so a symbol can never
#: acquire one without a new form being added --- which is the whole reason
#: these are worth finding separately from the names.
LAYER_OPERATOR = re.compile(r"(?<![A-Za-z0-9_-])([+×*/^-]_[a-z][a-z0-9]*)")

#: The operators the layers use without declaring, and which kind of open each
#: one is: "used" means formal lines apply it, "announced" means only banners
#: and permits name it. `L3_ordinatics.hm` says this in its own closing notes.
#: The table is here so the note cannot quietly stop being true in either
#: direction --- declaring one, or the last use of one going away.
UNDECLARED_OPERATORS = {"+_ord": "used", "×_ord": "announced"}

#: The one line in the corpus that discloses it, held so the disclosure and
#: the measurement cannot drift apart.
OPERATOR_DISCLOSURE = "never declared"


def test_every_operator_the_layers_use_is_declared_or_disclosed() -> None:
    """A symbol the layers compute with has to be introduced, or said not to be.

    `L3_ordinatics.hm` closes with a note saying `+_ord` and its multiplicative
    partner are used and never declared, that Section I's permit and the
    Section IV banner both announce them, and that no primitive, opaque or
    relation line introduces either. That note is prose. Nothing read it, so
    nothing failed when it stopped being true --- and it can stop being true in
    two opposite ways, which is why holding it needs a table rather than a
    search for the sentence.

    Measured: exactly two operators exist in the whole layer language and
    neither is declared. They are different kinds of open, and the difference
    is the finding. `+_ord` is applied on five lines that are not comments, one
    of them step 3 of `close(congruent-path-internals)` asserting that it "is
    now available (Section IV)" --- so this file's only close of a lower
    layer's residual rests on a symbol nothing introduces, and so does the
    discharge of the L2 composition-length-additive frame. Its partner is announced twice
    and applied nowhere; retiring it costs nothing and closing `+_ord` costs a
    declaration, which is a decision about the language and not a repair.

    The arms are self-maintaining rather than pinned to the count. If every
    formal use of an operator marked "used" goes away it becomes announced, and
    this fails until the table says so; if one is declared it drops out of the
    undeclared set, and this fails until the table stops claiming it. Neither
    direction can pass quietly, which is what the prose could not do.

    A line counts as a comment when it opens with the marker, so an operator
    written inside a trailing aside would read as a use. Seven lines carry an
    aside after formal text and none carries an operator, so the narrowing is
    recorded rather than coded around. The asides in these files are written
    with an em dash, which is punctuation here and not a marker at all ---
    reading one as a marker is what made this count four for a while.
    """
    declared = layer_names()
    found: dict[str, list[tuple[str, int, bool]]] = {}
    for path in layer_files():
        for number, line in enumerate(
                path.read_text(encoding="utf-8").splitlines(), 1):
            comment = line.lstrip().startswith("--")
            for match in LAYER_OPERATOR.finditer(line):
                found.setdefault(match.group(1), []).append(
                    (path.name, number, comment))
    assert found, "no operator found at all: the reader is looking for nothing"

    undeclared = {name: sites for name, sites in found.items()
                  if name not in declared}
    assert set(undeclared) == set(UNDECLARED_OPERATORS), {
        "found undeclared": sorted(undeclared),
        "table says": sorted(UNDECLARED_OPERATORS)}

    wrong: list[str] = []
    for name, kind in UNDECLARED_OPERATORS.items():
        formal = [f"{where}:{number}"
                  for where, number, comment in undeclared[name] if not comment]
        if kind == "used" and not formal:
            wrong.append(f"{name}: called used, applied on no left-margin line")
        if kind == "announced" and formal:
            wrong.append(f"{name}: called announced, but applied at "
                         + ", ".join(formal))
    assert not wrong, "the table and the layers disagree:\n" + "\n".join(wrong)

    # And the layers have to keep saying it. A measurement nothing states is
    # one a reader of the language itself never learns.
    disclosure = [f"{path.name}:{number}"
                  for path in layer_files()
                  for number, line in enumerate(
                      path.read_text(encoding="utf-8").splitlines(), 1)
                  if OPERATOR_DISCLOSURE in line
                  and all(name in line for name in UNDECLARED_OPERATORS)]
    assert len(disclosure) == 1, disclosure
