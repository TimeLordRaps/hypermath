"""What a layer file says about itself in its own header.

Each of the four opens with a header that is, in part, an account of the file
beneath it: a list of its sections, counts of what those sections hold, and
sentences saying where a thing declared in one place is closed in another. All
of it is hand-written, all of it sits beside the thing it describes, and none
of it was read by anything.

The account is kept in two shapes and one of the four keeps none.
`L0_ground.hm` writes its sections inline, in a run of prose after "Sections:",
with counts in parentheses. `L2_operations.hm` and `L3_ordinatics.hm` write a
block, one section to a line. `L1_relations.hm` lists nothing; it carries the
census parameters and stops. That asymmetry is recorded rather than repaired,
because it is the same boundary the grant-copy convention has --- the
convention starts at L2 --- and which side L1 belongs on is not decidable from
the files.

The finding was in the third kind of claim. Three sentences in `L0_ground.hm`
said the semantic close of its seven executive opaques was `L0` Section IX:

    their full semantic close is Section IX.
    opaque declarations here; semantic closes in Section IX.
    OPEN at executive layer (Section VIII closes stated, semantics pending
    Section IX).

Section IX exists, which is why nothing caught it. It is the self-kernel, it
contains no `close` statement at all, and it says of itself that at L0 "this is
structural verification only (not semantic validation)", deferring the
validator to L1 in so many words. The seven closes are in `L1_relations.hm`
Section IV, which is titled "SEMANTIC CLOSES FOR EXECUTIVE OPAQUES", holds
exactly seven, and says it discharges L0 self-kernel steps 25-31.

Eleven statements in the same file already said L1: the header's FRAME residual
reading "executive opaques semantic content (L1)"; the line introducing the
seven census rows as "Semantic closes deferred to L1"; those seven rows
themselves, one per opaque, each ending "semantic close: L1 pending. FRAME/L1.";
the census close's "Semantic validation: L1 (deferred, dependency named)"; and
Section IX's own "VALIDATOR (L1)". So a pointer that resolved, and landed on a
section holding none of what it named, stood three times against eleven
statements of the truth --- the third of the three sitting four lines above the
banner of the section it named.

What is recorded and not repaired is a status question the same note raises:
"Current graduation status: ... OPEN at executive layer" at line 568, against
"FORM (executive layer)" in the header five hundred and fifty lines above and
`close: FORM` in the census a hundred lines below. The note's own parenthesis
says why it might be both --- closes stated, semantics pending --- so whether
L0's executive layer is FORM on structural grounds while OPEN on semantic ones
is a question about the theory, not about its bookkeeping, and it is left for
the reader who owns the theory.
"""

from __future__ import annotations

import re

from _docstring_counts import _states
from test_layer_ledger import layer_paths

#: How far into a file its account of itself runs. Every list ends well inside
#: this, and the first `SECTION` banner is the real floor.
HEADER = 45

#: A section of the file, which is what all of these claims are about.
BANNER = re.compile(r"^--\s*SECTION\s+([IVX]+(?:\.[a-z])?)\s*:")

#: The block shape, one section to a line, as `L2` and `L3` write it. The colon
#: has to follow the numeral: "Status: FORM (relational layer, Sections I-VII)"
#: is a claim about a range and not an entry in a list.
BLOCK = re.compile(r"^--\s+([IVX]+(?:\.[a-z])?)\s*:\s*(\S.*?)\s*$")

#: The inline shape, as `L0` writes it: a run of prose after "Sections:", with
#: the entries separated by commas --- except that the counts are separated by
#: commas too, so the run cannot be split on them. It is split on the entry
#: heads instead, a numeral after a comma with a lowercase word following.
INLINE_RUN = re.compile(r"\bSections:\s*(.+?)(?:\s+(?:Triangle:|Maps to)|$)")
INLINE_HEAD = re.compile(r"(?:^\s*|,\s*)([IVX]+(?:\.[a-z])?)\s+(?=[a-z])")

#: A count inside an entry, in either of the two orders `L0` writes, sometimes
#: four words apart in the same list: "VII graduation criterion (4 NCs
#: discharged)" puts the number first, "III axioms (4)" puts it last. A reader
#: that knows only the first order sees six of the eight counts and reports
#: nothing missing, because the two it cannot see it also cannot miss.
#:
#: The lookbehind on the first is the rest of the reading: without it, `L1` and
#: `L2` in "(from L1 graduation)" and "L2 self-kernel" are read as the
#: quantities one and two, and the guard measures three things nobody claimed
#: and finds all three absent.
COUNT = re.compile(r"(?<![A-Za-z])(\d+)\s+([A-Za-z]+)")
COUNT_LAST = re.compile(r"\b([A-Za-z]+)\s*\((\d+)\)")

#: What a count can be a count of. A word outside this is not skipped quietly
#: --- the guard fails on it, because a count nothing measures is the thing
#: this module exists to prevent.
KIND = {"axioms": "axiom", "axiom": "axiom", "derives": "derive",
        "derive": "derive", "opaques": "opaque", "opaque": "opaque",
        "primitives": "primitive", "primitive": "primitive",
        "relations": "relation", "relation": "relation",
        "closes": "close", "close": "close",
        "steps": "step", "step": "step", "ncs": "nc", "nc": "nc"}

#: A section named as the place something is closed, with the section standing
#: as the object of the claim. The subject form is a different sentence and
#: must not be read as this one: "Section VIII closes that gap" and "Section
#: VIII closes 7 previously informal terms as opaque predicates" are prose
#: about what a section accomplishes, and Section VIII holds no `close` at all.
CLOSED_AT = re.compile(
    r"\b(?:semantic\s+close[sd]?|closes?|closed|pending)"
    r"\s+(?:is\s+|in\s+|at\s+)?(?:(L\d)\s+)?Section\s+([IVX]+(?:\.[a-z])?)",
    re.I)

#: The one layer that keeps no list of its sections.
UNLISTED = {1}


def sections(index: int) -> dict[str, list[str]]:
    """Each section of a layer file, from its banner to the next."""
    lines = layer_paths()[index].read_text(encoding="utf-8").splitlines()
    marks = [(number, found.group(1)) for number, line in enumerate(lines)
             if (found := BANNER.match(line))]
    return {roman: lines[start:(marks[position + 1][0]
                                if position + 1 < len(marks) else len(lines))]
            for position, (start, roman) in enumerate(marks)}


def listing(index: int) -> list[tuple[str, str]]:
    """A layer's own list of its sections, in whichever shape it keeps one."""
    lines = layer_paths()[index].read_text(encoding="utf-8").splitlines()
    head = lines[:HEADER]
    block = [(found.group(1), found.group(2)) for line in head
             if (found := BLOCK.match(line))]
    if block:
        return block
    joined = " ".join(line.lstrip("- ").strip() for line in head)
    run = INLINE_RUN.search(joined)
    if not run:
        return []
    text = run.group(1)
    heads = [(found.start(1), found.group(1))
             for found in INLINE_HEAD.finditer(text)]
    return [(roman, text[start:(heads[position + 1][0]
                                if position + 1 < len(heads) else len(text))])
            for position, (start, roman) in enumerate(heads)]


def tally(body: list[str]) -> dict[str, int]:
    """What a section actually holds, by the keyword that introduces it."""
    found = {keyword: sum(1 for line in body
                          if re.match(rf"^{keyword}\s", line))
             for keyword in ("axiom", "derive", "opaque", "primitive",
                             "relation", "close")}
    found["step"] = sum(1 for line in body
                        if re.match(r"^(--\s*)?\s*step\s+\d+\s*:", line))
    found["nc"] = len({number for line in body
                       for number in re.findall(r"\bNC-(\d+)", line)})
    return found


def test_every_section_a_header_lists_is_a_section_the_file_has() -> None:
    """A list of the file's parts, kept by hand, beside the parts.

    Both directions: a listed section the file does not have is a promise, and
    a section the list omits is the half that renumbering breaks quietly.
    """
    kept, wrong = set(), []
    for index in sorted(layer_paths()):
        listed = [roman for roman, _ in listing(index)]
        have = sections(index)
        assert have, f"L{index} has no sections at all"
        if not listed:
            continue
        kept.add(index)
        assert len(listed) == len(set(listed)), f"L{index} lists one twice"
        for roman in sorted(set(listed) - set(have)):
            wrong.append(f"L{index}: the header lists Section {roman} and the"
                         f" file has no such section")
        for roman in sorted(set(have) - set(listed)):
            wrong.append(f"L{index}: the file has Section {roman} and the"
                         f" header does not list it")

    assert kept == set(layer_paths()) - UNLISTED, (
        f"layers keeping a list: {sorted(kept)}, recorded as not keeping one:"
        f" {sorted(UNLISTED)}")
    assert len(kept) >= 3, sorted(kept)
    assert sum(len(listing(index)) for index in kept) >= 25, (
        "too few entries read for the two shapes both to be covered")
    assert not wrong, "sections a header and its file disagree about:\n" + "\n".join(
        wrong)


def test_a_header_count_of_a_section_is_the_count_that_section_has() -> None:
    """Eight numbers, written into the header, measured by nothing until now.

    `L0` says its Section III holds four axioms, its Section IV five derives,
    its Section VII four necessity constraints, its Section VIII seven opaques
    and seven axioms and three derives, and its Section IX forty-one census
    steps; `L2` says its Section VIII holds thirty-nine. Every one is right.
    Being right is not the same as being held: the count of `L2`'s census sat
    in that line reading twenty-nine against a census of thirty-nine until a
    guard was pointed at it, and nothing about the file looked wrong meanwhile.

    This said nine, and listed eight, above `assert len(checked) >= 8`. The
    sentence and the list disagreed in the one docstring that exists to say
    that a header and its file must not; the floor admitted both, and the count
    is now held to what the reader finds.
    """
    checked, wrong = [], []
    for index in sorted(layer_paths()):
        have = sections(index)
        for roman, text in listing(index):
            claims = [(number, word) for number, word in COUNT.findall(text)]
            claims += [(number, word)
                       for word, number in COUNT_LAST.findall(text)]
            for number, word in claims:
                kind = KIND.get(word.lower())
                assert kind, (
                    f"L{index} Section {roman} counts {number} {word!r}, and"
                    f" nothing here can measure a {word!r}")
                actual = tally(have.get(roman, []))[kind]
                checked.append((index, roman, kind, int(number)))
                if actual != int(number):
                    wrong.append(f"L{index}: the header says Section {roman}"
                                 f" holds {number} {word}, and it holds"
                                 f" {actual}")

    _states(test_a_header_count_of_a_section_is_the_count_that_section_has.__doc__,
            r"^([A-Za-z]+) numbers, written into the header", len(checked))
    assert len({kind for _, _, kind, _ in checked}) >= 4, (
        "the counts are all of one kind, so the reader covers one keyword")
    assert len({index for index, _, _, _ in checked}) >= 2, (
        "one layer is being read, so the reader has narrowed")
    assert not wrong, "counts a header claims and its sections do not hold:\n" + "\n".join(
        wrong)


def test_a_section_named_as_where_something_closes_is_a_section_that_closes() -> None:
    """Section IX exists. That is the whole reason nothing caught it.

    A pointer at a section is not checked by resolving it --- all fifty-five
    section references in these files resolve, and three of them named a
    section holding none of what they said it held. What is asked here is that
    a section named as the place a thing is closed contains a `close`.
    """
    files = {index: layer_paths()[index].read_text(encoding="utf-8")
             for index in sorted(layer_paths())}
    closes = {index: {roman: tally(body)["close"]
                      for roman, body in sections(index).items()}
              for index in files}
    assert sum(sum(here.values()) for here in closes.values()) >= 10, closes

    found, wrong = [], []
    for index, text in sorted(files.items()):
        for number, line in enumerate(text.splitlines(), 1):
            for hit in CLOSED_AT.finditer(line):
                where = int(hit.group(1)[1]) if hit.group(1) else index
                roman = hit.group(2)
                found.append((index, where, roman))
                if not closes.get(where, {}).get(roman):
                    wrong.append(
                        f"L{index}:{number}: names L{where} Section {roman} as"
                        f" where something closes, and that section holds no"
                        f" close — {line.strip()[:60]}")

    assert len(found) >= 4, found
    assert len({(where, roman) for _, where, roman in found}) >= 2, (
        "every pointer names one section, so nothing is distinguished")

    # The subject form is prose and must stay out. `L0` Section VIII "closes 7
    # previously informal terms as opaque predicates" and holds no `close`
    # statement of its own; a reader taking that for a pointer reports a defect
    # that is not there, and the repair for one of those is to delete a true
    # sentence. The trap cannot be set on whole lines, because the two forms
    # share one: "(Section VIII closes stated, semantics pending L1 Section
    # IV)" is a false pointer and a true one inside a single parenthesis. What
    # is asked is that no pointer anywhere resolves to L0 Section VIII.
    subject = [line for line in files[0].splitlines()
               if re.search(r"Section\s+VIII\s+closes", line)]
    assert len(subject) >= 2, subject
    assert closes[0]["VIII"] == 0, closes[0]["VIII"]
    assert (0, 0, "VIII") not in found, (
        "a sentence about what a section accomplishes is being read as a"
        " pointer at close statements")

    assert not wrong, "sections named as closing what they do not close:\n" + "\n".join(
        wrong)
