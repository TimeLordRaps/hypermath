"""The boundary each layer declares about itself, in its own eleventh line.

All four say it, in almost the same words:

    Layer boundary: no term from L1 or above appears anywhere in this file.
    Layer boundary: no terms from L2 (operations) or above appear here.
    Layer boundary: no term from L3 (ordinatics) or above appears here.
    Layer boundary: terminal layer. No layer above.

It is the strongest self-denying claim in the stack --- the stratification the
whole design rests on, asserted by each layer about the entirety of its own
text --- and nothing read it. Not the audit, not the census guards, not the
grant-and-copy guards that read the very blocks where it is broken.

It is kept. One hundred and thirty-six names are declared by some layer above
some other layer, and across all four files not one of them stands in a
statement of a layer below. The boundary is real and the stratification holds
exactly as advertised.

The sentence is not kept. Seventeen of those names appear in comments, and what
makes this worth an increment is *which* seventeen. They stand in ten comment
blocks, and every block does at least one of four things: four forbid, one
grants, six defer, four locate. That is more than ten because a block that
defers a term usually forbids it in the same breath, until the layer that owns
it arrives. L1 tells L2 it "may NOT introduce ordinal_limit"; L2's graduation
block grants L3 `ordinal_succ`; L0 warns that a derive in L1 requiring
`ordinal_limit` is over-reaching. A prohibition has to name what it prohibits.
A grant has to name what it grants. A deferral has to name what is deferred.

So the claim, read as written, is refuted entirely by the machinery that
enforces it --- and by nothing else. There is no use anywhere, only the
sentences that prevent one. The three non-terminal claims are repaired to say
what the files do: no term from above in any *statement*. The part of the claim
that made it worth asserting, that the comments naming those terms are bounding
them rather than using them, is not left to a sentence; it is held below.

L3's claim is terminal and unfalsifiable --- there is no layer above it, so
nothing can violate it --- and that is recorded rather than counted as held.

One collision has to be classified out loud or this measures nothing. L2
declares `step` as a primitive, and L0 and L1 both write `step 25:` for every
row of their own censuses and "each step is a strengthen-of" in prose. One
hundred and seventy-five of those, against seventeen real mentions. A guard that
took the spelling for the primitive would report the two lower layers as
massively in breach of a boundary they keep perfectly, so `step` is named in
`AMBIGUOUS` with the reason, and the control is run below rather than described.

Before anything read it, the count of mentions was written seven times in this
file: three times in this docstring, twice in the comments beside the tables,
and once in each of two guards below. Every one of the seven said sixteen. It
had been seventeen since the mention nothing had read was found, and a floor of
sixteen admitted every copy. The numbers in this docstring are now held by the
guards, which is what `_states` is for, and a count that cannot be held ---
because it stands in a comment rather than a docstring --- is not written.
"""

from __future__ import annotations

import re
from itertools import permutations

from _docstring_counts import _states
from test_layer_ledger import layer_paths

#: What a layer declares, by the keyword that introduces it.
DECLARES = re.compile(
    r"^(primitive|opaque|relation|derive|axiom|close|discharge)\s+"
    r"([A-Za-z_'+~=][^\s:(]*)")

#: The claim itself, which every one of the four states in its header.
CLAIM = re.compile(r"^--\s*Layer boundary:\s*(\S.*?)\s*$")

#: Which layer a claim names as the floor of "or above".
FLOOR = re.compile(r"from\s+L(\d)\b")

#: A spelling shared by a declared name and something else entirely. `step` is
#: an L2 primitive and also the word L0 and L1 use for every row of their own
#: censuses. Reading the spelling for the primitive reports the two layers that
#: keep the boundary best as the two that break it most. The module docstring
#: gives both counts and the first guard below runs the control that produces
#: them; a comment is not a docstring, so no number is repeated here.
AMBIGUOUS = {"step"}

#: The layer whose boundary claim cannot be violated, having nothing above it.
TERMINAL = {3}

#: What a comment does when it names a term from above. Every mention does at
#: least one of these; none of them uses the term.
BOUNDING = {
    "forbids": re.compile(r"may\s+NOT|prohibit|over-reaching"
                          r"|belongs?\s+to\s+L\d", re.I),
    "grants": re.compile(r"graduation\s+permits|permits\s+L\d", re.I),
    "defers": re.compile(r"\bFRAME\b|\[deferred\]|awaits|pending"),
    "locates": re.compile(r"L\d\s*\([A-Z][a-z]+\)\s+introduces"
                          r"|L\d\s+(?:will|uses)\b|NC-\d"),
}


def declarations(index: int) -> dict[str, str]:
    """Every name a layer declares, by the keyword that declares it."""
    found: dict[str, str] = {}
    for line in layer_paths()[index].read_text(encoding="utf-8").splitlines():
        hit = DECLARES.match(line)
        if hit:
            found.setdefault(hit.group(2).strip("'\""), hit.group(1))
    return found


def occurrences(ambiguous: set[str] | None = None) -> tuple[list[tuple],
                                                            list[tuple], int]:
    """Where a term declared above a layer turns up inside it.

    A term "from above" is one some higher layer declares and this one does
    not: a name both declare is this layer's own vocabulary too, whatever the
    layer above does with it. Returns the occurrences in statements, those in
    comments, and how many names were considered.

    The set of ambiguous spellings is a parameter so that the control can be
    run rather than described. `AMBIGUOUS` carries one name and the reason it
    is there, and a reason is a claim: passing the empty set is what makes it
    one this repository checks.
    """
    ambiguous = AMBIGUOUS if ambiguous is None else ambiguous
    declared = {index: declarations(index) for index in sorted(layer_paths())}
    statements, comments, considered = [], [], 0
    for lower in sorted(layer_paths()):
        above: dict[str, tuple[int, str]] = {}
        for upper in sorted(layer_paths()):
            if upper <= lower:
                continue
            for name, kind in declared[upper].items():
                if (name not in declared[lower] and len(name) >= 4
                        and name not in ambiguous):
                    above.setdefault(name, (upper, kind))
        considered += len(above)
        lines = layer_paths()[lower].read_text(encoding="utf-8").splitlines()
        for name, (upper, kind) in sorted(above.items()):
            spelling = re.compile(r"(?<![A-Za-z0-9_'-])" + re.escape(name)
                                  + r"(?![A-Za-z0-9_-])")
            for number, line in enumerate(lines, 1):
                if not spelling.search(line):
                    continue
                row = (lower, number, upper, kind, name, line.strip())
                (comments if line.lstrip().startswith("--")
                 else statements).append(row)
    return statements, comments, considered


def paragraph(index: int, number: int) -> str:
    """The run of comment lines a comment line stands in, and its anchors.

    A clause is bounded by the block it sits in and not by its own words: the
    line reading "The filtration chain is an ordering, not a simultaneity"
    names an L1 axiom and says nothing about permission, three lines under the
    "L1 may NOT define ==" it is explaining.

    The run is taken with the statement on each side of it, because a comment
    run is very often the body of the statement above it and that statement is
    what says what the run is doing. The five clauses of L2's grant to L3 are
    comments; the word `permits` is on the line above them, and it is not a
    comment. A reader stopping at the run reports those five as naming L3's
    terms for no reason anyone can see.
    """
    lines = layer_paths()[index].read_text(encoding="utf-8").splitlines()
    start = end = number - 1
    while start > 0 and lines[start - 1].lstrip().startswith("--"):
        start -= 1
    while end + 1 < len(lines) and lines[end + 1].lstrip().startswith("--"):
        end += 1
    return "\n".join(lines[max(0, start - 1):end + 2])


def test_no_layer_uses_a_term_the_layers_above_it_declare() -> None:
    """The stratification the whole design rests on, held for the first time.

    Every layer asserts it about itself and nothing had ever read the assertion
    --- including the guards that read, clause by clause, the very blocks where
    the terms from above are named.

    The two floors this opened with are gone. Each stood under a number the
    module docstring also spelled, which is one measurement written twice with
    only the weaker copy checked; the docstring is now held exactly, and an
    exact statement leaves a floor beneath it nothing to say.
    """
    statements, comments, considered = occurrences()

    _states(__doc__, r"It is kept\. (One hundred and [a-z-]+) names are"
                     r" declared", considered)
    _states(__doc__, r"([A-Za-z]+) of those names appear in comments", len(comments))
    _states(__doc__, r"worth an increment is \*which\* ([a-z]+)", len(comments))

    # `AMBIGUOUS` says a spelling collides and the module docstring says what
    # the collision would cost. Both are claims, and running the reader without
    # the table is what makes them ones this repository checks rather than
    # describes.
    wide_statements, wide_comments, wide_considered = occurrences(set())
    collisions = [row for row in wide_statements + wide_comments
                  if row[4] in AMBIGUOUS]
    _states(__doc__, r"(One hundred and [a-z-]+) of those, against ([a-z]+)"
                     r" real mentions", len(collisions), len(comments))
    assert wide_considered > considered, (
        "dropping the ambiguity table considers no more names, so `step` is"
        " no longer declared above a layer that writes it and the table is"
        " describing a collision that has gone")

    assert len({row[4] for row in comments}) >= 5, (
        "too few distinct terms found for the reader to be doing anything")
    assert len({row[0] for row in comments}) >= 3, (
        "one layer is being read, so the reader has narrowed to it")

    assert not statements, (
        "terms from above, standing in statements of a layer below:\n"
        + "\n".join(f"L{lower}:{number}: L{upper} {kind} {name!r} — {text[:60]}"
                    for lower, number, upper, kind, name, text in statements))


def test_a_term_from_above_is_named_only_to_bound_it() -> None:
    """Seventeen mentions, and every one of them is the boundary working.

    This is what makes the repair of the claim's wording honest rather than a
    weakening. The strong reading --- nothing from above anywhere --- is false,
    and the reason it is false is that a prohibition has to name what it
    prohibits. What the strong reading was reaching for is true and is held
    here: a term from above is named to forbid it, to grant it, to defer to it,
    or to say which layer owns it, and never to use it.

    That the four categories *distinguish* was held as "no one category covers
    every mention", which is a count standing where a partition is the subject.
    It passed with nine mentions to spare, and it would have gone on passing if
    two categories had come to take exactly the same mentions and say one thing
    twice, or if one had become a strictly coarser reading of another. What is
    held instead is that no two take the same mentions and none takes a subset
    of another. That implies the bound it replaces: no category is empty, so
    one covering every mention would contain every other.
    """
    _, comments, _ = occurrences()

    kinds: dict[str, int] = {name: 0 for name in BOUNDING}
    taken: dict[str, set[tuple[int, int]]] = {name: set() for name in BOUNDING}
    blocks: dict[tuple[int, str], list[str]] = {}
    loose = []
    for lower, number, _upper, _kind, name, text in comments:
        block = paragraph(lower, number)
        matched = [label for label, marker in BOUNDING.items()
                   if marker.search(block)]
        for label in matched:
            kinds[label] += 1
            taken[label].add((lower, number))
        blocks.setdefault((lower, block), []).append(name)
        if not matched:
            loose.append(f"L{lower}:{number}: names {name!r} and the comment"
                         f" it stands in neither forbids, grants, defers nor"
                         f" locates it — {text[:60]}")

    empty = sorted(label for label, count in kinds.items() if not count)
    assert not empty, f"no mention is classified as {empty}, so the category is dead"

    shadowed = [f"{inner} takes only mentions {outer} takes, so it reads"
                f" nothing {outer} does not: {sorted(taken[inner])}"
                for inner, outer in permutations(sorted(taken), 2)
                if taken[inner] <= taken[outer]]
    assert not shadowed, ("categories that distinguish nothing:\n"
                          + "\n".join(shadowed))

    per_block = {label: sum(1 for _, block in blocks
                            if BOUNDING[label].search(block))
                 for label in BOUNDING}
    doc = test_a_term_from_above_is_named_only_to_bound_it.__doc__
    _states(doc, r"^([A-Za-z]+) mentions, and every one", len(comments))
    _states(doc, r"That the ([a-z]+) categories \*distinguish\*", len(BOUNDING))
    _states(doc, r"passed with ([a-z-]+) mentions to spare",
            len(comments) - max(kinds.values()))
    _states(__doc__, r"They stand in ([a-z]+) comment blocks", len(blocks))
    _states(__doc__, r"at least one of ([a-z]+) things: ([a-z]+) forbid,"
                     r" ([a-z]+) grants, ([a-z]+) defer, ([a-z]+) locate",
            len(BOUNDING), per_block["forbids"], per_block["grants"],
            per_block["defers"], per_block["locates"])

    assert not loose, "terms from above named outside any bounding sentence:\n" + "\n".join(
        loose)


def test_every_layer_states_its_boundary_and_states_the_one_it_keeps() -> None:
    """Four claims, one per layer, and three of them said more than is true.

    The scope is the whole of the repair. "Appears anywhere in this file" is
    refuted seventeen times over by the file's own grant blocks; "appears in any
    statement of this file" is what the four files actually do, and what the
    two guards above hold them to.
    """
    doc = test_every_layer_states_its_boundary_and_states_the_one_it_keeps.__doc__
    _states(doc, r"refuted ([a-z]+) times over", len(occurrences()[1]))

    claims = {}
    for index in sorted(layer_paths()):
        found = [(number, hit.group(1)) for number, line in
                 enumerate(layer_paths()[index].read_text(encoding="utf-8")
                           .splitlines(), 1)
                 if (hit := CLAIM.match(line))]
        assert len(found) == 1, (f"L{index} states its layer boundary"
                                 f" {len(found)} times: {found}")
        claims[index] = found[0][1]

    assert set(claims) == set(layer_paths()), sorted(claims)
    wrong = []
    for index, text in sorted(claims.items()):
        if index in TERMINAL:
            assert "terminal" in text.lower(), (index, text)
            assert not FLOOR.search(text), (
                f"L{index} has nothing above it and names a floor: {text}")
            continue
        floor = FLOOR.search(text)
        if not floor:
            wrong.append(f"L{index}: states a boundary naming no layer"
                         f" — {text}")
        elif int(floor.group(1)) != index + 1:
            wrong.append(f"L{index}: its boundary starts at L{floor.group(1)},"
                         f" and the layer above it is L{index + 1}")
        if "statement" not in text:
            wrong.append(f"L{index}: claims a scope its own comments break"
                         f" — {text}")

    assert len(claims) - len(TERMINAL) >= 3, sorted(claims)
    assert not wrong, "boundaries claimed otherwise than they are kept:\n" + "\n".join(
        wrong)
