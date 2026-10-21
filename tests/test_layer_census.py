"""The census each layer keeps of itself, which asked to be checked and was not.

Every layer ends with a self-kernel: a numbered walk over everything the file
declared, with the closure status of each. `L0_ground.hm` says what it is for
in the section header --- "a census derive. It does not compute --- it
manifests" --- and then says the thing that made this module necessary:

    A future parser/deriver can evaluate this block mechanically against the
    file.

None ever had. The census is a hand-written index of a file kept beside the
file, which is the oldest way a true document goes stale, and its length is
restated in the layer header, in the section header, in the closing block and
again in the Lean file that formalises the layer --- four or five copies of one
number, each maintained by hand.

Three of those copies had drifted, and every one of them drifted alone, with
the correct value standing elsewhere in the same file.

  * `L2_operations.hm` indexed its own section as a "structural census, 29
    steps" eleven lines below `P_2 = 39`, which the file goes on to say twice
    more, and the census has 39 rows.
  * `lean4/Hypermath/L3Ordinatics.lean` opened with `P_3 = 18` and closed its
    own self-kernel section with `P_3 = 20`, which is what the source says and
    what the source has.
  * `L2_operations.hm` step 20 accounted for `plus-and-additionally-distinct`.
    The layer declares `plus-and-additionally-are-distinct`. One word, and the
    row pointed at nothing --- the same defect as the dictionary's three short
    forms, in the file's own index of itself rather than in a document about
    it.

What none of them were was wrong about the mathematics. The census rows are
right, the layer really does declare what they say it declares, and the count
really is what the other three copies say. The artifact just did not have the
29 steps, the 18 steps, or the name.

One asymmetry is recorded rather than repaired. `L0`, `L1` and `L3` carry the
census as a statement of the layer language, `derive Ln-self-kernel as FORM`.
`L2` carries all 39 of its rows inside comments: it indexes the section like
the others and calls it "the closed structural census", and nothing in the
language closes it. Making it a statement would be writing specification
content, which is not this module's to write, so the guard below holds the
line where it is: no further layer may put its census out of the language.
"""

from __future__ import annotations

import re
from pathlib import Path

from test_layer_language import (CARRIES_NO_NAME, INTRODUCES, STATEMENT,
                                 _statements, layer_files)

REPO = Path(__file__).resolve().parents[1]

#: The banner every layer puts over the section. The colon is required: the
#: layer headers also mention the section in prose 550 lines earlier, and a
#: reader that starts there counts every proof step in the file as a census
#: row: 58 of them in `L0`, where the census has 41.
SECTION = re.compile(r"SECTION\s+[IVX]+\s*:\s*L?\d?\s*SELF-KERNEL", re.I)

#: A numbered census row. The `--` is optional because one layer's census is
#: entirely commented, and counting only the uncommented rows would report
#: that layer as having a census of length zero and agree with nothing.
CENSUS_ROW = re.compile(r"^(--\s*)?\s*step\s+(\d+)\s*:")

#: The statement that carries a census in the layer language.
CARRIER = re.compile(r"^derive\s+L(\d)-self-kernel\b")

#: `P_n` is the census length of layer `n`, and it says which layer it is
#: about, so it can be read in any file.
PARAMETER = re.compile(r"\bP_(\d)\s*=\s*(\d+)")

#: The same length written as prose. This one does not say which layer it is
#: about, so it is read only in a file that is about one layer, and only on a
#: line that says it is talking about the census.
IN_PROSE = re.compile(r"\b(\d+)\s+(?:numbered\s+)?steps?\b")
NAMES_A_CENSUS = re.compile(r"self-kernel|structural census", re.I)

#: The layer a file is about: `L2_operations.hm`, `L2Operations.lean`.
FILE_LAYER = re.compile(r"^L(\d)[_A-Z]")

#: The one layer whose census stands in comments rather than in the language.
#: Naming it here is what keeps it from being lost, and the guard is written so
#: that closing the gap leaves it green while opening another one does not.
COMMENTARY = {2}


def layer_index(path: Path) -> int | None:
    found = FILE_LAYER.match(path.name)
    return int(found.group(1)) if found else None


def lean_files() -> list[Path]:
    return [path for path in sorted((REPO / "lean4").rglob("*.lean"))
            if ".lake" not in path.parts]


def censuses() -> dict[int, dict[str, object]]:
    """Each layer's census: where it starts, its rows, and what carries it."""
    found: dict[int, dict[str, object]] = {}
    for path in layer_files():
        index = layer_index(path)
        if index is None:
            continue
        lines = path.read_text(encoding="utf-8").splitlines()
        heads = [number for number, line in enumerate(lines) if SECTION.search(line)]
        if not heads:
            continue
        start = heads[-1]
        rows: list[tuple[int, int, bool]] = []
        # What the census says is what stands in its rows, and a row runs on
        # until the next row or the next statement.  Reading to the end of the
        # file instead would put anything written after the census inside it,
        # which is how this reader first passed a declaration nobody censused.
        body: list[str] = []
        inside = False
        for number, line in enumerate(lines[start:], start):
            if line and line[0] not in " \t-#":
                inside = False
            if row := CENSUS_ROW.match(line):
                rows.append((number, int(row.group(2)), bool(row.group(1))))
                inside = True
            if inside:
                body.append(line)
        carried = any(CARRIER.match(line) for line in lines[start:])
        found[index] = {"path": path, "start": start + 1, "rows": rows,
                        "carried": carried, "text": "\n".join(body)}
    return found


def test_every_stated_census_length_is_the_length_of_the_census() -> None:
    """One number, written out five times by hand, checked against the rows.

    The claim is not that the census is complete or that its rows are right ---
    it is only that a file saying the census is 29 steps long is saying
    something the census settles. Nothing had ever asked it, and two of the
    copies had drifted apart from the other three while every document
    containing them stayed true.
    """
    length = {index: len(record["rows"]) for index, record in censuses().items()}
    assert sorted(length) == [0, 1, 2, 3], sorted(length)
    assert all(count > 15 for count in length.values()), length

    claims: list[tuple[str, int, int, int]] = []
    for path in list(layer_files()) + lean_files():
        relative = path.relative_to(REPO).as_posix()
        here = layer_index(path)
        for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            for found in PARAMETER.finditer(line):
                claims.append((relative, number, int(found.group(1)),
                               int(found.group(2))))
            if here is not None and NAMES_A_CENSUS.search(line):
                for found in IN_PROSE.finditer(line):
                    claims.append((relative, number, here, int(found.group(1))))
    # A reader finding no claims agrees with every census there is.
    assert len(claims) >= 10, claims
    assert len({relative.rsplit(".", 1)[1] for relative, _, _, _ in claims}) == 2, (
        "the Lean side restates these counts too, and is not being read")

    wrong = [f"{relative}:{number}: says P_{index} = {said}, the census has"
             f" {length[index]}"
             for relative, number, index, said in claims
             if index in length and said != length[index]]
    assert not wrong, "census lengths that disagree with the census:\n" + "\n".join(
        wrong)


def test_the_census_accounts_for_every_entity_its_layer_declares() -> None:
    """"Every entity declared in this file is accounted for above." --- `L0`.

    `L0` is the only layer that writes the claim down, and all four keep it.
    Holding the other three to it is not putting words in their mouths: a
    census whose whole content is "here is everything this file declared" makes
    the claim by being one, and a row that names a thing the layer does not
    declare is the same defect from the other side.

    The census derive itself is the one thing left out, uniformly and by all
    three layers that carry one, because a census cannot appear in its own
    walk of what came before it.
    """
    short: list[str] = []
    for index, record in sorted(censuses().items()):
        path = record["path"]
        assert isinstance(path, Path)
        declared: dict[str, tuple[str, int]] = {}
        for number, line in _statements(path):
            head = STATEMENT.match(line)
            if head is None or head.group(1) in CARRIES_NO_NAME:
                continue
            rule = INTRODUCES.get(head.group(1))
            if rule is not None and (found := rule.match(line)):
                declared[found.group(1)] = (head.group(1), number)
        assert len(declared) > 15, (path.name, len(declared))
        text = record["text"]
        assert isinstance(text, str)
        for name, (form, number) in sorted(declared.items(), key=lambda item: item[1][1]):
            if CARRIER.match(f"derive {name} "):
                continue
            if not re.search(r"(?<![A-Za-z0-9-])" + re.escape(name)
                             + r"(?![A-Za-z0-9-])", text):
                short.append(f"{path.name}:{number}: [{form}] {name}")
    assert not short, (
        "declared and missing from the layer's own census:\n" + "\n".join(short))


def test_no_further_layer_demotes_its_census_to_commentary() -> None:
    """A census in comments is a census the language has no record of.

    `L2` indexes its self-kernel as a section like the other three and calls it
    "the closed structural census", and all 39 of its rows are comments: there
    is no `derive L2-self-kernel as FORM` to close, and nothing in the language
    knows the layer censused itself. Whether that should become a statement is
    a question about the specification and not about this suite, so the guard
    asks the smaller question it is entitled to ask --- that no other layer
    goes the same way --- and is written to stay green if `L2` is repaired.
    """
    record = censuses()
    assert sorted(record) == [0, 1, 2, 3], sorted(record)
    commentary = {index for index, one in record.items() if not one["carried"]}
    assert commentary <= COMMENTARY, (
        "a layer's census left the language: " + str(sorted(commentary)))
    for index, one in sorted(record.items()):
        rows = one["rows"]
        assert isinstance(rows, list)
        inside = {commented for _, _, commented in rows}
        assert len(inside) == 1, (
            f"L{index}: the census is half in the language and half in comments,"
            " so neither reading of it is the census")
        assert (index in commentary) == inside.pop(), (
            f"L{index}: carried by a statement and written as comments, or the"
            " reverse")
