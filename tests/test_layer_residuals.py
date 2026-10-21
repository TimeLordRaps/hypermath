"""The other side of the ledger: the promises, and the claim that they are all.

Increment 38 held the paying side --- a discharge must point at a row that
exists, and at the row it says it does. The opening side is a layer's own
inventory of what it leaves undone, and it does not merely list: it closes with
a claim about itself.

    No entity unaccounted.  No FRAME hidden.

That is a claim of exhaustiveness, which is the hardest kind to keep by hand,
because nothing goes wrong when an item is left out. Every sentence in the
inventory stays true; the list is simply not all of them.

`L1_relations.hm` opens four residuals --- steps 10, 21, 22 and 25 --- and its
inventory names three. The missing one is step 22, `opaque(D)`, whose row reads
`FORM (schema). FRAME/L3 (content)`, the same shape `L2` uses at step 6 for
`compose` and step 7 for `congruent-path`, both of which are listed in their
layer's inventory and one of which `L3` discharges by name. Step 22 appears in
no inventory and in no discharge register, at either end.

It is left unrepaired, and the reason is that the repair is not determined.
Everything else in the stack says D belongs to L1: the declaration gives its
reading in full --- a trace-sequence from x to y maintained at `=~` or above
--- and marks it `orbital: L1`; `L1`'s inventory says so twice, in the header
and in the closing block; `L3` says in so many words that the matrix is defined
at L1, and its register neither discharges the residual nor lists it as
remaining. Four places say L1 and one census row says FRAME/L3. Adding it to
the inventory would assert a residual four other places deny, and clearing the
row would assert a closure nothing states. Which of the five is wrong is a
question about the specification, so the gap is recorded here instead, held so
that no second one can open without the suite saying so.

Only `L1` keeps an inventory that cites its own rows by number, and that is why
it is the only layer whose completeness is measured below. `L0` documents its
eight residuals as two descriptions, `L2` as five, and a description covers as
many rows as it covers --- matching one to the other is a reading and not a
measurement, and a reader that guessed would be wrong in both directions at
once. What the survey found by hand, and what is recorded rather than guarded:
`L2`'s inventory of five omits `path-trace` (step 5) and the `compose`
internals (step 6) among the seven rows it opens, and `L3` accounts for the
first in its non-blocking residuals and for the second only through the length
law that `composition-length-additive` asks for.
"""

from __future__ import annotations

import re
from pathlib import Path

from test_layer_census import CENSUS_ROW
from test_layer_ledger import census_rows, layer_paths

REPO = Path(__file__).resolve().parents[1]

#: A row that opens a residual names the layer that will close it. A bare
#: `FRAME` without a target is the word the files use to talk about them.
OPENS = re.compile(r"\bFRAME\s*/\s*L(\d\+?)")

#: Paying a residual off is written about in the same words as opening one:
#: `L3` step 16 quotes the `L1` row it closes, target and all. Only the verb
#: counts as payment --- `discharge` is also a declared name and a statement
#: form, and matching those would lose six of `L0`'s eight.
PAYS = re.compile(r"\bDischarges\b")

#: A row may also say it has none, and three do: "No FRAME internal",
#: "compose respects ~= with no FRAME", "Opens no FRAME and discharges none."
#: Not one of them names a target layer, so requiring a target already excludes
#: them, and filtering on the denial as well would be a reader handling a case
#: that does not occur. What is held instead is that the two never meet on one
#: line --- because the day they do, requiring a target reads a denial as a
#: promise, and the reader would be wrong in the quiet direction.
DENIES = re.compile(r"\bno FRAME\b", re.I)

#: The heading a layer puts over its own inventory. The colon has to follow the
#: word, because `L2` labels three census rows "FRAME residuals at L2:" and a
#: reader that started there would read those rows' own numbers as an inventory
#: of them --- and `L3` closes with "FRAME residuals remaining:", which is the
#: other list entirely, of what was never opened rather than what was.
INVENTORY = re.compile(r"\bFRAME residuals:")

#: A reference to a row of the census in the file making it. Increment 38 reads
#: the prefixed form, `L1 step 10`; inside `L1_relations.hm` the same row is
#: cited as `step 10`, because the file is already talking about itself.
BARE = re.compile(r"(?<![A-Za-z0-9_])steps?\s+(\d+)((?:\s*(?:,|and)\s*\d+)*)")
CONTINUED = re.compile(r"(\d+)")

#: Another layer's row, which this module does not own. The window has to allow
#: words in between: `L1_relations.hm` cites "L0 self-kernel step 40", and a
#: stricter reader takes that for a claim about L1's own twenty-five rows.
PREFIXED = re.compile(r"\bL(\d)\b[^.\n]{0,28}?\bsteps?\s+\d+")

#: The one residual its layer opens and its layer's inventory does not name.
#: Written down here because the repair is not determined and a finding that
#: lives only in a note is a finding that rots. Repairing it --- from either
#: end --- leaves this guard green; a second one does not.
UNLISTED = {(1, 22)}


def opened_residuals() -> dict[int, dict[int, str]]:
    """Per layer, the census rows that open a residual, and what they say."""
    found: dict[int, dict[int, str]] = {}
    for index, rows in sorted(census_rows().items()):
        here: dict[int, str] = {}
        for step, body in sorted(rows.items()):
            for line in body.splitlines():
                if OPENS.search(line) and not PAYS.search(line):
                    here[step] = " ".join(body.split())[:90]
                    break
        found[index] = here
    return found


def inventories() -> dict[int, tuple[list[str], set[int]]]:
    """Per layer, its closing inventory and the rows that inventory cites."""
    found: dict[int, tuple[list[str], set[int]]] = {}
    for index, path in sorted(layer_paths().items()):
        text = path.read_text(encoding="utf-8")
        heads = [match.start() for match in INVENTORY.finditer(text)]
        if not heads:
            continue
        block: list[str] = []
        for line in text[heads[-1]:].split("\n")[1:]:
            if not line.strip().startswith("--"):
                break
            block.append(line.strip())
        cited: set[int] = set()
        for line in block:
            for found_one in BARE.finditer(line):
                cited.add(int(found_one.group(1)))
                cited.update(int(more) for more
                             in CONTINUED.findall(found_one.group(2) or ""))
        found[index] = (block, cited)
    return found


def test_a_layer_naming_one_of_its_own_rows_names_a_row_it_has() -> None:
    """A citation with no prefix is still a citation, and nothing read them.

    Thirty-six of them stand in the layer files, and the cross-layer reader
    cannot see one: it is looking for `L1 step 10` and the file, already
    talking about itself, writes `step 10`. Being in range is the whole of what
    is checked here, and it is the part that a renumbering breaks first.
    """
    rows = census_rows()
    assert sorted(rows) == [0, 1, 2, 3], sorted(rows)
    seen: list[tuple[int, int, int]] = []
    wrong: list[str] = []
    for index, path in sorted(layer_paths().items()):
        length = len(rows[index])
        for number, line in enumerate(
                path.read_text(encoding="utf-8").splitlines(), 1):
            if CENSUS_ROW.match(line):
                continue                 # a row numbering itself is the census
            clean = PREFIXED.sub(" ", line)
            for found in BARE.finditer(clean):
                steps = [int(found.group(1))]
                steps += [int(more) for more
                          in CONTINUED.findall(found.group(2) or "")]
                for step in steps:
                    seen.append((index, number, step))
                    if not 1 <= step <= length:
                        wrong.append(
                            f"{path.name}:{number}: names step {step}, and the"
                            f" census has {length} rows"
                            f" | {' '.join(line.split())[:60]}")
    assert len(seen) >= 25, seen
    assert len({index for index, _, _ in seen}) >= 3, (
        "only one layer is being read, so the reader has narrowed")
    assert not wrong, "rows a layer names itself and does not have:\n" + "\n".join(
        wrong)


def test_an_inventory_cites_only_rows_that_open_a_residual() -> None:
    """The inventory is a list of residuals, so its members must be residuals.

    This is the soundness half, and it is the half a renumbering breaks in the
    direction that can be seen: an inventory pointing at a row that opens
    nothing is claiming a promise the layer never made.
    """
    opened = opened_residuals()
    assert sorted(opened) == [0, 1, 2, 3], sorted(opened)
    assert sum(len(here) for here in opened.values()) >= 15, opened
    for index in (0, 1, 2):
        assert opened[index], f"L{index} opens no residual at all"

    # A row set aside as payment has to name what it pays. Without this, a
    # reader that matched `discharge` rather than `Discharges` would drop six
    # of L0's eight residuals -- `syntax(discharge)` declares a name and
    # `discharge(derives-is-directional, FRAME)` is a statement form, and
    # neither pays anything -- and every count above would still hold.
    unpaid: list[str] = []
    for index, rows in sorted(census_rows().items()):
        for step, body in sorted(rows.items()):
            for line in body.splitlines():
                if not (OPENS.search(line) and PAYS.search(line)):
                    continue
                if not re.search(r"\bL\d\b[^.\n]{0,28}?\bsteps?\s+\d+"
                                 r"|\bL\d\s+FRAME\b", line):
                    unpaid.append(f"L{index} step {step}: set aside as payment"
                                  f" and names no row | {line.strip()[:64]}")
    assert not unpaid, "rows dropped as discharges that discharge nothing:\n" + "\n".join(
        unpaid)

    # And the denials stay where requiring a target can see past them.
    denials: list[str] = []
    collided: list[str] = []
    for index, rows in sorted(census_rows().items()):
        for step, body in sorted(rows.items()):
            for line in body.splitlines():
                if not DENIES.search(line):
                    continue
                denials.append(f"L{index} step {step}")
                if OPENS.search(line):
                    collided.append(f"L{index} step {step}:"
                                    f" {line.strip()[:64]}")
    assert len(denials) >= 3, denials
    assert not collided, (
        "a line says it has no residual and names a layer to close one, so the"
        " denial reads as a promise:\n" + "\n".join(collided))

    numbered = {index: cited for index, (_, cited) in inventories().items()
                if cited}
    assert numbered, "no inventory cites a row, so nothing here is measured"
    wrong: list[str] = []
    for index, cited in sorted(numbered.items()):
        for step in sorted(cited - set(opened[index])):
            wrong.append(f"L{index}: the inventory names step {step}, which"
                         " opens no residual")
    assert not wrong, "inventory entries that are not residuals:\n" + "\n".join(
        wrong)


def test_no_further_residual_goes_unlisted_by_the_layer_that_opens_it() -> None:
    """"No FRAME hidden," says `L1`, with one of its four not in the list.

    The completeness half, asked only where it can be asked: of an inventory
    that cites rows by number. The one gap that exists is named in `UNLISTED`
    rather than described, so that repairing it from either end is a one-line
    change here and a second gap is not.

    This opened by asserting that an inventory is no longer than the residuals
    it lists, written `len(opened[index]) > len(cited) - 1`. The guard above
    already holds every cited row to be a row that opens a residual, so the
    inventory is a subset of the residuals and the count follows from it: the
    bound could not fail while the guard above passed. What stands in its place
    is the one thing an exemption list can get wrong on its own --- an entry
    whose gap has since been closed, subtracted forever from a set that no
    longer contains it.
    """
    opened = opened_residuals()
    numbered = {index: cited for index, (_, cited) in inventories().items()
                if cited}
    assert numbered, "no inventory cites a row, so completeness is unmeasured"

    missing = {(index, step) for index, cited in numbered.items()
               for step in set(opened[index]) - cited}
    extra = sorted(missing - UNLISTED)
    assert not extra, (
        "residuals a layer opens and its own inventory does not name: "
        + str([(f"L{index}", step, opened[index][step]) for index, step in extra]))

    # The recorded gap has to stay a real row of a real census, or the record
    # rots into a pair of numbers that mean nothing.
    rows = census_rows()
    for index, step in sorted(UNLISTED):
        assert index in rows and step in rows[index], (
            f"L{index} step {step} is recorded as unlisted and is not a row")

    # And it has to stay unlisted. `UNLISTED` is subtracted from what this
    # finds, so an entry whose gap has been closed goes on being subtracted
    # from nothing: the guard stays green while the record says a layer hides a
    # residual it now names. An exemption that outlives the thing it exempts is
    # a claim this repository does not have.
    closed = sorted(UNLISTED - missing)
    assert not closed, (
        "recorded as unlisted by the layer that opens it, and now listed by"
        " it, so the record is stale: "
        + str([(f"L{index}", step) for index, step in closed]))
