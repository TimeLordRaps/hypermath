"""The ledger the layers keep across each other, where FRAME is a promise.

A census row marked FRAME is a forward dependency stated out loud. The layers
are explicit that this is the point --- "FRAME residuals are not failures. They
are honest forward-dependencies: each FRAME names which layer will close it and
what vocabulary is needed. A file with all FRAMEs named is more honest than a
file with hidden gaps" --- and later layers pay them off by citing the row:
`Discharges L1 step 10`, and a closing register at the end of `L3` listing every
FRAME it discharged.

That citation is a pointer into another file's census, written by hand, and
censuses are renumbered when material is inserted into them. Ten of them had
gone stale, in two clean groups.

  * `L1`'s census has 25 rows. `L3` cited `L1 step 26` and `L1 step 30` four
    times each --- both past the end --- and both are off by exactly five. The
    parentheticals say which rows are meant and say it exactly: the deriver
    primitive is step 21, and `D[deriver][deriver]` at `==` is step 25.
  * `L2`'s census grew by eight rows when abstraction was added, which is the
    same growth that left its section index claiming 29 steps. `L3` cited
    `L2 step 24` for `composition-length-additive`, which is step 25, and
    `L2 step 30` for congruent-path internals --- step 30 says in so many words
    that it has no FRAME, and step 37 is the close that carries the internals
    residual.

Nothing was wrong about which obligations exist or which layer paid them. The
rows are right, the discharges happened, and every parenthetical named its
target correctly. Only the numbers pointed elsewhere.

One discrepancy is recorded and not repaired. `definitionOfGround` is cited as
`L0 step 24` in four places --- twice in the Lean sources, once in the changelog
and once in the research note --- and `L0`'s census puts `definition-of-ground`
at step 41, while step 24 is the graduation status and carries no FRAME at all.
The citation is certainly not step 24 as the census numbers it, and nothing
written down says which row it is, so it is left alone: replacing a reference
that visibly points at the wrong thing with one that invisibly does would be
the worse trade. Neither guard below fires on it, and that is deliberate ---
they check what the text determines, which in this case is nothing.

The two guards are scoped differently, and the reason is what each of them
needs to read. Asking whether a row exists needs only the number, so it is
asked of the Lean sources too --- they cite these rows in the layers' own
numbering, eleven times, in one contiguous hand-written run. Asking what a row
is about needs the name, and a Lean source names its own declarations in its
own spelling: `definitionOfGround` cannot be resolved against a census that
spells it `definition-of-ground` without a transliteration this module would
have to invent. So the subject guard reads the layers only.
"""

from __future__ import annotations

import re
from pathlib import Path

from test_layer_census import censuses, layer_index, lean_files
from test_layer_language import (CARRIES_NO_NAME, INTRODUCES, STATEMENT,
                                 _statements, layer_files)

REPO = Path(__file__).resolve().parents[1]

#: A citation of a row in another layer's census.
REFERENCE = re.compile(r"\bL(\d)\s+steps?\s+(\d+)")

#: What a citation says the row is about, when it says anything.
SUBJECT = re.compile(r"\bL(\d)\s+steps?\s+(\d+)\s*\(([^()]{3,80})\)")

#: The other two census parameters. `N_n_atomic` counts the atomic entities the
#: layer introduces and `G_n` the graduation conditions it must discharge; both
#: are restated in the layer header, the section banner, the closing block and
#: the Lean file, exactly as the census length is.
ATOMIC = re.compile(r"\bN_(\d)_atomic\s*=\s*(\d+)\s*(?:\(([^()]*)\))?")
GRADUATION = re.compile(r"\bG_(\d)\b[^=\n]{0,24}=\s*(\d+)")

#: The conditions a graduation block states, named as it names them.
CONDITION = re.compile(r"\bNC-(\d+)\b")


def layer_paths() -> dict[int, Path]:
    return {index: path for path in layer_files()
            if (index := layer_index(path)) is not None}


def census_rows() -> dict[int, dict[int, str]]:
    """Each census row's full text: the row line and what runs on from it."""
    rows: dict[int, dict[int, str]] = {}
    for index, record in censuses().items():
        path = record["path"]
        assert isinstance(path, Path)
        lines = path.read_text(encoding="utf-8").splitlines()
        numbered = record["rows"]
        assert isinstance(numbered, list)
        here: dict[int, str] = {}
        for position, (lineno, step, _) in enumerate(numbered):
            stop = (numbered[position + 1][0] if position + 1 < len(numbered)
                    else lineno + 4)
            here[step] = "\n".join(lines[lineno:stop])
        rows[index] = here
    return rows


def declared_in(index: int) -> set[str]:
    names: set[str] = set()
    for number, line in _statements(layer_paths()[index]):
        head = STATEMENT.match(line)
        if head is None or head.group(1) in CARRIES_NO_NAME:
            continue
        rule = INTRODUCES.get(head.group(1))
        if rule is not None and (found := rule.match(line)):
            names.add(found.group(1))
    return names


def test_every_row_another_layer_cites_is_a_row_that_layer_has() -> None:
    """A forward dependency is paid off by pointing at where it was opened.

    The pointer is into a file that gets renumbered, and six of these pointed
    past the end of the census they named. Being past the end is the part no
    reading can argue with: `L1` has 25 rows, so `L1 step 30` is not a claim
    about a row that is described wrongly, it is a claim about a row.
    """
    rows = census_rows()
    assert sorted(rows) == [0, 1, 2, 3], sorted(rows)
    cited: list[tuple[str, int, int, int]] = []
    for path in list(layer_paths().values()) + lean_files():
        relative = path.relative_to(REPO).as_posix()
        for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            for found in REFERENCE.finditer(line):
                cited.append((relative, number, int(found.group(1)),
                              int(found.group(2))))
    assert len(cited) >= 25, cited
    assert len({index for _, _, index, _ in cited}) >= 3, (
        "only one layer's census is being cited, so the reader has narrowed")
    assert len({relative.rsplit(".", 1)[1] for relative, _, _, _ in cited}) == 2, (
        "the Lean sources cite these rows too, and are not being read")

    missing = [f"{relative}:{number}: cites L{index} step {step}, which has"
               f" {len(rows[index])} rows"
               for relative, number, index, step in cited
               if index in rows and step not in rows[index]]
    assert not missing, "citations of rows no census has:\n" + "\n".join(missing)


def test_a_cited_row_is_about_what_the_citation_says_it_is_about() -> None:
    """Being in range is not being right, and the citation says which row it means.

    `L2 step 24 (composition-length-additive)` names a row that exists and an
    entity that exists, and the row is `finite-path-exists`. That is checkable
    without inferring anything: the parenthetical names a thing the layer
    declares, so the row it points at has to be the row that names it too.

    Only a name the cited layer actually declares counts as a subject here. A
    parenthetical that merely describes --- "deriver ==-cycle", "at == level"
    --- is prose about the row and is not held to appearing in it.
    """
    rows = census_rows()
    checked = 0
    wrong: list[str] = []
    for path in layer_paths().values():
        relative = path.relative_to(REPO).as_posix()
        for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            for found in SUBJECT.finditer(line):
                index, step, said = (int(found.group(1)), int(found.group(2)),
                                     found.group(3))
                if index not in rows or step not in rows[index]:
                    continue                     # the guard above owns this
                subjects = sorted(
                    name for name in declared_in(index)
                    if len(name) > 2 and re.search(
                        r"(?<![A-Za-z0-9-])" + re.escape(name)
                        + r"(?![A-Za-z0-9-])", said))
                if not subjects:
                    continue
                checked += 1
                row = rows[index][step]
                for name in subjects:
                    if not re.search(r"(?<![A-Za-z0-9-])" + re.escape(name)
                                     + r"(?![A-Za-z0-9-])", row):
                        wrong.append(
                            f"{relative}:{number}: says L{index} step {step} is"
                            f" about {name!r}; that row is"
                            f" {' '.join(row.split())[:60]!r}")
    assert checked >= 3, checked
    assert not wrong, "citations naming a row that is about something else:\n" + "\n".join(
        wrong)


def test_the_other_census_parameters_agree_with_the_layers() -> None:
    """`P_n` was one of three, and the other two are kept the same way.

    `N_n_atomic` and `G_n` are restated across the layer files and the Lean
    sources exactly as the census length is, and `G_n` has something to be
    checked against: the graduation block of layer `n` states its conditions by
    name, so counting them settles it. Where a parenthesised list follows the
    number, the list settles it too.
    """
    conditions: dict[int, int] = {}
    for index, path in sorted(layer_paths().items()):
        lines = path.read_text(encoding="utf-8").splitlines()
        for number, line in enumerate(lines):
            if not line.startswith("graduation"):
                continue
            block: list[str] = []
            for follow in lines[number + 1:]:
                if follow and follow[0] not in " \t-#":
                    break
                block.append(follow)
            conditions[index] = len(set(CONDITION.findall("\n".join(block))))
    assert sorted(conditions) == [0, 1, 2, 3], sorted(conditions)

    atomic: dict[int, set[int]] = {}
    wrong: list[str] = []
    seen = 0
    for path in list(layer_files()) + lean_files():
        relative = path.relative_to(REPO).as_posix()
        for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            for found in ATOMIC.finditer(line):
                index, said, listed = (int(found.group(1)), int(found.group(2)),
                                       found.group(3))
                atomic.setdefault(index, set()).add(said)
                seen += 1
                if listed and all(
                        re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'-]*", part.strip())
                        for part in listed.split(",") if part.strip()):
                    items = [part for part in listed.split(",") if part.strip()]
                    if len(items) != said:
                        wrong.append(f"{relative}:{number}: N_{index}_atomic ="
                                     f" {said}, lists {len(items)}")
            for found in GRADUATION.finditer(line):
                index, said = int(found.group(1)), int(found.group(2))
                seen += 1
                if index in conditions and said != conditions[index]:
                    wrong.append(f"{relative}:{number}: G_{index} = {said}, and"
                                 f" the graduation of L{index} states"
                                 f" {conditions[index]} conditions")
    assert seen >= 20, seen
    assert len(atomic) == 4, sorted(atomic)
    split = {index: sorted(values) for index, values in atomic.items()
             if len(values) > 1}
    assert not split, "N_n_atomic stated two ways: " + str(split)
    assert not wrong, "census parameters that disagree:\n" + "\n".join(wrong)
