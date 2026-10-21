"""Check Hypermath's adjacent-repository register against the family census.

`AGENTS.md` section 1.1 is a hand-written, counted register of the repositories
most relevant to this tree. `docs/family/family-graph.json` is a generated
census of the wider family at published default-branch coordinates. A register
entry must either resolve to a graph node or explain why it does not; the
register is not an exhaustive list of graph nodes. The graph's digest and
kind-specific edge totals are checked independently.

Local documents can cite a sibling before that citation reaches the published
default branch used by the graph. Such a gap is pinned explicitly below. A
foreign citation is exempt from local resolution only when its paragraph names
the tree that holds it, or anchors the precursor to a local Git commit.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
GRAPH = REPO / "docs" / "family" / "family-graph.json"
REGISTER = REPO / "AGENTS.md"

#: Trees whose documents this repository did not write, plus build and tool
#: output. A citation inside one of them is not a claim this project makes.
NOT_OURS = {".git", ".venv", "build", "node_modules", "references", ".lake",
            "archive", "site-packages"}

#: The register's own heading, and where it stops.
HEADING = "### 1.1 Ecosystem Ancestry and Adjacent Repositories"
NEXT_HEADING = re.compile(r"^#{1,4}\s")

#: The counted sentence: everything from "alongside" to the colon that opens
#: the list. The count is the number words inside it, added up.
COUNTED_RUN = re.compile(r"\balongside\s+(.+?):\s*$", re.S | re.M)
NUMBER_WORD = {"one": 1, "two": 2, "three": 3, "four": 4, "five": 5,
               "six": 6, "seven": 7, "eight": 8, "nine": 9, "ten": 10}
NUMBER = re.compile(r"(?<![A-Za-z])(" + "|".join(NUMBER_WORD) + r")(?![A-Za-z])")

#: A register entry: its position, the repository it names, and the coordinate
#: it gives for it. The two spellings have to agree or the entry points
#: somewhere other than where it says.
ENTRY = re.compile(r"^(\d+)\.\s+\*\*`([a-z0-9-]+)`\*\*\s+"
                   r"\(`([A-Za-z][A-Za-z0-9_-]*)/([a-z0-9-]+)`\)", re.M)

#: How an entry says it is deliberately absent from the generated graph.
NOT_A_NODE = re.compile(r"not a node of `docs/family/family-graph\.json`")

#: A list item. What a sentence about another tree governs is the item it
#: stands in, not every bullet that happens to share its blank-line block.
ITEM = re.compile(r"^\s*(?:[-*+]|\d+\.)\s")

#: The precursor is not a repository and has no node. It is anchored instead by
#: the commit it forked from, which this repository does have.
PRECURSOR = re.compile(r"precursor tree\b[^.]*?forked from this repository at"
                       r"\s+`([0-9a-f]{7,40})`(?:\s+on\s+(\d{4}-\d{2}-\d{2}))?")

#: A tree named as *holding* something, rather than merely mentioned. This
#: distinction is the whole reader. `ordinatics` is a sibling repository and
#: also this repository's own vocabulary --- a clause name, an axiom, a layer
#: file --- so hundreds of paragraphs here contain the word while being about
#: nothing but this tree. Attributing those excused seven hundred names. What
#: attributes a citation is a tree said to carry, ship or declare a thing.
HOLDS = re.compile(r"\b(?:carries|carry|ships|declares|holds|contains"
                   r"|provides|exists\s+in|lives\s+in)\b")

#: Citations in local documents absent from the graph generated from published
#: default branches. Pin the gap so another omission is not silent. Regenerate
#: after these documents reach the default branch; do not hand-edit the graph.
UNGRAPHED_CITATIONS = {
    "hyperethics": "the local README now links to the foundations reader's"
                   " map before that citation reaches the published default branch",
    "hyperlogic": "cited on this local branch by P0_STATUS.md and AGENTS.md;"
                  " the graph reads the published default branch",
}


def documents() -> list[Path]:
    """Every markdown document this repository wrote."""
    return [path for path in sorted(REPO.rglob("*.md"))
            if not NOT_OURS & set(path.parts)]


def graph() -> dict:
    return json.loads(GRAPH.read_text(encoding="utf-8"))


def register() -> list[str]:
    """Section 1.1 of AGENTS.md, as lines."""
    lines = REGISTER.read_text(encoding="utf-8").splitlines()
    start = next(number for number, line in enumerate(lines)
                 if line.strip() == HEADING)
    kept = []
    for line in lines[start + 1:]:
        if NEXT_HEADING.match(line):
            break
        kept.append(line)
    return kept


def entries() -> list[tuple[int, str, str, str]]:
    """The register's numbered entries, read from the joined block.

    Joined, because an entry's sentence wraps and the coordinate can land on
    the line after the name.
    """
    block = "\n".join(register())
    return [(int(hit.group(1)), hit.group(2), hit.group(3), hit.group(4))
            for hit in ENTRY.finditer(block)]


def entry_text(block: str, name: str) -> str:
    """One register entry's own lines, from its number to the next one.

    Read per entry rather than over the whole section, so that a sentence
    explaining one repository's absence cannot excuse another's.
    """
    lines = block.splitlines()
    starts = [number for number, line in enumerate(lines) if ENTRY.match(line)]
    for index, number in enumerate(starts):
        if ENTRY.match(lines[number]).group(2) == name:
            stop = starts[index + 1] if index + 1 < len(starts) else len(lines)
            return "\n".join(lines[number:stop])
    return ""


def paragraphs(path: Path) -> list[tuple[int, str]]:
    """The unit a sentence about another tree governs: an item, not a block.

    Blank lines are the wrong boundary here and the difference is not small. A
    bullet list has no blank lines inside it, so a changelog's entire list is
    one block; one bullet saying "hyperlogic carries a file" then attributed
    four hundred and thirty-six names from hundreds of unrelated bullets, and
    among them quietly excused a path that is pinned elsewhere as deliberately
    absent. A list item is its own paragraph, and that is the unit.
    """
    found = []
    for start, block in blocks(path):
        lines = block.splitlines()
        cuts = [index for index, line in enumerate(lines) if ITEM.match(line)]
        if not cuts:
            found.append((start, block))
            continue
        edges = sorted({0, *cuts, len(lines)})
        for first, last in zip(edges, edges[1:]):
            piece = "\n".join(lines[first:last])
            if piece.strip():
                found.append((start + first, piece))
    return found


def blocks(path: Path) -> list[tuple[int, str]]:
    """Blank-line separated runs, with the line each one starts on."""
    found, start, buffer = [], 1, []
    for number, line in enumerate(path.read_text(encoding="utf-8")
                                  .splitlines(), 1):
        if line.strip():
            if not buffer:
                start = number
            buffer.append(line)
        elif buffer:
            found.append((start, "\n".join(buffer)))
            buffer = []
    if buffer:
        found.append((start, "\n".join(buffer)))
    return found


def foreign_trees() -> set[str]:
    """Every tree this repository has an account of, other than itself.

    A paragraph cannot attribute a citation to a tree the repository has never
    heard of. The two accounts are the graph's nodes and the register's
    entries, so inventing a sibling in prose is caught rather than believed.
    """
    names = {node["id"] for node in graph()["nodes"]}
    names |= {name for _, name, _, _ in entries()}
    return names - {"hypermath"}


def foreign_citations() -> dict[str, tuple[str, str, int]]:
    """Names and paths this repository's documents attribute to another tree.

    Read out of the documents, in the shape `retired_layer_names` uses: the
    exemption is a sentence the artifact contains, not an entry in a test. A
    paragraph that says which tree holds a thing is a paragraph whose
    code-style names are that tree's names, and `test_layer_language` and
    `test_declared_counts` both consult this instead of reporting them absent.

    A name is attributed to every tree its paragraph names, not to one of them.
    The reader does not parse which clause a name belongs to, so a sentence
    saying that one tree declares this and another carries that attributes both
    names to both trees. That is a real limit and it is recorded here rather
    than hidden behind a first-wins pick: what is held is that the right tree
    is among them, never that it is the only one.
    """
    trees = foreign_trees()
    found: dict[str, list[tuple[str, str, int]]] = {}
    for path in documents():
        relative = path.relative_to(REPO).as_posix()
        for number, block in paragraphs(path):
            named = held_by(block, trees)
            if PRECURSOR.search(block):
                named.append("the precursor tree")
            if not named:
                continue
            for token in code_spans(block):
                for tree in named:
                    found.setdefault(token, []).append((tree, relative, number))
    return found


def mentions(block: str, tree: str) -> list[re.Match]:
    """Where a block names a tree, and not where it merely spells it.

    The underscore is the whole point of the boundary. `L3_ordinatics.hm` is a
    file in *this* repository whose name contains a sibling's, and a word
    boundary that stops at letters and digits reads it as a citation of that
    sibling. It sits four words from "declares", so it attributed a paragraph
    about this repository's own FORM declarations to another tree, and would
    have excused seven local names from having to resolve.
    """
    return list(re.finditer(r"(?<![A-Za-z0-9_-])" + re.escape(tree)
                            + r"(?![A-Za-z0-9_-])", block))


def held_by(block: str, trees: set[str]) -> list[str]:
    """The trees a paragraph says hold something, in the order they are named.

    Mention is not enough and the difference is not cosmetic. Every tree in the
    register is also a word this repository uses about itself somewhere, and
    `ordinatics` most of all. Requiring the holding verb in the same sentence
    is what separates "hyperlogic carries a P0_shadow_ground.hm" from four
    hundred paragraphs of this repository's own changelog.
    """
    named = []
    for tree in sorted(trees):
        for hit in mentions(block, tree):
            if HOLDS.search(block[hit.end():hit.end() + 80].split(". ")[0]):
                named.append(tree)
                break
    return named


def code_spans(block: str) -> list[str]:
    """Code-style names, paired left to right along each line.

    Paired in order rather than matched by a pattern over the line, because a
    pattern looking for backtick-run-backtick finds the gap *between* two spans
    whenever the first one is a single character: `a` and `b` on one line yield
    " --- and the ". That is the same off-by-one this series has already found
    once in a reader of backticked spans, arriving from the other end.
    """
    found = []
    for line in block.splitlines():
        parts = line.split("`")
        for index in range(1, len(parts), 2):
            span = parts[index].strip()
            if 2 <= len(span) <= 60:
                found.append(span)
    return found


def test_the_register_of_adjacent_repositories_names_as_many_as_it_counts() -> None:
    """A counted sentence over a list, and nothing had added the list up.

    "Three tightly coupled adjacent formal systems and one reference standard"
    is a measurement of the lines beneath it, written in words, in the file an
    agent reads first. The register can gain an entry without the sentence
    moving, or lose one, and every reading of it afterwards is wrong in a way
    no test and no build step would notice.
    """
    block = "\n".join(register())
    run = COUNTED_RUN.search(block)
    assert run, "section 1.1 no longer opens with a counted sentence"
    claimed = sum(NUMBER_WORD[word] for word in NUMBER.findall(run.group(1)))
    listed = entries()

    assert claimed >= 4, run.group(1)
    assert claimed == len(listed), (
        f"the register counts {claimed} adjacent repositories and lists"
        f" {len(listed)}: {[name for _, name, _, _ in listed]}")
    assert [number for number, _, _, _ in listed] == list(
        range(1, len(listed) + 1)), listed
    for _, name, owner, repository in listed:
        assert name == repository, (
            f"the register names `{name}` and gives the coordinate"
            f" `{owner}/{repository}`")


def test_every_repository_the_register_names_is_one_the_graph_has_or_says_it_is_not() -> None:
    """Every adjacent entry resolves or explains its exclusion from the census.

    The graph is sealed by a digest over its own body, which is checked here
    too: a hand-edit of a generated census is the failure this whole series is
    about, so the seal is what makes the comparison mean anything.
    """
    body = graph()
    recomputed = hashlib.sha256(json.dumps(
        {key: value for key, value in body.items() if key != "digest"},
        sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    assert recomputed == body["digest"], (
        "the family graph's digest does not match its body, so it has been"
        " edited by hand rather than regenerated")

    nodes = {node["id"] for node in body["nodes"]}
    assert len(nodes) == len(body["nodes"]), "duplicate family graph node"
    assert body["totals"]["repositories"] + body["totals"]["reserved"] == len(nodes)
    assert "hypermath" in nodes and len(nodes) >= 5, sorted(nodes)
    for node in body["nodes"]:
        assert node["visibility"] == "public", (
            f"{node['id']} is in a view the graph's own note calls public")

    block = "\n".join(register())
    named = {name for _, name, _, _ in entries()}
    assert len(named) >= 5, sorted(named)

    unmodelled = sorted(named - nodes)
    for name in unmodelled:
        assert NOT_A_NODE.search(entry_text(block, name)), (
            f"the register names `{name}`, the graph has no node for it, and"
            f" the entry does not say that it is deliberately not a node")
    assert unmodelled, (
        "no register entry stands outside the graph, so the guard is holding"
        " nothing: the register and the graph model different things and the"
        " place where they differ is what has to be stated")

    # The register selects adjacent repositories; the graph covers the family.
    # Requiring every graph node here would turn a local adjacency list into an
    # accidental, manually maintained second census.


def test_every_sibling_this_repository_cites_is_an_edge_the_generated_graph_has() -> None:
    """Check generated edge totals and pin local citations awaiting publication."""
    body = graph()
    nodes = {node["id"] for node in body["nodes"]}
    outbound = {edge["target"] for edge in body["edges"]
                if edge["source"] == "hypermath"}
    assert outbound and outbound <= nodes, sorted(outbound)
    counted = {kind: sum(edge["kind"] == kind for edge in body["edges"])
               for kind in ("citation", "dependency", "import")}
    assert body["totals"]["edges_by_kind"] == counted, (
        "the graph's kind-specific totals no longer describe its edges")

    cited: dict[str, str] = {}
    for path in documents():
        relative = path.relative_to(REPO).as_posix()
        text = path.read_text(encoding="utf-8")
        for name in nodes - {"hypermath"}:
            if mentions(text, name):
                cited.setdefault(name, relative)

    assert len(cited) >= 4, sorted(cited)
    ungraphed = {name: where for name, where in cited.items()
                 if name not in outbound}
    assert set(ungraphed) == set(UNGRAPHED_CITATIONS), (
        "siblings this repository cites and the generated graph has no edge"
        f" for: {sorted(ungraphed.items())}")

    gone = sorted(name for name in outbound if name not in cited)
    assert not gone, (
        f"the graph carries a citation edge to {gone} and no document here"
        " cites it any more")


def test_a_citation_that_does_not_resolve_here_names_the_tree_that_holds_it() -> None:
    """The first document about somewhere else, and what excuses its citations.

    `ax-no-return` is a gate the precursor's draft declares and no layer here
    does. `P0_shadow_ground.hm` is a file `hyperlogic` carries and this tree
    does not. Both sentences are true and both were reported as defects,
    because resolving meant resolving here.

    What is asked instead is that the paragraph name the tree, and that the
    tree be one the repository has an account of --- or the precursor, whose
    anchor is a commit this repository can check and does.
    """
    attributed = foreign_citations()
    assert attributed, "no document attributes any citation to another tree"
    assert len(attributed) <= 40, (
        "attribution has widened to the point where it excuses anything:"
        f" {len(attributed)} names")

    holders = {token: {tree for tree, _, _ in rows}
               for token, rows in attributed.items()}
    trees = set().union(*holders.values())
    assert len(trees) >= 2, sorted(trees)
    known = foreign_trees() | {"the precursor tree"}
    assert trees <= known, sorted(trees - known)

    # The two that three separate readers reported, with the tree each lives in.
    assert "the precursor tree" in holders.get("ax-no-return", set()), (
        holders.get("ax-no-return"))
    assert "hyperlogic" in holders.get("P0_shadow_ground.hm", set()), (
        holders.get("P0_shadow_ground.hm"))

    anchors = 0
    for path in documents():
        for _, block in paragraphs(path):
            for hit in PRECURSOR.finditer(block):
                anchors += 1
                commit, date = hit.group(1), hit.group(2)
                shown = subprocess.run(
                    ["git", "log", "-1", "--format=%H|%ad", "--date=short",
                     commit], cwd=str(REPO), capture_output=True, text=True)
                assert shown.returncode == 0 and shown.stdout.strip(), (
                    f"{path.name} says the precursor forked at {commit},"
                    " which is not a commit this repository has")
                full, dated = shown.stdout.strip().split("|")
                assert full.startswith(commit), (commit, full)
                if date:
                    assert dated == date, (
                        f"{path.name} dates the fork {date} and {commit} is"
                        f" dated {dated}")
    assert anchors >= 1, "no precursor citation carries a fork point"
