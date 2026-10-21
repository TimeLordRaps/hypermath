"""The grant one layer writes and the copy the next layer keeps of it.

Every layer closes with a `graduation` block that hands the next layer a
lettered grant: `permits L<n+1>:` and `prohibits L<n+1>:`. The receiving layer
opens with a copy of it, under a header that says what the copy is for.

    Copied from L1 graduation block for traceability.

That header is a claim about the block beneath it, and it is the only thing
that makes the block worth reading: a copy is traceable exactly insofar as it
is a copy. Nothing inside such a block ever reads as wrong, because every
sentence in it was true somewhere --- the question is only whether it is the
sentence that was granted, addressed to the layer that was bound.

Three ways it was not, found by comparing the six grants against the four
copies clause by clause.

`L3_ordinatics.hm` copied two of the three prohibitions `L2` places on it. The
missing one is `(c)`, separate classification machinery, and the thing to see
is that `L3` *obeys* it --- "the self-kernel pattern (L0-L3) IS the
classification machinery", it says at three separate places, and its own census
closes the question as CLOSED. The constraint is alive in the body of the layer
and absent from the layer's list of constraints. That is the whole species: the
artifact does the right thing and stops saying that it must.

`L2_operations.hm` carried a sentence addressed to the wrong layer. Inside its
copy of `L1`'s grant *to L2*, clause (a) read "L3 may NOT assert: a + b == b +
a" where `L1` wrote "L2 may NOT assert commutativity for '+'". The sentence was
true --- `L3` may not, and `L2` says so itself in the block that binds `L3` ---
but a prohibition addressed to the wrong layer binds nothing at the layer it
was written for, and the clause's own next words, "Commutativity is prohibited
at L2", disagreed with its subject. Both of these are repaired, because in both
cases the granting layer says in full what the copy should have said.

The third is recorded rather than repaired, below.
"""

from __future__ import annotations

import re

from test_layer_ledger import layer_paths

#: A layer granting the next one. These sit inside the `graduation` block and
#: are indented under it; the copies are flush-left comments.
GRANT = re.compile(r"^\s+(permits|prohibits)\s+L(\d):\s*$")

#: The receiving layer's copy of one, which names both ends: whose grant it is
#: and whom it binds. The file it stands in is the file of the layer bound.
COPY = re.compile(r"^--\s*L(\d)\s+graduation\s+(permits|prohibits)\s+L(\d):\s*$")

#: A lettered clause, and the comment lines that run on from it. Two things end
#: a block --- a blank line, and the header of the next one --- and in these
#: four files they are redundant, because every block is followed by a blank
#: line and then a header. Dropping either alone changes nothing; dropping both
#: is what matters, and then the permits copy runs on into the prohibits copy
#: below it and every clause is read against the wrong one. That was the first
#: reading of this increment, and it reported defects in the loud direction
#: where there were none.
CLAUSE = re.compile(r"^\s*--\s+\(([a-z])\)\s*(.*)$")
CONTINUE = re.compile(r"^\s*--(\s.*)?$")

#: The binding form. A clause may *mention* another layer perfectly correctly
#: --- "those belong to L3", "prohibition carries forward from L2" --- and a
#: reader that took any mention for a binding would report four defects that
#: are not there. What binds is the deontic verb with a subject.
DEONTIC = re.compile(r"\bL(\d)\s+may\s+NOT\b")

#: What a clause is about, for the purpose of recognising its copy. Quoted
#: names, hyphenated and underscored identifiers, the relation symbols, and
#: plain words long enough not to be scaffolding. Words are matched exactly
#: and not stemmed: `operation` and `operations` are the only tokens standing
#: between L1's clause (d) and L2's, and stemming would hide it.
QUOTED = re.compile(r"'[^'\n]{1,30}'")
IDENT = re.compile(r"[A-Za-z_+×][A-Za-z0-9]*(?:[-_][A-Za-z0-9+×_]+)+")
WORD = re.compile(r"[A-Za-z]{5,}")
SYMBOL = re.compile(r"==|=~|~~")

#: `L0`'s grant to `L1` is the one no layer copied. The copy convention starts
#: at `L2`, and whether `L1` predates it or skipped it is not decidable from
#: the files: `L1` has a Section I, and it holds axioms rather than a copy.
UNCOPIED = {(0, 1)}

#: The two clauses where the copy is not a copy, kept as a set rather than as
#: prose so that a third one cannot open quietly. `L1` permits `L2` (c) the
#: quant family and (d) free use of filtration. `L2`'s copy puts `'compose'`
#: at (c) and finite structural operations at (d) --- and the substitution is
#: not idle in either direction. `L2` *uses* both grants it dropped: it spends
#: `quantification` and `quanta` throughout its congruent-path close, and it
#: cites "the filtration chain (== -> =~ -> ~~, L1 Section I)" by name. And
#: `'compose'`, which the copy reports as granted, is granted by nobody --- the
#: string does not occur in `L0_ground.hm` or `L1_relations.hm` at all, while
#: `L2`'s own grant to `L3` leans on it, permitting `L3` to close
#: `simulation-pair-exists` "using compose + ordinal continuation".
#:
#: So the chain of grants has a link that begins in the middle, and that is why
#: this is recorded and not repaired. Making the copy a copy would delete the
#: only sentence in the stack that says `compose` is permitted; leaving it
#: leaves the header's claim false. Which one the specification wants is a
#: question about whether `L1`'s grant should reach `DerivationPath`, and that
#: is a question about the theory rather than about its bookkeeping.
DIVERGED = {(1, 2, "permits", "c"), (1, 2, "permits", "d")}


def blocks() -> tuple[dict, dict]:
    """The grants each layer writes and the copies each layer keeps."""
    grants: dict[tuple[int, int, str], tuple[int, int, dict[str, str]]] = {}
    copies: dict[tuple[int, int, str], tuple[int, int, dict[str, str]]] = {}
    for index, path in sorted(layer_paths().items()):
        lines = path.read_text(encoding="utf-8").splitlines()
        for number, line in enumerate(lines):
            grant, copy = GRANT.match(line), COPY.match(line)
            if grant:
                key = (index, int(grant.group(2)), grant.group(1))
            elif copy:
                key = (int(copy.group(1)), int(copy.group(3)), copy.group(2))
            else:
                continue
            clauses: dict[str, list[str]] = {}
            letter: str | None = None
            for follow in lines[number + 1:]:
                if GRANT.match(follow) or COPY.match(follow):
                    break
                if not follow.strip():
                    if letter is not None:
                        break
                    continue
                hit = CLAUSE.match(follow)
                if hit:
                    letter = hit.group(1)
                    clauses[letter] = [hit.group(2)]
                elif CONTINUE.match(follow) and letter is not None:
                    clauses[letter].append(follow.strip().lstrip("-").strip())
                else:
                    break
            packed = {name: " ".join(p for p in body if p).strip()
                      for name, body in clauses.items()}
            (grants if grant else copies)[key] = (index, number + 1, packed)
    return grants, copies


def distinctive(text: str) -> set[str]:
    """The tokens by which a clause can be told from its neighbours."""
    found = set(QUOTED.findall(text)) | set(IDENT.findall(text))
    found |= {word.lower() for word in WORD.findall(text)}
    return found | set(SYMBOL.findall(text))


def test_every_clause_a_layer_grants_is_a_clause_the_next_layer_copies() -> None:
    """A copy with a clause missing is a permission the copy does not report.

    Letters are the whole of what is asked here, and they are enough: `L3`'s
    copy of the prohibitions `L2` places on it ran (a), (b), and stopped, so
    the layer's own list of what it may not do was short by one of three.
    """
    grants, copies = blocks()
    assert len(grants) >= 6, sorted(grants)
    assert len(copies) >= 4, sorted(copies)
    assert {kind for _, _, kind in grants} == {"permits", "prohibits"}
    for key, (_, line, clauses) in sorted(grants.items()):
        assert clauses, f"{key} at line {line} grants nothing"

    # A copy belongs to the layer it binds, and copies the layer below it.
    misplaced: list[str] = []
    for (granter, bound, kind), (index, line, _) in sorted(copies.items()):
        if index != bound or granter != bound - 1:
            misplaced.append(f"L{index}:{line}: a copy of L{granter}'s"
                             f" {kind} on L{bound}, kept by L{index}")
    assert not misplaced, "copies kept by the wrong layer:\n" + "\n".join(misplaced)

    uncopied = {(granter, bound) for granter, bound, _ in grants
                if (granter, bound, "permits") not in copies
                and (granter, bound, "prohibits") not in copies}
    assert uncopied == UNCOPIED, (
        f"grants with no copy at all: {sorted(uncopied)}, recorded"
        f" {sorted(UNCOPIED)}")

    compared, short = 0, []
    for key, (_, _, granted) in sorted(grants.items()):
        if key not in copies:
            continue
        compared += 1
        index, line, copied = copies[key]
        for letter in sorted(set(granted) - set(copied)):
            short.append(f"L{index}:{line}: the copy of L{key[0]}'s {key[2]}"
                         f" on L{key[1]} has no ({letter}), which grants"
                         f" — {granted[letter][:56]}")
        for letter in sorted(set(copied) - set(granted)):
            short.append(f"L{index}:{line}: the copy has ({letter}) and no"
                         f" grant does — {copied[letter][:56]}")
    assert compared >= 4, compared
    assert not short, "clauses a copy and its grant do not share:\n" + "\n".join(
        short)


def test_a_copied_clause_is_about_what_the_clause_it_copies_is_about() -> None:
    """Matching letters are not matching clauses, and twice they were not.

    Letters agree while the text underneath is substituted, which is the
    quieter half and the one that cannot be seen by counting. A clause and its
    copy have to share at least one distinctive token --- and the reader has to
    be shown able to tell clauses apart at all, or sharing means nothing.
    """
    grants, copies = blocks()
    pairs: list[tuple[tuple[int, int, str], str, int]] = []
    apart = 0
    for key, (_, _, granted) in sorted(grants.items()):
        if key not in copies:
            continue
        _, _, copied = copies[key]
        for letter in sorted(set(granted) & set(copied)):
            here = distinctive(granted[letter])
            assert here, (f"{key} ({letter}) has no distinctive token, so"
                          f" nothing about it can be recognised")
            pairs.append((key, letter, len(here & distinctive(copied[letter]))))
            # The same clause against every other letter of its own copy: a
            # reader generous enough to match those is matching scaffolding.
            for other in sorted(set(copied) - {letter}):
                if not here & distinctive(copied[other]):
                    apart += 1

    assert len(pairs) >= 14, len(pairs)
    assert apart >= 25, (
        f"only {apart} mismatched clause pairs share nothing, so the reader"
        f" cannot tell clauses apart and sharing proves nothing")

    diverged = {(key[0], key[1], key[2], letter)
                for key, letter, shared in pairs if not shared}
    assert len(pairs) - len(diverged) >= 13, (
        f"only {len(pairs) - len(diverged)} clause pairs share anything")
    extra = sorted(diverged - DIVERGED)
    assert not extra, (
        "clauses whose copy is about something else: "
        + str([(f"L{g}", f"{kind} L{b}", letter) for g, b, kind, letter in extra]))
    assert diverged == DIVERGED, (
        f"recorded divergences that closed: {sorted(DIVERGED - diverged)}")


def test_a_prohibition_binds_the_layer_whose_block_it_stands_in() -> None:
    """"L3 may NOT", said a block binding L2, in the clause that binds it.

    The block is a copy of what `L1` permits `L2`, and clause (a) is `'+'`.
    `L1` writes the prohibition as "L2 may NOT assert commutativity", `L2`
    restates it that way two blocks down, and `L2` says the forward form --
    that the prohibition carries to `L3` -- in the block that binds `L3`. Only
    here, where the subject had to be `L2`, was it `L3`.
    """
    grants, copies = blocks()
    found: list[tuple[int, int, str, str, int]] = []
    wrong: list[str] = []
    for source, which in ((grants, "grant"), (copies, "copy")):
        for (granter, bound, kind), (index, line, clauses) in sorted(source.items()):
            for letter, body in sorted(clauses.items()):
                for hit in DEONTIC.finditer(body):
                    named = int(hit.group(1))
                    found.append((index, line, kind, letter, named))
                    if named == bound:
                        continue
                    wrong.append(
                        f"L{index}:{line}: the {which} of L{granter}'s {kind}"
                        f" on L{bound}, clause ({letter}), forbids L{named}"
                        f" — {body[:64]}")

    assert len(found) >= 10, found
    assert len({(index, line) for index, line, _, _, _ in found}) >= 3, (
        "the deontic reader sees one block only, so it has narrowed")
    assert {kind for _, _, kind, _, _ in found} >= {"prohibits"}, found
    assert not wrong, (
        "prohibitions addressed to a layer the block does not bind:\n"
        + "\n".join(wrong))
