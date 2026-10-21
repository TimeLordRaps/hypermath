# Excluded declarations

The release claims only what Lean proves. A declaration whose axiom closure
contains `sorryAx` is not proved, so it is **excluded** from every claim the
release makes. It stays in the source, unchanged, where its docstring already
states why it is admitted.

This table is the exclusion list. The Lean file SorryExclusions.lean, in this
folder, holds it to what Lean reports. Run it from here:

```
lake env lean SorryExclusions.lean
```

It exits 0 and prints a line beginning `SORRY_EXCLUSIONS PASS`, then one
`EXCLUDED` line per entry, only when all four of these hold:

1. The declarations of the library whose axiom closure contains `sorryAx` are
   exactly the entries of its `excludedDeclarations`, each in the module
   recorded for it. A new admission, a new dependent of an existing one, an
   admission proved but left on the list, or a declaration moved to another
   module each make it exit 1.
2. Every non-entailment witness in it uses only `propext`, `Classical.choice`
   and `Quot.sound`.
3. Its `production_clauses` uses exactly the axioms declared in the four layer
   modules, so the clause structure leaves no production assumption out.
4. `Hypermath.definitionOfGround` is declared in `L0Ground` and does not reach
   `sorryAx`.

When it fails, change the source, or change this table and the list in
SorryExclusions.lean together. That file carries no comments on purpose: the
test suite pins the amount of comment prose under this folder, and this page is
where the explanation lives.

## The list

There are no exclusions. No declaration of the library reaches `sorryAx`, and
`excludedDeclarations` is empty, so the first check holds the library to zero:
any admission added later makes the check exit 1 until it is listed here. The run
prints `excluded=0` and no `EXCLUDED` lines.

Check 2 currently has no witnesses to inspect. The earlier non-entailment
models were removed because they do not satisfy the closing clauses of
`L0Ground` section VIII.b and `axCongruentPathSymm`, which the formerly
admitted proofs now use.
`HypermathFullAxiomModel.closing_clauses_consistent_with_full_axioms` exhibits
one interpretation in which those clauses hold together with the 44 clauses
listed by `FullAxioms`.

## Scope

The check scans every constant declared in a `Hypermath.*` module of the
library, which is what `lake build` builds. The standalone reporter files in
this folder (`Countermodels.lean`, `FullAxiomModel.lean` and the others) are
not library modules and are not scanned here. The audit runs them separately
and checks their axiom reports.

## Why the declarations were not moved or renamed

The exclusion is recorded beside the source rather than by moving the excluded
declarations into a namespace of their own. Their names are cited by the audit
package's baseline, by the test suite's pinned admission list, by the research
notes, and by other declarations' docstrings. Renaming them would change each
of those, and would change what the audit reports, without changing what is
proved. Their docstrings already state each admission's status and name its
witnesses, and the test suite already holds them to that. What was missing was
a single, machine-checked statement of what is excluded from the claim. That is
this file and SorryExclusions.lean.
