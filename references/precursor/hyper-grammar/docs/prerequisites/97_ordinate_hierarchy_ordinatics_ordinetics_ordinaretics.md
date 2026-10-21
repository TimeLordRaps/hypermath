# Chapter 97 — The Four-Level Ordinate Hierarchy: Ordinatics, Ordinetics, and Ordinaretics

**Status:** FORM at `≡` for the level structure (ported from closed `.hm` derivations); FRAME at `=` for the prose-to-spec correspondence stated in this chapter
**Presupposes:** Chapter 48 (ordinatics), Chapter 49 (hyperordinality), Chapter 50 (wrap operation W), Chapter 51 (imaginary ordinates), Chapter 76 (form calculus), Chapter 84 (cardinals and in-betweenness)
**Backing spec:** `hypermath_frame/spec/ordinatics.hm` §1 (Four-Level Type Hierarchy, lines 177–358), `hypermath_frame/spec/stdlib/surordinal_extension.hm`, `hypermath_frame/spec/stdlib/surordinal_real_extension.hm`, `hypermath_frame/spec/stdlib/hyperordinal.hm`
**Date:** 2026-08-06
**Key insight:** a four-level ordinal type hierarchy (Ordinal → Subreal → Complordinal → Hyperordinal) was already closed at `≡` in the `.hm` spec layer on 2026-04-13, independently of the numbered prerequisite chapters. It was never ported into prose. This chapter is that port, and assigns it the reader-facing vocabulary requested directly: **ordinatics**, **ordinetics** (= **hyperordinary numbers**), and **ordinaretics**.

---

## What This Chapter Establishes

`FRAME` at the start: Chapters 48–53 and 83–84 built ordinatics as a single flat system — ordinals, the wrap operation W, imaginary ordinates ι, and the ordinatic complex plane (=, ι) — with no explicit account of *levels*. Meanwhile, three open frames sat unresolved: Chapter 76's form-calculus derivative and integral required "ordinal division" that was flagged `FRAME — the formal definition of ordinal division as a □-derived operation is not yet in ordinatics.hm"; Chapter 84 flagged the jump from countable to continuum cardinality as needing "a power-set ordinal extension" not yet derived; and TIME.md OF-40 (2026-04-13) named a fourth, structurally unprecedented layer — "the current ordinal framework cannot represent ω^(−1)... A structure with all three [reciprocals, imaginary exponents, non-commutative addition] is unnamed" — and left it FRONTIER.

`FORM` at the end: the four levels are named, ordered, and each is given a wrap operation with a known codomain. **Ordinatics** (Chapter 48, unchanged) is Level 0. **Ordinetics**, synonymously **hyperordinary numbers**, is Level 1 — the field extension of ordinatics that first admits reciprocals and fractional powers of ω, closing Chapter 76's ordinal-division frame. **Ordinaretics** is Level 2 — the complex-valued extension of ordinetics, where W-images leave the real line entirely and trace a logarithmic spiral in ℂ. Level 3 (Hyperordinal) remains FRONTIER; it is the subject of Chapter 98.

---

## Why the Levels Were Missed by the Numbered Chapters

Chapter 48 built ordinal addition and multiplication. Chapter 50 built W. Chapter 51 built the imaginary ordinate ι and the ordinatic complex plane. At no point did the chapter sequence ask: *what is ω⁻¹?* Classical ordinal arithmetic has no answer — Chapter 48's successor-case definition (`α + S(β) = S(α + β)`) only ever produces larger ordinals; there is no ordinal operation that shrinks one. The question was structurally unaskable inside Chapters 48–53's vocabulary.

The `.hm` spec layer asked it anyway, on 2026-04-13, while working the W-spectrum problem from the opposite direction: W-coherence under multiplication (`W(α·β) = W(α)·W(β)`) *forces* a value for `W(ω⁻¹)` whether or not `ω⁻¹` has been defined as an ordinal. Solving `1 = W(1) = W(ω · ω⁻¹) = W(ω) · W(ω⁻¹) = −½ · W(ω⁻¹)` gives `W(ω⁻¹) = −2` — a perfectly good rational number, demanding a form to attach to. That form is not an ordinal. It is the next level up.

This is the same move Chapter 51 made for `1+ω` vs `ω+1`: a gap in the existing vocabulary, found by pushing the arithmetic until it broke, resolved by naming what the break was pointing at. Chapters 48–53 did it once (real → imaginary). The `.hm` layer did it three more times in a single day, producing Levels 1, 2, and a FRONTIER stub for Level 3. This chapter gives Levels 0–2 their prose names.

---

## Level 0 — Ordinatics (unchanged from Chapter 48)

**Ordinatics** (etymology given in Chapter 48: *ordi(nal) + -atics*, the study of order) is the limit-power basis form — the ordinal arithmetic already established: `0, 1, 2, ..., ω, ω+1, ..., ω·2, ..., ω², ..., ε₀, ...`. Its defining property, carried forward unchanged:

- Non-commutative addition at limit ordinates: `1 + ω = ω ≠ ω + 1` (Chapter 48).
- No reciprocals: `ω⁻¹` is not representable at this level (`hypermath_frame/spec/ordinatics.hm` line 196).
- `W : Ordinal → ℤ` — the wrap operation lands in the integers (Chapter 50).

Nothing here changes. Level 0 is ordinatics exactly as Chapter 48 left it. It is included in the table below only to show what it is a level *of*.

---

## Level 1 — Ordinetics / Hyperordinary Numbers (new: Subreal)

**Definition.** Ordinetics is the field extension of ordinatics that admits negative and fractional exponents of ω. A form at this level is defined *by its W-image*: `ω^r` for `r ∈ ℚ̄` (the algebraic closure of ℚ) is the unique form `F` such that `W(F) = (−½)^r`. Existence and uniqueness follow from W-injectivity on this class (`hypermath_frame/spec/stdlib/surordinal_extension.hm` §5), not from importing a pre-built total order — the form is defined by what W says about it, which keeps the derivation internal to the □-system rather than importing an external number-theoretic construction wholesale.

**Why "ordinetics."** Read as *ordin(al) + net + -ics*: the layer where ordinal forms first become **netted** — closed under division, joined into a field. At Level 0, `ω` has no inverse; there is no operation that connects `ω` back to `1` by division. At Level 1, that connection exists for every nonzero form: `ω · ω⁻¹ ≡ 1`. Ordinetics is named for the joining operation that Level 0 structurally lacks.

**Why "hyperordinary numbers"** (the synonym, offered in parallel — same relationship as *ordinatics =~ ordimatics* in Chapter 48, §"Ordimatics =~ Ordinatics"). Read as *hyper- (beyond) + ordinary (the base number field ℚ/ℝ) + numbers*: this level is reached by extending the *ordinary* numbers with the infinite and infinitesimal structure that ω supplies, while remaining closed under the field operations — unlike ordinatics, which is not a field, and unlike Level 2, which is no longer confined to the real line. Where **ordinatics** answers to *ordering* (the etymology Chapter 48 gave), **hyperordinary numbers** answers to *number* — same level, two derivation paths, `=~` in the sense Chapter 48 already established for ordinatics/ordimatics. Canonical form in this document: **ordinetics** (parallel structure with ordinatics and ordinaretics is the entry path). **Hyperordinary numbers** is the equally valid alternate characterization, used where the field/number-theoretic sense is structurally foregrounded.

**Values.**

| Form | W-image | Class |
|------|---------|-------|
| `ω⁰` | `1` | integer |
| `ω¹` | `−½` | rational (Chapter 50) |
| `ω⁻¹` | `−2` | integer — *not* 0; retracts an earlier ℤ-codomain error (`surordinal_extension.hm` §2 step 2). `W(ω⁻¹) = 0` was the wrong guess: it conflated the real limit `ω⁻¹ → 0⁺` with the W-image, which is algebraic, not a limit. |
| `ω^(1/3)` | `−(½)^(1/3)` | real algebraic irrational |
| `ω^(1/2)` | `i/√2` | complex algebraic — exits ℝ; the bridge to Level 2 |

**Properties** (`hypermath_frame/spec/ordinatics.hm` lines 218–232):

- **Commutative addition**, overriding Level 0's non-commutativity: `a + b = b + a` for all ordinetic forms. This is the cost of the field extension — non-commutativity is recovered only by dropping back to the Ordinal sub-type, or by going up to Level 3 (Chapter 98).
- **Algebraically closed division ring**: every nonzero form has a multiplicative inverse. `ω · ω⁻¹ ≡ 1`, checked: `W(ω)·W(ω⁻¹) = (−½)(−2) = 1 = W(1)`.
- **`W : Ordinetics → ℚ̄`** — the wrap operation's codomain is the algebraic closure of ℚ, strictly larger than Level 0's ℤ, strictly smaller than Level 2's ℂ_fin (transcendentals like `e`, `π`, `ln 2` are not reachable here — they first appear at Level 2, via the exponential/logarithm machinery).

**Bridge to Chapter 49 (hyperordinality).** Chapter 49 coined *hyperordinal* for a `~`-class of ordinates, `[α]_~`, and *hyperordinary structure* for a pair `(H, ○)` with `H` a hyperordinal and `○` a hyperoperation into `P(H)\{∅}` — built entirely at the `~` level, before Chapters 50–51 existed. Ordinetics, arriving later from the W-coherence direction, is the same territory approached from the `≡`/`=` level: not a similarity class of ordinates, but a concrete field of forms with a single-valued W. The two are not in conflict — Chapter 49's hyperordinal is the coarse `~`-shadow that ordinetics' field structure casts. A hyperordinal `[α]_~` containing `ω` and an ordinetic form `ω^r` are `~`-related whenever they share continuation capacity, exactly as Chapter 49's filtration predicts; ordinetics simply supplies the `≡`/`=`-level detail that Chapter 49 left as a structural claim (its Open Frame 2, "cofinality ≡ ~ breadth," is FRAME for exactly this reason — it is asking for what ordinetics now partially supplies). This is a naming convergence, not a collision: both names point at the "between" layer, arrived at from opposite ends of the filtration.

---

## Level 2 — Ordinaretics (new: Complordinal)

**Definition.** Ordinaretics extends ordinetics by the imaginary unit `ι` with `ι² = −1` at the `=` level, plus the transcendental forms generated by `exp_surcomp` and `Ln_surcomp`. A form here is `ω^(a+bι)` for `a, b` ordinetic; its W-image is a point in `ℂ_fin`.

**Why "ordinaretics."** Read as *ordinat(ics) + re- (again) + -tics*: ordinatics, applied a second time. The step from ordinatics to ordinetics was one extension (admit division). The step from ordinetics to ordinaretics is that same kind of move made **again**, on top of the result — admit a second, orthogonal generator. This is the literal shape of "beyond beyonds infinitum": not one crossing of a boundary but the boundary-crossing operation iterated on its own output. Ordinaretics is where the *"complex infinities"* live in the most direct sense available in this system — its forms are literally surreal-valued exponents of ω composed with an imaginary unit (`No[i]`, "complex infinities" is not a metaphor here, it is the type).

**The spiral, not the circle.** The single most important correction this level makes to naive expectation: `W(ω^(ι·t))` does **not** trace the classical unit circle. It traces an equiangular (logarithmic) spiral:

$$W(\omega^{\iota t}) = \exp(-t(\pi + \iota \ln 2)) = e^{-t\pi} \cdot e^{-\iota t \ln 2}$$

anchored entirely by `W(ω) = −½` (`hypermath_frame/spec/stdlib/exponential_surreal_composition.hm` §5, cited in `ordinatics.hm` lines 288–296). An earlier working claim that the image was the classical unit circle (`W(e^{ι·2πk/n}) = e^{2πik/n}`) is explicitly retracted in the spec — the classical roots of unity only reappear if the base is renormalized, which is a separate, still-open closure (`F1` in the spec's frontier tracking). Every point of the spiral, real-axis restriction included, is reachable this way: `Φ(a,b) = exp((a+ιb)(−ln2+ιπ))` is a bijection onto `ℂ\{0}` (`hypermath_frame/spec/stdlib/surordinal_real_extension.hm` §8.3), so `W` restricted to ordinaretics is a complete coordinate system for the finite complex plane minus the origin.

**`ordinaretic ι` is not `Chapter 51's ι` — same as the spec already flags.** `hypermath_frame/spec/ordinatics.hm` line 272 states this explicitly and it is worth restating in prose because the symbol collision is real: Chapter 51's `ι` satisfies `ι² ≡ −1` — a `≡`-level, *non-commutative* claim, derived from the ordinatic non-commutativity gap `δ(ω,1)`. Ordinaretic `ι` satisfies `ι² = −1` — an `=`-level, *commutative* claim, imported the moment the field extension is taken. They are `~` to each other (same continuation-capacity shape: both are "the direction orthogonal to the real ordinate axis") but **not** `≡` (Chapter 51's ι carries non-commutative residue that ordinaretic ι has, by construction, discarded). Using one where the other is meant is the single easiest error to make once both are on the page. Chapter 98 depends on keeping them apart.

**`W : Ordinaretics → ℂ_fin`**, `FORM` at `≡` (the coherence and spiral structure are derived), `FRAME` at `=` (full closure needs the ordinetic metric completeness step, closed separately in `surordinal_metric.hm` / `surordinal_real_extension.hm` §§3–4 for the real-restriction case).

---

## The Level Table

| Level | Prose name | Spec type | Admits | `W` codomain | Commutative addition? | Status |
|-------|-----------|-----------|--------|--------------|------------------------|--------|
| 0 | Ordinatics (Ch48) | `Ordinal` (limit-power basis form) | — | ℤ | No (native non-commutativity) | FORM |
| 1 | Ordinetics / Hyperordinary numbers | `Subreal` | reciprocals, fractional powers of ω | ℚ̄ | Yes | FORM at `≡`, FORM at `=` for integer exponents |
| 2 | Ordinaretics | `Complordinal` | imaginary exponents, transcendentals | ℂ_fin | Yes | FORM at `≡`, FRAME at `=` |
| 3 | (Chapter 98) | `Hyperordinal` | `≡`-graded non-commutativity restored on top of Level 2 | `≡`-class of ℂ_fin | Graded — `~`-yes, `≡`-no, `=`-no | FRONTIER |

Each level *strictly contains* the one below it as a sub-type (`Subreal extends Ordinal`, `Complordinal extends Surreal`), and each pays for what it gains: Level 1 buys division by giving up native ordinal non-commutativity; Level 2 buys the imaginary direction by giving up realness; Level 3 (Chapter 98) attempts to buy back what Level 1 gave up, without giving up what Level 2 bought.

---

## Closure: Chapter 76's Ordinal-Division Frame

Chapter 76 (form calculus) stated an explicit blocking `FRAME`: *"the formal definition of ordinal division as a □-derived operation is not yet in ordinatics.hm... the form calculus derivative at limit ordinates is `~~` motivated but not `==` closed until ordinal division is derived."* Ordinetics closes this. Division by a nonzero ordinetic form is total (§ "Level 1" above, algebraically-closed-division-ring property) — for the first time in this chapter sequence, `Δquant` in the form-calculus derivative can be a genuine ordinetic quotient rather than an undefined operation. This does not by itself close Chapter 76's derivative and integral definitions to `FORM` — the wrap-semantics of the limit inside a derivative still needs to be spelled out — but it removes the specific missing primitive Chapter 76 named. Status: Chapter 76's ordinal-division `FRAME` upgrades from *blocked-on-undefined-operation* to *blocked-on-composing-two-now-defined-operations* (division, from this chapter; wrap-at-a-limit, from Chapter 50). See Chapter 99 for the full downstream accounting.

---

## Summary Table

| Term | Definition established in this chapter |
|------|------------------------------------------|
| Ordinatics | Level 0 — Chapter 48, unchanged. Ordinal, limit-power basis form. |
| Ordinetics | Level 1 — the field extension admitting reciprocals and fractional powers of ω. `=~` hyperordinary numbers. |
| Hyperordinary numbers | Synonym for ordinetics, entered from the "extends the ordinary numbers" derivation path rather than the "nets ordinals into a field" path. |
| Ordinaretics | Level 2 — the complex-valued extension of ordinetics; W-images trace a logarithmic spiral, not a circle. |
| `W(ω⁻¹) = −2` | Corrected value; retracts an earlier `W(ω⁻¹) = 0` error that conflated the real limit with the W-image. |
| Ordinaretic ι | `ι² = −1`, commutative, `=`-level. **Not** Chapter 51's ι (`ι² ≡ −1`, non-commutative, `≡`-level). `~` but not `≡`. |

---

## Open Frames

1. **Ordinaretics `=`-closure** (FRAME): `W : Ordinaretics → ℂ_fin` is FORM at `≡`; the `=`-level closure requires the ordinetic metric completeness argument, done for the real-axis restriction (`surordinal_real_extension.hm` §§3–4) but not yet stated in prose form here. Closure criterion: port that argument into this chapter or a successor.

2. **Renormalized base and classical roots of unity** (FRAME, inherited from spec `F1`): the classical unit circle only reappears from ordinaretics under a renormalized base `ω̃`, not yet derived. Until then, "the ordinatic complex plane looks like the classical one" is false in general, and this chapter's spiral correction should be treated as the standing claim.

3. **Chapter 49 / ordinetics unification at `=`** (FRAME): the bridge stated above (§"Bridge to Chapter 49") is a structural identification at `~`, consistent with but not derived from Chapter 49's own open frames (its Open Frame 1 and 2). Closure criterion: a formal map `[α]_~ → {ordinetic forms with W-image in a fixed ~-neighborhood}` shown to be well-defined.

---

## Forward Dependencies

- **Chapter 98 (Dimensional Transition Operators):** Level 3 — Hyperordinal — requires all three levels of this chapter, plus Chapter 51's (non-commutative, `≡`-level) ι kept distinct from ordinaretic ι.
- **Chapter 99 (Language Calculus Downstream):** traces what this chapter's closures and remaining frames do to Chapter 09's and Chapter 76's open items.

---

## Legend

| Structural Term | Classical Cross-Reference |
|------------------|---------------------------|
| Ordinetics / Subreal | Surreal numbers (Conway, 1970s) restricted to the algebraic-exponent sub-field of powers of ω; no total order imported, form existence defined via W-preimage instead (`hypermath_frame/spec/nomenclature.hm` §4 renames the surreal-field construction to "properly-ordered class-field," POCF, to satisfy the etymological naming constraint governing that spec layer). |
| Ordinaretics / Complordinal | Surcomplex numbers `No[i]`; the W-image spiral is the ordinatic analog of the complex exponential's argument/modulus decomposition. |
| `W(ω^n) = (−½)^n` | Geometric-sequence homomorphism `(Ord,+) → (ℂ,·)`; the unique such homomorphism sending ω to its Chapter 50 W-value. |
