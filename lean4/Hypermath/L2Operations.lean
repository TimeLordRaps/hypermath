-- Hypermath.L2Operations
-- Layer 2: Operations
-- Lean4 mechanization scaffold for L2_operations.hm
--
-- Introduces: DerivationPath, pathStep, pathGround, pathLength, pathTrace,
--             compose, congruentPath, +, additionally, reflexion,
--             orbit-reflexion-quotient.
-- P_2 = 42.  N_2_atomic = 3 (DerivationPath, pathStep, pathGround).  G_2 = 4.
-- Source census raised 31 -> 39 on 2026-09-20 when `~=` (abstracted-path) was
-- back-propagated into L2_operations.hm. The eight new steps are steps 8, 26-31
-- and 38; six of them are mechanized in QuadrilateralFiltration, not here.
-- Source: L2_operations.hm

import Hypermath.L1Relations

namespace Hypermath

-- ============================================================================
-- §I  Layer Permits and Prohibits
-- (Copied from L1 graduation block for traceability.)
-- ============================================================================

-- Permits L2:
--   (a) DerivationPath :: Type — a finite record of f2f-steps with trace levels.
--   (b) + (additionally) — co-presence, commutative.
--   (c) quant family (preview of L3; full arithmetic in L3).
--   (d) Filtration freely: any operation preserving ≡ preserves =~ and ~~.

-- Prohibits L2:
--   (a) ordinal_limit or any infinite ordinal — L3 only.
--   (b) Separate classification machinery — self-kernel IS the machinery.
--   (c) Closing simulation-pair-exists — requires L3 continuation-path.
--   (d) Commutativity for + — hard invariant: + is non-commutative.

-- ============================================================================
-- §II  Primitives — DerivationPath
-- Three atomic forms at L2. All definition-acts. FORM.
-- ============================================================================

/-- A finite record of f2f-steps with associated trace levels.
    Analogous to a typed derivation sequence. -/
axiom DerivationPath : Type

/-- Unit path: a single f2f-step from Form x to Form y. -/
axiom pathStep : Form → Form → DerivationPath

/-- The empty derivation path. Identity element for compose. -/
axiom pathGround : DerivationPath

/-- Endpoint projections used explicitly in L3_ordinatics.hm:123–125.
    These are uninterpreted source parameters, not an implementation of paths.
    No endpoint law or path finiteness theorem is assumed by declaring them. -/
axiom pathStart : DerivationPath → Form
axiom pathEnd : DerivationPath → Form

/-- Path length: the number of steps, represented as a Form.
    For pathGround: ~~ ground (zero steps).
    For pathStep(x)(y): ~~ f2f(ground) (one step).
    Arithmetic (full ordinal grounding) is FRAME/L3. -/
axiom pathLength : DerivationPath → Form

/-- Path trace: the minimum trace level (~~/=~/≡) across all steps.
    Minimum trace arithmetic is FRAME/L3. -/
axiom pathTrace : DerivationPath → Form

/-- Sequential composition of two DerivationPaths.
    compose(p)(q) traverses p then q.
    Governed by axComposeAssoc, axComposeIdentity. -/
axiom compose : DerivationPath → DerivationPath → DerivationPath

/-- The =~-analog for DerivationPath: same substance regardless of intermediate steps.
    congruentPath(p, q) iff same (start, end, pathTrace, quantification).

    Opaque, and only three of the 39 clauses mention it -- `axComposeAssoc`,
    `axComposeIdentity`, `axComposeNonempty` -- none of which relates
    `congruentPath p q` to `congruentPath q p`. Symmetry is therefore
    independent of the clauses:
    `HypermathFullAxiomModel.congruentPath_symmetry_independent`.

    Making the reading above into a definition does not settle it either.
    `HypermathFullAxiomModel.tuple_reading_consistent_and_conditional` builds
    that definition from the four existing parameters, shows it satisfies all 39
    clauses, and shows its symmetry is exactly symmetry of `=~` -- which is
    itself undeclared, by
    `HypermathCountermodel.AsymmetricCongruent.congruent_symmetry_independent`.
    Defining this parameter relocates the missing assumption to `=~`; it does
    not remove it. See `docs/research/CLAUSE_INDEPENDENCE.md`. -/
axiom congruentPath : DerivationPath → DerivationPath → Prop

/-- **ax-congruent-path-symm**: path congruence holds both ways. -/
axiom axCongruentPathSymm :
    ∀ p q : DerivationPath, congruentPath p q → congruentPath q p

-- ============================================================================
-- §III  Axioms for + (non-commutative sequential connection)
-- ============================================================================

-- Translation boundary: these clauses quantify separate witnesses. No binary
-- Form operation for + or additionally is declared or bound to those witnesses.
-- They therefore do not implement the source's operation laws. Sequential.lean
-- proves that a common operation with the source's two-sided identity and
-- uniform separation cannot exist for nontrivial symmetric, transitive
-- congruence. The current clauses themselves are left unchanged.

/-- **ax-seq**: a common similarity witness exists for each pair.
    Identifying that witness with a particular a + b requires another construction. -/
axiom axSeq : ∀ a b : Form, ∃ c : Form, (c ~~ a) ∧ (c ~~ b)

/-- **ax-seq-asymm**: incongruent inputs have two incongruent similarity witnesses.
    This translation does not bind those witnesses to a + b and b + a. -/
axiom axSeqAsymm :
    ∀ a b : Form, ¬ (a =~ b) →
      ∃ c d : Form,
        (c ~~ a) ∧ (c ~~ b) ∧
        (d ~~ b) ∧ (d ~~ a) ∧
        ¬ (c =~ d)

/-- Separate identity witnesses; neither clause refers to a binary + operation. -/
axiom axSeqIdentityR : ∀ a : Form, ∃ c : Form, (c ~~ a) ∧ (c =~ a)
axiom axSeqIdentityL : ∀ a : Form, ∃ c : Form, (c ~~ a) ∧ (c =~ a)

-- ============================================================================
-- §IV  Axioms for additionally (commutative co-presence)
-- ============================================================================

/-- **ax-coop**: a common similarity witness, without a bound additionally operation. -/
axiom axCoop : ∀ a b : Form, ∃ c : Form, (c ~~ a) ∧ (c ~~ b)

/-- Two congruent co-presence witnesses; no binary additionally function is bound. -/
axiom axCoopComm :
    ∀ a b : Form, ∃ ca cab : Form,
      (ca ~~ a) ∧ (ca ~~ b) ∧
      (cab ~~ b) ∧ (cab ~~ a) ∧
      (ca =~ cab)

/-- A co-presence identity witness, without a bound binary operation. -/
axiom axCoopIdentity : ∀ a : Form, ∃ c : Form, (c ~~ a) ∧ (c =~ a)

-- ============================================================================
-- §V  Axioms for compose and congruentPath
-- ============================================================================

/-- compose is associative at congruentPath level. -/
axiom axComposeAssoc :
    ∀ p q r : DerivationPath,
      congruentPath (compose p (compose q r)) (compose (compose p q) r)

/-- pathGround is the two-sided identity for compose. -/
axiom axComposeIdentity :
    ∀ p : DerivationPath,
      congruentPath (compose p pathGround) p ∧
      congruentPath (compose pathGround p) p

/-- At least one non-trivial DerivationPath exists connecting any two Forms. -/
axiom axComposeNonempty :
    ∀ x y : Form, ∃ p : DerivationPath, ¬ congruentPath p pathGround

-- ============================================================================
-- §VI  Derives (all FORM unless marked FRAME)
-- ============================================================================

/-- (a + b) ~~ a and (a + b) ~~ b for all a b. FORM. -/
theorem plusStaysSimilar : ∀ a b : Form, ∃ c : Form, (c ~~ a) ∧ (c ~~ b) :=
  axSeq

/-- additionally(a,b) ~~ a and additionally(a,b) ~~ b for all a b. FORM. -/
theorem additionallyStaysSimilar : ∀ a b : Form, ∃ c : Form, (c ~~ a) ∧ (c ~~ b) :=
  axCoop

/-- Distinct witness patterns for sequencing and co-presence. FORM.
    `axDiffCongruent` gives `¬ (f2f ground =~ ground)`, which is the
    incongruence `axSeqAsymm` needs. -/
theorem plusAndAdditionallyAreDistinct :
    ∃ a b : Form,
      (∃ c d : Form, (c ~~ a) ∧ (c ~~ b) ∧ (d ~~ b) ∧ (d ~~ a) ∧ ¬ (c =~ d)) ∧
      (∃ ca cab : Form, (ca ~~ a) ∧ (ca ~~ b) ∧ (cab ~~ b) ∧ (cab ~~ a) ∧ (ca =~ cab)) :=
  ⟨f2f ground, ground, axSeqAsymm _ _ (axDiffCongruent ground), axCoopComm _ _⟩

/-- pathGround is the two-sided identity for compose. FORM. -/
theorem pathGroundIsIdentity :
    ∀ p : DerivationPath,
      congruentPath (compose p pathGround) p ∧
      congruentPath (compose pathGround p) p :=
  axComposeIdentity

/-- The concrete self-read trace. No conversion to opaque DerivationPath is
    assumed: that source-to-scaffold bridge remains a separate obligation. -/
def reflexionTrace (x : Form) : DEntry x x := selfRead x

/-- Self-read is a two-sided identity for finite D-entry composition, at the
    correct endpoints. This concerns dEntryCompose, not opaque compose. -/
theorem reflexionTraceComposeIdentity {x y : Form} (p : DEntry x y) :
    dEntryCompose (reflexionTrace x) p = p ∧
    dEntryCompose p (reflexionTrace y) = p := by
  exact ⟨Trace.nil_compose p, Trace.compose_nil p⟩

/-- The existing proposition-level reflexion API, now backed by selfRead.
    reflexionTrace exposes its actual witness and composition identity. -/
theorem reflexion : ∀ x : Form, D x x :=
  dIsReflexive

/-- A D-entry from a to b is either a zero-step read or lands b at a's substance. -/
theorem dEntryEqOrCongruent : ∀ {a b : Form}, DEntry a b → a = b ∨ (b =~ a)
  | _, _, Trace.nil _ => Or.inl rfl
  | _, _, Trace.cons edge tail => by
    obtain ⟨hmid, hcong⟩ := edge
    rcases dEntryEqOrCongruent tail with h | h
    · subst h; subst hmid; exact Or.inr hcong
    · subst hmid; exact Or.inr (axCongruentTrans _ _ _ h hcong)

/-- orbit-reflexion-quotient: two Forms whose D-columns coincide are similar.
    This is the single unified width measure. FORM.

    `D x x` gives `D x y`; that trace either is a zero-step read, and `~~` is
    reflexive, or lands at `=~`, which filtration lowers to `~~`. -/
theorem orbitReflexionQuotient :
    ∀ x y : Form,
      (∀ z : Form, D x z ↔ D y z) →
      (x ~~ y) := by
  intro x y cols
  obtain ⟨p⟩ := (cols x).mp (dIsReflexive x)
  rcases dEntryEqOrCongruent p with h | h
  · subst h; exact axSimilarRefl _
  · exact filtrationCongSim _ _ h

/-- At least one non-trivial DerivationPath exists. FORM. -/
theorem finitePathExists : ∃ p : DerivationPath, ¬ congruentPath p pathGround :=
  axComposeNonempty ground (f2f ground)

/-- **path-length is additive over compose.** Step 24 of the L2 self-kernel.
    Corrected 2026-09-20; the previous form of this declaration read

        ∀ p q : DerivationPath, pathLength (compose p q) ~~ pathLength p

    in which `q` never occurs on the right-hand side. That is not additivity —
    it says composing on the right leaves the length unchanged — and `~~` is the
    wrong tier for it. A step count is quanta content, and quanta live at `=~`:
    `L2_operations.hm:185–206` closes `congruent-path` on
    (start, end, path-trace, quantification). `~~` is broad enough to make the
    claim nearly vacuous.

    L2 has no addition on `Form` — that is precisely the FRAME — so the adding
    operator is existentially quantified here, which is the formal reading of the
    source's "length(compose(p)(q)) = length(p) + length(q) in some numeric
    sense" (`L2_operations.hm:330`).

    **No derivation is available at L2**, and the reason is checkable rather
    than asserted: every axiom that can conclude a `=~` fact either concludes it
    of `f2f x` and `x` (`traceLevels`), or from a `≡` premise
    (`filtrationSimCong`), or only of an existentially chosen witness
    (`axSeqIdentityR/L`, `axCoopIdentity`, `axCoopComm`, `axSeqAsymm`). None
    names a term built from `pathLength`, and `pathLength` is opaque, so
    `pathLength (compose p q)` cannot be recovered from `pathLength p` and
    `pathLength q` — which is exactly the well-definedness gap `add` would have
    to close. No countermodel is claimed here; independence is not established.
    The L3 discharge, with `ordinalApply` supplied for `add`, is
    `pathLengthArithmeticClaim`, which a checked full-clause model refutes. -/
def compositionLengthAdditiveClaim : Prop :=
  ∃ add : Form → Form → Form,
    ∀ p q : DerivationPath,
      pathLength (compose p q) =~ add (pathLength p) (pathLength q)

/-- **Additivity itself, proved** — on the surface where the step count is a
    `Nat` and addition therefore exists inside L2: the concrete trace witness.
    This discharges the law of step 24 constructively. What stays FRAME/L3 is
    only the Form-valued *representation* of the count, never the law. Compare
    `QuadrilateralFiltration.quantaAdditive`, the same law at the `~=` surface
    one level of abstraction up. -/
theorem dEntryLengthAdditive {x y z : Form} (p : DEntry x y) (q : DEntry y z) :
    Trace.length (dEntryCompose p q) = Trace.length p + Trace.length q :=
  Trace.length_compose p q

-- ============================================================================
-- §VII  Graduation — L2 → L3
-- Four source NCs. Their current Lean proof status is reported individually.
-- ============================================================================

-- NC-1: common similarity witnesses exist (axSeq); no operation is constructed.
theorem nc1_L2 : ∀ a b : Form, ∃ c : Form, (c ~~ a) ∧ (c ~~ b) := axSeq

-- NC-2: common co-presence witnesses exist (axCoop); no operation is constructed.
theorem nc2_L2 : ∀ a b : Form, ∃ c : Form, (c ~~ a) ∧ (c ~~ b) := axCoop

-- NC-3: compose is well-defined with pathGround identity (axComposeAssoc + axComposeIdentity). FORM.
theorem nc3_L2 :
    ∀ p : DerivationPath,
      congruentPath (compose p pathGround) p ∧
      congruentPath (compose pathGround p) p :=
  axComposeIdentity

-- NC-4: Non-trivial paths exist (finitePathExists). FORM.
theorem nc4_L2 : ∃ p : DerivationPath, ¬ congruentPath p pathGround :=
  finitePathExists

-- ============================================================================
-- §VII.a  What separates + from additionally
-- ============================================================================

/-- **The two operations are declared by the same clauses.** Both conjuncts
    below are the same proposition written twice; the left is inhabited by the
    sequencing declarations and the right by the cooperation declarations, and
    both elaborate. That is a kernel check that `axSeq` and `axCoop` are the
    same statement, and that `axSeqIdentityR`, `axSeqIdentityL` and
    `axCoopIdentity` are the same statement --- not merely corresponding ones.
    Five declarations, two propositions. `nc1_L2` and `nc2_L2` have carried the
    identical statement side by side since they were written.

    What is left is `axSeqAsymm` against `axCoopComm`. `axCoopComm` is
    unconditional; `axSeqAsymm` fires only on `¬ (a =~ b)`, and no instance of
    that is derivable from any of the 39 clauses --- see
    `HypermathTransportCountermodel.no_incongruence_is_derivable`, where `=~` is
    total and every clause still holds. So the only clause that could separate
    the two operations never applies.

    This is why `plusAndAdditionallyAreDistinct` is independent. Not because a
    model happens to make `=~` total, but because the clause set states the same
    obligations for both operations and then distinguishes them with a
    conditional it can never discharge. Declaring a distinctness clause at `=~`
    is the repair; strengthening `axSeqAsymm` in place is not, because its
    antecedent is the problem. FORM. -/
theorem sequencingClausesAreCooperationClauses :
    ((∀ a b : Form, ∃ c : Form, (c ~~ a) ∧ (c ~~ b)) ∧
      (∀ a : Form, ∃ c : Form, (c ~~ a) ∧ (c =~ a))) ∧
    ((∀ a b : Form, ∃ c : Form, (c ~~ a) ∧ (c ~~ b)) ∧
      (∀ a : Form, ∃ c : Form, (c ~~ a) ∧ (c =~ a))) :=
  ⟨⟨axSeq, axSeqIdentityR⟩, ⟨axCoop, axCoopIdentity⟩⟩

/-- **Four of the seven operation clauses are removable.** Beyond being written
    twice, `axSeq` and `axCoop` are *derivable*: `axCoopComm` already produces a
    pair of common similarity witnesses for every `a b`, and keeping the first
    and discarding the rest is exactly their statement. `axSeqIdentityR` and
    `axSeqIdentityL` are `axCoopIdentity` verbatim.

    So the proof below inhabits both propositions from `axCoopComm` and
    `axCoopIdentity` alone, and `#print axioms` names those two and neither
    `axSeq`, `axCoop`, `axSeqIdentityR` nor `axSeqIdentityL`. Deleting those
    four declarations would leave every theorem in the development provable.

    What is left of the operation layer is `axCoopComm`, one identity clause,
    and `axSeqAsymm` --- whose antecedent nothing can discharge. Three
    declarations, one of them inert. FORM. -/
theorem commonWitnessesComeFromCommutativity :
    (∀ a b : Form, ∃ c : Form, (c ~~ a) ∧ (c ~~ b)) ∧
      (∀ a : Form, ∃ c : Form, (c ~~ a) ∧ (c =~ a)) := by
  refine ⟨fun a b => ?_, axCoopIdentity⟩
  obtain ⟨ca, _, ca_a, ca_b, _, _, _⟩ := axCoopComm a b
  exact ⟨ca, ca_a, ca_b⟩

-- Graduation status: FORM. L3 licensed.

-- ============================================================================
-- §VIII  L2 Self-Kernel
-- P_2 = 42 steps.  N_2_atomic = 3.  G_2 = 4.
-- FRAME residuals:
--   compositionLengthAdditiveClaim  — FRAME/L3 (Form-valued length arithmetic
--                                     only; the law is proved at
--                                     dEntryLengthAdditive)
--   congruentPath internals eval   — not a FRAME. `congruentPathInternals`
--                                     (L3 §VII) is independent of all 39
--                                     clauses; see
--                                     HypermathFullAxiomModel.
--                                     congruentPath_symmetry_independent.
--   simulation-pair-exists         — closed at L1, not at L3. The weak pair is
--                                     `Hypermath.simulationPairExists_L1`; the
--                                     nontrivial pair is refuted and survives as
--                                     `simulationPairExistsClaim`.
-- Steps 1-25, 32-37 and 39 are represented by the declarations above.
-- The `~=` steps live in QuadrilateralFiltration (L2, imported downstream):
--   step 8  relation(abstracted-path)          — AbstractedFrom, with `~=` notation
--   step 26 abstracted-path refl/symm          — abstractedRefl, abstractedSymm
--   step 27 congruent-path refines it          — congruentFromPathRefines
--   step 28 strictly weaker                    — abstractedNotCongruentAtCycle
--   step 29 evaluates inside L2                — quantaAdditive (rfl, no FRAME)
--   step 30 compose is a congruence for it     — DExpr.seq, retraceSeq
--   step 31 derives is abstraction tier        — derivesIsAbstractionOfDerivesIn (L1),
--                                                dExprToDerives, derivesLosesQuanta
--   step 38 close(abstracted-path), no FRAME   — AbstractedFrom is a def, not an axiom
-- ============================================================================

end Hypermath
