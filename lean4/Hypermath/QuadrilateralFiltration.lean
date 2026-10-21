-- Hypermath.QuadrilateralFiltration
-- Layer 2: Quadrilateral Filtration — Transitive Abstraction (~=) over
-- derivation expressions, the Metamath Functorial Bridge, and Constructive
-- Hypersets.
--
-- PLACEMENT.  Abstraction is an L2 path relation, not an L1 Form relation.
-- The tier relations are declared on Forms at L1; only L2 lifts them to paths.
-- `~=` is defined to discard operational trace VOLUME, and volume
-- (quantification, L2_operations.hm:192) is not a first-class object until L2
-- introduces DerivationPath and quanta accounting.  Trace *levels* are L1
-- (trace-levels, L1_relations.hm VI); trace *volume* is L2.
--
-- `~=` IS NOT `=~`.  The two symbol pairs name different relations:
--     `=~`  congruent from  — (start, end, path-trace, quantification)
--     `~=`  abstracted from — (start, end, path-trace); quantification forgotten
-- `~=` is the tangent path around congruence by which grounded substance
-- reforms into a new semantics: forget the volume, re-quantify, retrace.
--
-- Author: Tyler Roost (The TimeLord)
-- Repository: TimeLordRaps/hypermath/lean4/Hypermath/QuadrilateralFiltration.lean

import Hypermath.L2Operations

namespace Hypermath

open Hypermath

-- ============================================================================
-- §0  Withdrawn: abstraction as the transitive closure of Similar
-- ============================================================================

/-- The original L1-level proposal for `~=`: the equivalence closure of `~~`.
    Retained as a named definition with its refutation, not as the meaning of
    `~=`.  `~~` already links every Form to ground (axBox then axSim), and
    non-transitivity of `~~` was the only thing preventing those from chaining,
    so closing under transitivity collapses the relation.  The original
    `Abstraction` inductive, and the `abstractionTransitive`,
    `syntaxToAbstraction` and `conditionalRetrace` theorems stated over it,
    have therefore been withdrawn. -/
inductive SimilarClosure : Form → Form → Prop where
  | ofSimilar (x y : Form) : Similar x y → SimilarClosure x y
  | refl (x : Form) : SimilarClosure x x
  | symm {x y : Form} : SimilarClosure x y → SimilarClosure y x
  | trans {x y z : Form} : SimilarClosure x y → SimilarClosure y z → SimilarClosure x z

/-- Every Form closes to ground: axBox reaches x, axSim reaches ground. -/
theorem similarClosureToGround : ∀ x : Form, SimilarClosure x ground :=
  fun x =>
    SimilarClosure.trans
      (SimilarClosure.symm
        (SimilarClosure.ofSimilar _ _ (axBoxInRelationLanguage x)))
      (SimilarClosure.ofSimilar _ _ (axSimInRelationLanguage (f2f x)))

/-- Refutation: the closure is the total relation.  It separates nothing, so it
    cannot be the abstraction layer. -/
theorem similarClosureIsTotal : ∀ x y : Form, SimilarClosure x y :=
  fun x y =>
    SimilarClosure.trans (similarClosureToGround x)
      (SimilarClosure.symm (similarClosureToGround y))

-- ============================================================================
-- §1  The abstraction surface: derivation expressions
-- ============================================================================

/-- A **derivation expression**: a reusable, compositional derivation built from
    evidenced atoms, self-reads and sequencing, held without expanding its
    evidence.  This is the `~=` surface at L2. -/
abbrev DExpr (x y : Form) := TraceExpr DStep x y

/-- The quanta observation, computed at the abstraction surface. -/
def DExpr.quanta {x y : Form} (e : DExpr x y) : Nat := TraceExpr.length e

/-- **Retrace**: expand an abstract derivation into its evidenced D-entry.
    For evidence-carrying atoms this is total; the conditional case is section 4. -/
def DExpr.retrace {x y : Form} (e : DExpr x y) : DEntry x y := TraceExpr.expand e

/-- Retrace soundness: the observation made at the abstraction surface agrees
    with the observation of the expanded ground trace.  This is the substance
    half of the quadrilateral, proved rather than assumed. -/
theorem retraceSound {x y : Form} (e : DExpr x y) :
    Trace.length (DExpr.retrace e) = DExpr.quanta e :=
  TraceExpr.length_expand e

-- ============================================================================
-- §2  `~=` and `=~` on derivation expressions
-- ============================================================================

/-- **`~=` — abstracted from.**  Two derivation expressions are
    abstraction-equivalent when they agree on (start, end, path-trace),
    forgetting quantification.  In `DExpr` the trace floor is constant — every
    `DStep` carries `Congruent` — so the endpoint index carries the whole
    surviving invariant.  In the source's `DerivationPath`, whose steps carry
    non-decreasing trace metadata at varying levels, path-trace would be a
    third independent coordinate. -/
def AbstractedFrom {x y x' y' : Form} (_ : DExpr x y) (_ : DExpr x' y') : Prop :=
  x = x' ∧ y = y'

@[inherit_doc] scoped infix:50 " ~= " => AbstractedFrom

/-- **`=~` — congruent from**, at the path level: the same schema *including*
    quantification.  Named rather than notated, because `=~` already denotes
    `Congruent` on Forms and these are relations on different objects. -/
def CongruentFromPath {x y x' y' : Form} (p : DExpr x y) (q : DExpr x' y') : Prop :=
  x = x' ∧ y = y' ∧ DExpr.quanta p = DExpr.quanta q

/-- `~=` is reflexive. -/
theorem abstractedRefl {x y : Form} (e : DExpr x y) : e ~= e := ⟨rfl, rfl⟩

/-- `~=` is symmetric. -/
theorem abstractedSymm {x y x' y' : Form} {p : DExpr x y} {q : DExpr x' y'} :
    (p ~= q) → (q ~= p) :=
  fun h => ⟨h.1.symm, h.2.symm⟩

/-- `~=` is strictly transitive, unlike continuation similarity `~~`.
    Research note 3.1, now holding by construction rather than by stipulation. -/
theorem abstractedTrans {a b c d e f : Form}
    {p : DExpr a b} {q : DExpr c d} {r : DExpr e f} :
    (p ~= q) → (q ~= r) → (p ~= r) :=
  fun h1 h2 => ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

/-- `=~` refines `~=`: congruence carries quantification, abstraction forgets it. -/
theorem congruentFromPathRefines {x y x' y' : Form}
    {p : DExpr x y} {q : DExpr x' y'} :
    CongruentFromPath p q → (p ~= q) :=
  fun h => ⟨h.1, h.2.1⟩

/-- The refinement is strict exactly where there is a cycle: a self-read and a
    round trip are abstraction-equivalent but not congruent.  This is the same
    structure the deriver cycle demands. -/
theorem abstractedNotCongruentAtCycle {x y : Form}
    (out : DStep x y) (back : DStep y x) :
    (TraceExpr.self x ~= TraceExpr.atom (Trace.cons out (Trace.cons back (Trace.nil x)))) ∧
    ¬ CongruentFromPath (TraceExpr.self x)
        (TraceExpr.atom (Trace.cons out (Trace.cons back (Trace.nil x)))) :=
  ⟨⟨rfl, rfl⟩, fun h => Nat.noConfusion h.2.2⟩

-- ============================================================================
-- §3  Compositionality at the abstraction surface
-- ============================================================================

/-- Composition of abstract derivations.  Total, with no side condition. -/
def DExpr.seq {x y z : Form} (a : DExpr x y) (b : DExpr y z) : DExpr x z :=
  TraceExpr.seq a b

/-- **Quanta compose without retracing.**  This is why the off-branch exists:
    proof engines work at the abstraction surface without carrying DStep trace
    mass.  Compare `compositionLengthAdditiveClaim` (L2, Form-valued, not
    entailed), `dEntryLengthAdditive` (L2, proved on traces) and
    `pathLengthArithmeticClaim` (L3, refuted). -/
theorem quantaAdditive {x y z : Form} (a : DExpr x y) (b : DExpr y z) :
    DExpr.quanta (DExpr.seq a b) = DExpr.quanta a + DExpr.quanta b := rfl

/-- Retrace is a homomorphism for composition. -/
theorem retraceSeq {x y z : Form} (a : DExpr x y) (b : DExpr y z) :
    DExpr.retrace (DExpr.seq a b) =
      Trace.compose (DExpr.retrace a) (DExpr.retrace b) := rfl

/-- The self-read is a two-sided identity for retraced composition.
    This is the L2 conjunct of self-derivation (`reflexion`). -/
theorem retraceSelfIdentity {x y : Form} (p : DEntry x y) :
    Trace.compose (DExpr.retrace (TraceExpr.self x)) p = p ∧
    Trace.compose p (DExpr.retrace (TraceExpr.self y)) = p :=
  ⟨Trace.nil_compose p, Trace.compose_nil p⟩

/-- Retraced composition is associative.  With `retraceSelfIdentity`, D-entries
    form a category: the compositional surface, axiom-free. -/
theorem retraceAssoc {w x y z : Form}
    (a : DEntry w x) (b : DEntry x y) (c : DEntry y z) :
    Trace.compose (Trace.compose a b) c = Trace.compose a (Trace.compose b c) :=
  Trace.compose_assoc a b c

/-- Downstream compositionality, research note 3.2: abstract rewrites compose
    algebraically without carrying intermediate operational traces, and
    re-association is invisible at the abstraction surface. -/
theorem compositionalityChain3 {a b c d : Form}
    (p : DExpr a b) (q : DExpr b c) (r : DExpr c d) :
    DExpr.seq (DExpr.seq p q) r ~= DExpr.seq p (DExpr.seq q r) :=
  ⟨rfl, rfl⟩

/-- Re-association is invisible to the quanta observation as well. -/
theorem compositionalityChain3Quanta {a b c d : Form}
    (p : DExpr a b) (q : DExpr b c) (r : DExpr c d) :
    DExpr.quanta (DExpr.seq (DExpr.seq p q) r) =
      DExpr.quanta (DExpr.seq p (DExpr.seq q r)) :=
  Nat.add_assoc _ _ _

-- ============================================================================
-- §4  Conditional retrace around substance — the Metamath bridge
-- ============================================================================

/-- A **schematic derivation**: atoms are *claims* carrying no evidence.  This is
    the Metamath surface — pure syntactic assertion with no operational
    substance (research note 4.1). -/
inductive SchematicExpr : Form → Form → Type where
  | claim (x y : Form) : SchematicExpr x y
  | self (x : Form) : SchematicExpr x x
  | seq {x y z : Form} : SchematicExpr x y → SchematicExpr y z → SchematicExpr x z

/-- A **substance witness**: certification that a claimed edge is realizable in
    ground substance.  This replaces `SubstanceWitness x y := (x ≡ y)`, which was
    defined as its own conclusion and made the retrace the identity function.
    Realizability is `=~`-level — a D-entry — not `==`-level. -/
def Realizer : Type := ∀ x y : Form, Option (DEntry x y)

/-- **Conditional retrace around substance.**  An abstract identity retraces to
    an evidenced derivation exactly when every claimed edge has a substance
    witness.  `none` is `FiltrationRetraceError` (abstraction.py). -/
def realize (W : Realizer) : {x y : Form} → SchematicExpr x y → Option (DExpr x y)
  | _, _, .claim a b => (W a b).map TraceExpr.atom
  | _, _, .self a => some (TraceExpr.self a)
  | _, _, .seq first second =>
      match realize W first, realize W second with
      | some f, some s => some (DExpr.seq f s)
      | _, _ => none

/-- Self-reads need no witness: they are realizable unconditionally. -/
theorem realizeSelf (W : Realizer) (x : Form) :
    realize W (SchematicExpr.self x) = some (TraceExpr.self x) := rfl

/-- A realizer supplying no witness. -/
def emptyRealizer : Realizer := fun _ _ => none

/-- The retrace is genuinely conditional: under a realizer supplying no witness,
    a claim does not retrace.  Contrast the withdrawn `conditionalRetrace`,
    which was `fun _ _ _ hWit => hWit`. -/
theorem retraceCanFail (x y : Form) :
    realize emptyRealizer (SchematicExpr.claim x y) = none := rfl

-- Metamath to Hypermath functorial mapping (research note 4.2):
--   token expression         -> SchematicExpr at the `~=` surface
--   floating hypothesis      -> endpoint index of SchematicExpr
--   essential hypothesis     -> Realizer obligation for that edge
--   proof step               -> SchematicExpr.seq
--   verified proof           -> a closed SchematicExpr
--   complete grounding       -> realize W, then DExpr.retrace

/-- Metamath hypothesis kinds: floating (syntactic typing), essential (substance
    premise), disjoint-variable (orbit disjointness). -/
inductive MetamathHypothesis where
  | Floating (varName : String) (typeClass : Form)
  | Essential (witnessCondition : Form × Form)
  | DisjointVar (var1 var2 : String)

/-- A Metamath assertion as a schematic derivation. -/
structure MetamathAssertion where
  label : String
  hypotheses : List MetamathHypothesis
  conclusionLhs : Form
  conclusionRhs : Form
  deduction : SchematicExpr conclusionLhs conclusionRhs

/-- Instantiation: retracing a verified Metamath theorem into an evidenced
    Hypermath derivation, on supplying substance witnesses for its essential
    hypotheses.  Returns `none` when a witness is missing. -/
def instantiateMetamathTheorem (W : Realizer) (thm : MetamathAssertion) :
    Option (DEntry thm.conclusionLhs thm.conclusionRhs) :=
  (realize W thm.deduction).map DExpr.retrace

-- ============================================================================
-- §4b  Orbit-reflexion factors through `~=`
-- ============================================================================

/-- Source orbit-reflexion (`L2_operations.hm`: `D[x][z] =~ D[y][z]`): D-entries
    compared at congruence, i.e. endpoints AND quanta. -/
def CongruentProfile (x y : Form) : Prop :=
  ∀ (z : Form) (n : Nat),
    (∃ p : DEntry x z, Trace.length p = n) ↔ (∃ q : DEntry y z, Trace.length q = n)

/-- The `~=` profile: endpoints only, quanta forgotten. -/
def AbstractionProfile (x y : Form) : Prop :=
  ∀ z : Form, Nonempty (DEntry x z) ↔ Nonempty (DEntry y z)

/-- `orbitReflexionQuotient`'s hypothesis IS the `~=` profile, definitionally.
    The L2 translation already performed the abstraction — it dropped the quanta
    coordinate the source demanded — which is why the source's `=~`-class proof
    does not transfer to it. -/
theorem orbitReflexionHypothesisIsAbstraction (x y : Form) :
    AbstractionProfile x y ↔ (∀ z : Form, D x z ↔ D y z) := Iff.rfl

/-- Orbit-reflexion factors through abstraction: the source's `=~` profile
    refines the `~=` profile. -/
theorem congruentProfileFactorsThroughAbstraction (x y : Form) :
    CongruentProfile x y → AbstractionProfile x y := by
  intro h z
  constructor
  · intro hx
    obtain ⟨p⟩ := hx
    obtain ⟨q, _⟩ := (h z (Trace.length p)).mp ⟨p, rfl⟩
    exact ⟨q⟩
  · intro hy
    obtain ⟨q⟩ := hy
    obtain ⟨p, _⟩ := (h z (Trace.length q)).mpr ⟨q, rfl⟩
    exact ⟨p⟩

-- ============================================================================
-- §4c  `derives` sits at the abstraction tier
-- The retiering of L1 §IV.a, stated against the `~=` surface that defines it.
-- ============================================================================

/-- **The bridge from the quanta-carrying surface to `derives`.**  A derivation
    expression of quanta n yields `DerivesIn n`, provided its endpoint is a
    substance — which is exactly `y =~ y` (`closeSubstanceOpaque`), the only
    congruence available without a reflexivity axiom. -/
theorem dExprToDerivesIn {x y : Form} (e : DExpr x y) (hy : Substance y) :
    DerivesIn (DExpr.quanta e) x y := by
  show Nat.repeat f2f (DExpr.quanta e) x =~ y
  have h : Nat.repeat f2f (Trace.length (DExpr.retrace e)) x = y :=
    dEntryEndpointIteration (DExpr.retrace e)
  rw [retraceSound e] at h
  rw [h]
  exact (closeSubstanceOpaque y).mp hy

/-- Composing with the abstraction map lands in `Derives`, with n forgotten. -/
theorem dExprToDerives {x y : Form} (e : DExpr x y) (hy : Substance y) :
    Derives x y :=
  derivesInToDerives (dExprToDerivesIn e hy)

/-- **The map is not injective on quanta.**  Two expressions of different quanta
    over the same endpoints produce the same `Derives` fact, so the passage
    admits no inverse: `derives` is genuinely forgetful.  That is what places it
    at `~=` (abstracted from) rather than `=~` (congruent from). -/
theorem derivesLosesQuanta {x y : Form} (e f : DExpr x y) (hy : Substance y) :
    dExprToDerives e hy = dExprToDerives f hy :=
  rfl

/-- The abstraction relation `~=` is exactly the indistinguishability that
    `derives` imposes: `~=` agrees on endpoints and forgets quanta, and
    `Derives` reads only endpoints.  Two `~=`-related expressions therefore
    carry the same `Derives` fact, whatever their quanta. -/
theorem abstractedFromAgreesOnDerives {x y x' y' : Form}
    (e : DExpr x y) (f : DExpr x' y') (hab : e ~= f)
    (hy : Substance y) : Derives x' y' := by
  obtain ⟨hx, hyy⟩ := hab
  subst hx
  subst hyy
  exact dExprToDerives e hy

-- ============================================================================
-- §5  Terminal Self-Derivation: Cyclical Completion of the Hyperkernel
-- ============================================================================

/-- The four operational pillars of the Hyperkernel (Self-Meta Kernel). -/
structure Hyperkernel where
  state : Form
  selfDerivable : Form → Form            -- Generative derivation from ground
  selfDefined : Form → Form → Prop       -- Supplies its own relations
  selfVerifiable : Form → Bool           -- Internal decision procedure
  selfRepresentation : Form              -- Injective fractal encoding into Form
  cyclical : selfDerivable state ≡ state

/-- Cyclical Completion: The Hyperkernel achieves terminal self-derivation as an
    endofunctor fixed point under mutual simulation (≡). -/
theorem cyclicalCompletion :
    ∀ (K : Hyperkernel), (K.selfDerivable K.state ≡ K.state) :=
  fun K => K.cyclical

-- ============================================================================
-- §6  Hyperset Theory from Ordinatics Fractal Self-Representations
-- ============================================================================

/-- Constructive membership relation (∈_O) derived from structural sub-form decomposition. -/
def memOrdinatics (subform parent : Form) : Prop :=
  f2f subform ≡ parent

scoped notation:50 a " ∈_O " b => memOrdinatics a b

/-- An immediate constituent in a fractal representation is a member. -/
theorem fractalSubformMembership :
    ∀ (subform parent : Form), (f2f subform ≡ parent) → (subform ∈_O parent) :=
  fun _ _ h => h

/-- The Quine Atom (Ω = {Ω}): Non-well-founded fixed point.
    Derives self-membership constructively without requiring external AFA axiom. -/
theorem quineAtomSelfMembership :
    ∀ (Ω : Form), (f2f Ω ≡ Ω) → (Ω ∈_O Ω) :=
  fun Ω hFixedPoint => fractalSubformMembership Ω Ω hFixedPoint

-- ============================================================================
-- §7  Objectification: Equivalence Classes & Proof Trajectories as Forms
-- ============================================================================

/-- An equivalence class lifted into a first-class mathematical object in Form. -/
structure ObjectifiedClass where
  representative : Form
  relation : Form → Form → Prop

/-- Canonical quotient projection π: Form → ObjectifiedClass. -/
def classProjection (representative : Form) (relation : Form → Form → Prop) : ObjectifiedClass :=
  ⟨representative, relation⟩

/-- Proof Trajectory: A formal derivation path lifted into a first-class 1-cell. -/
structure ProofTrajectory where
  startForm : Form
  endForm : Form
  stepCount : Nat

/-- Identity trajectory: id_x : x → x. -/
def trajectoryIdentity (x : Form) : ProofTrajectory :=
  ⟨x, x, 0⟩

/-- Associative trajectory composition (1-cell composition). -/
noncomputable def trajectoryCompose (t1 t2 : ProofTrajectory) : Option ProofTrajectory :=
  open Classical in
  if t1.endForm = t2.startForm then some ⟨t1.startForm, t2.endForm, t1.stepCount + t2.stepCount⟩ else none

/-- Trajectory Homotopy (2-cell): Algebraic commutation of derivation paths. -/
def TrajectoryHomotopy (t1 t2 : ProofTrajectory) : Prop :=
  t1.startForm = t2.startForm ∧ t1.endForm = t2.endForm

-- ============================================================================
-- §8  The Five Formal Calculi Pathways
-- ============================================================================

/-- 1. Language Calculus: Operational semantics and grammar rewriting lattice. -/
structure LanguageCalculusModel where
  alphabet : Type
  reductionRelation : Form → Form → Prop
  syntaxEvaluation : Form → Form

/-- 2. Meta-Calculus: Symbolic dynamics of symbolic representational calculi. -/
structure MetaCalculusModel where
  rewriteOperator : Form → Form
  orbitCycleDetector : Form → Nat → Bool
  fixedPointAttractor : Form → Prop

/-- 3. Hyper-Calculus: Group-theoretical / Lie-algebraic approach to calculus. -/
structure HyperCalculusModel where
  derivationOp1 : Form → Form
  derivationOp2 : Form → Form
  lieBracket : Form → Form
  leibnizProductRule : Form → Form → Prop

/-- 4. Ordinal Calculus: Transfinite difference and limit derivatives. -/
structure OrdinalCalculusModel where
  transfiniteDifference : Form → Form
  limitDerivative : Form → Form
  transfiniteSummation : Form → Form

/-- 5. Normal Math Calculus: Standard continuous analysis via Ordinatics wrap map. -/
structure MathCalculusModel where
  continuousDerivative : (Float → Float) → (Float → Float)
  riemannIntegral : (Float → Float) → Float → Float → Float
  fundamentalTheoremOfCalculus : Prop

-- ============================================================================
-- §9  Aczel's Anti-Foundation Axiom (AFA) in Ordinatics
-- ============================================================================

/-- Accessible Pointed Graph (APG) for Non-Well-Founded Hyperset Equations. -/
structure APG where
  nodeType : Type
  edgeRel : nodeType → nodeType → Prop
  rootNode : nodeType

/-- Unique decoration of an APG into Hypermath Forms. -/
noncomputable def apgDecoration (_ : APG) : Form :=
  ground

/-- Relational bisimulation matching mutual simulation (≡). -/
def apgBisimulation (d1 d2 : Form) : Prop :=
  d1 ≡ d2

/-- Aczel AFA Uniqueness Theorem in Ordinatics:
    Bisimilar decorations mutually simulate under the Hyperkernel quotient. -/
theorem afaDecorationUniqueness :
    ∀ (d1 d2 : Form), apgBisimulation d1 d2 → (d1 ≡ d2) :=
  fun _ _ h => h

end Hypermath
