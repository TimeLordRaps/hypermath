import Hypermath.Trace

/- Finite countermodels to selected claimed consequences of the L0/L1 axiom
   clauses. Only the generic constructive Trace implementation is imported;
   no production Form parameters or logical axioms are used. The Bool model
   tests reverse filtration, directionality, and the promised endpoint cycle.
   The separate Fin 3 model tests the now-defined congruence-preserving D.
   Neither model covers every later L2/L3 clause or establishes consistency
   of the intended complete theory. There are no admitted proofs here. -/

namespace HypermathCountermodel

def ground : Bool := false
def f2f (_ : Bool) : Bool := true
def Similar (_ _ : Bool) : Prop := True
def Congruent (_ _ : Bool) : Prop := True
def Simulation (x y : Bool) : Prop := x = y
def structContinues (_ _ : Bool) : Prop := True
def structDistinct (x y : Bool) : Prop := ¬ Simulation x y
def structOrbits (_ _ : Bool) : Prop := True
def HMSyntax (_ : Bool) : Prop := True
def Substance (_ : Bool) : Prop := True
def Semantics (_ : Bool) : Prop := True
def FormClosure (_ : Bool) : Prop := True
def Derives (_ _ : Bool) : Prop := True
def Discharge (_ _ : Bool) : Prop := True
def Definition (_ _ : Bool) : Prop := True
def deriver : Bool := false

/-- All 24 logical axiom clauses of L0Ground and L1Relations, with Bool
    replacing their uninterpreted Form parameter. Theorems admitted with
    sorry are deliberately not treated as axioms of this model. -/
structure PrefixAxioms : Prop where
  axDiff : ∀ x, structDistinct (f2f x) ground
  axSim : ∀ x, structContinues (f2f x) ground
  axBox : ∀ x, structOrbits (f2f (f2f x)) x
  axGroundSelf : structContinues ground ground
  closeStructContinues : ∀ x, structContinues x ground ↔ Similar x ground
  closeStructDistinct : ∀ x y, structDistinct x y ↔ ¬ Simulation x y
  closeStructOrbits : ∀ x, structOrbits (f2f (f2f x)) x ↔ Similar (f2f (f2f x)) x
  axSyntaxRequiresSubstance : ∀ x, HMSyntax x → Substance x
  axSubstanceRequiresSemantics : ∀ x, Substance x → Semantics x
  axSemanticsRequiresSyntax : ∀ x, Semantics x → HMSyntax x
  axFormClosesLoop : ∀ x, HMSyntax x → Semantics x → FormClosure x
  axGroundSyntaxAx : HMSyntax ground
  axGroundSubstanceAx : Substance ground
  axGroundSemanticsAx : Semantics ground
  filtrationSimCong : ∀ x y, Simulation x y → Congruent x y
  filtrationCongSim : ∀ x y, Congruent x y → Similar x y
  closeSyntaxOpaque : ∀ x, HMSyntax x ↔ ∃ n : Nat, Similar (Nat.repeat f2f n ground) x
  closeSubstanceOpaque : ∀ x, Substance x ↔ Congruent x x
  closeSemanticsOpaque : ∀ x, Semantics x ↔ Simulation x x
  closeDerivesOpaque : ∀ x y, Derives x y ↔ ∃ n : Nat, Congruent (Nat.repeat f2f n x) y
  closeDischargeOpaque : ∀ c e, Discharge c e ↔ Derives e c
  closeDefinitionOpaque : ∀ n x, Definition n x ↔ Derives n x
  closeFormClosureOpaque : ∀ x, FormClosure x ↔ HMSyntax x ∧ Substance x ∧ Semantics x
  traceLevels : ∀ x, Similar (f2f x) x ∧
    (Congruent (f2f x) x → Similar (f2f x) x) ∧
    (Simulation (f2f x) x → Congruent (f2f x) x)

theorem prefixAxioms_hold : PrefixAxioms := by
  constructor <;> simp [ground, f2f, Similar, Congruent, Simulation,
    structContinues, structDistinct, structOrbits, HMSyntax, Substance,
    Semantics, FormClosure, Derives, Discharge, Definition]

/-- The premise claimed for axSeqAsymm is not supplied by axDiff. -/
theorem reverse_filtration_fails :
    ¬ Simulation (f2f ground) ground ∧ Congruent (f2f ground) ground := by
  simp [Simulation, Congruent, f2f, ground]

/-- Derives can be symmetric while all prefix axiom clauses hold. -/
theorem directionality_claim_fails :
    ¬ (¬ ∀ x y : Bool, Derives x y → Derives y x) := by
  simp [Derives]

/-- The prefix does not provide the promised simulation cycle. -/
theorem driver_cycle_claim_fails : ¬ Simulation (f2f (f2f deriver)) deriver := by
  simp [Simulation, f2f, deriver]

namespace PreservingTrace

/-- Three Forms with an exact two-step cycle away from ground. -/
def ground : Fin 3 := 0
def f2f (x : Fin 3) : Fin 3 := if x = 1 then 2 else 1
def Similar (_ _ : Fin 3) : Prop := True
def Congruent (x y : Fin 3) : Prop := x = y
def Simulation (x y : Fin 3) : Prop := x = y
def structContinues (_ _ : Fin 3) : Prop := True
def structDistinct (x y : Fin 3) : Prop := ¬ Simulation x y
def structOrbits (_ _ : Fin 3) : Prop := True
def HMSyntax (_ : Fin 3) : Prop := True
def Substance (_ : Fin 3) : Prop := True
def Semantics (_ : Fin 3) : Prop := True
def FormClosure (_ : Fin 3) : Prop := True
def Derives (x y : Fin 3) : Prop := ∃ n : Nat, Congruent (Nat.repeat f2f n x) y
def Discharge (c e : Fin 3) : Prop := Derives e c
def Definition (n x : Fin 3) : Prop := Derives n x
def deriver : Fin 3 := 1

/-- The same 24 logical prefix clauses, interpreted on Fin 3. In particular,
    Derives has its stipulated finite endpoint-reachability interpretation;
    it is not silently identified with the stricter edge-preserving D. -/
structure PrefixAxioms : Prop where
  axDiff : ∀ x, structDistinct (f2f x) ground
  axSim : ∀ x, structContinues (f2f x) ground
  axBox : ∀ x, structOrbits (f2f (f2f x)) x
  axGroundSelf : structContinues ground ground
  closeStructContinues : ∀ x, structContinues x ground ↔ Similar x ground
  closeStructDistinct : ∀ x y, structDistinct x y ↔ ¬ Simulation x y
  closeStructOrbits : ∀ x, structOrbits (f2f (f2f x)) x ↔ Similar (f2f (f2f x)) x
  axSyntaxRequiresSubstance : ∀ x, HMSyntax x → Substance x
  axSubstanceRequiresSemantics : ∀ x, Substance x → Semantics x
  axSemanticsRequiresSyntax : ∀ x, Semantics x → HMSyntax x
  axFormClosesLoop : ∀ x, HMSyntax x → Semantics x → FormClosure x
  axGroundSyntaxAx : HMSyntax ground
  axGroundSubstanceAx : Substance ground
  axGroundSemanticsAx : Semantics ground
  filtrationSimCong : ∀ x y, Simulation x y → Congruent x y
  filtrationCongSim : ∀ x y, Congruent x y → Similar x y
  closeSyntaxOpaque : ∀ x, HMSyntax x ↔ ∃ n : Nat, Similar (Nat.repeat f2f n ground) x
  closeSubstanceOpaque : ∀ x, Substance x ↔ Congruent x x
  closeSemanticsOpaque : ∀ x, Semantics x ↔ Simulation x x
  closeDerivesOpaque : ∀ x y, Derives x y ↔ ∃ n : Nat, Congruent (Nat.repeat f2f n x) y
  closeDischargeOpaque : ∀ c e, Discharge c e ↔ Derives e c
  closeDefinitionOpaque : ∀ n x, Definition n x ↔ Derives n x
  closeFormClosureOpaque : ∀ x, FormClosure x ↔ HMSyntax x ∧ Substance x ∧ Semantics x
  traceLevels : ∀ x, Similar (f2f x) x ∧
    (Congruent (f2f x) x → Similar (f2f x) x) ∧
    (Simulation (f2f x) x → Congruent (f2f x) x)

theorem prefixAxioms_hold : PrefixAxioms := by
  constructor <;> simp [ground, f2f, Similar, Congruent, Simulation,
    structContinues, structDistinct, structOrbits, HMSyntax, Substance,
    Semantics, FormClosure, Derives, Discharge, Definition]
  all_goals decide

/-- Exactly the production DStep shape, with this model's operations. -/
def DStep (x y : Fin 3) : Prop := y = f2f x ∧ Congruent y x
abbrev DEntry (x y : Fin 3) := Hypermath.Trace DStep x y
def D (x y : Fin 3) : Prop := Nonempty (DEntry x y)

theorem no_congruent_step : ∀ x : Fin 3, ¬ Congruent (f2f x) x := by
  unfold Congruent f2f
  decide

theorem no_step {x y : Fin 3} (edge : DStep x y) : False := by
  exact no_congruent_step x (edge.1 ▸ edge.2)

/-- Zero-step reflexivity survives; every positive step is excluded by evidence. -/
theorem trace_is_zero {x y : Fin 3} (path : DEntry x y) :
    x = y ∧ path.length = 0 := by
  cases path with
  | nil _ => exact ⟨rfl, rfl⟩
  | cons edge _ => exact False.elim (no_step edge)

theorem d_iff_equal (x y : Fin 3) : D x y ↔ x = y := by
  constructor
  · intro ⟨path⟩
    exact (trace_is_zero path).1
  · intro h
    subst y
    exact ⟨Hypermath.Trace.nil x⟩

end PreservingTrace

/-- The preserving-trace countermodel satisfies all 24 logical prefix clauses. -/
theorem preserving_prefix_axioms_hold : PreservingTrace.PrefixAxioms :=
  PreservingTrace.prefixAxioms_hold

/-- The actual trace-defined D need not span ground, despite the prefix axioms. -/
theorem d_spans_ground_claim_fails :
    ¬ (∀ y : Fin 3, PreservingTrace.D PreservingTrace.ground y) := by
  intro spans
  have impossible := (PreservingTrace.d_iff_equal PreservingTrace.ground 1).mp (spans 1)
  exact (by decide : PreservingTrace.ground ≠ (1 : Fin 3)) impossible

/-- Even exact endpoint simulation after two applications does not supply a
    positive-length congruence-preserving trace through the intermediate Form. -/
theorem driver_endpoint_cycle_without_positive_trace :
    PreservingTrace.Simulation
      (PreservingTrace.f2f (PreservingTrace.f2f PreservingTrace.deriver))
      PreservingTrace.deriver ∧
    ¬ (∃ path : PreservingTrace.DEntry PreservingTrace.deriver PreservingTrace.deriver,
      0 < path.length) := by
  constructor
  · unfold PreservingTrace.Simulation PreservingTrace.f2f PreservingTrace.deriver
    decide
  · intro ⟨path, positive⟩
    rw [(PreservingTrace.trace_is_zero path).2] at positive
    exact Nat.not_lt_zero _ positive

namespace IrreflexiveSimilar

/-- A third model, over two disjoint chains, testing whether the L0/L1 clauses
force `Similar` to be reflexive. The second coordinate carries a chain that the
ground chain never reaches; `isolated` heads it. `Similar` holds of everything
except `isolated`, and of `isolated` only from the later members of its own
chain -- never from `isolated` itself, because `isolated` has no predecessor to
be the image of. Every clause below still holds. -/
abbrev Form := Nat × Bool
def ground : Form := (0, false)
def isolated : Form := (0, true)
def f2f (x : Form) : Form := (x.1 + 1, x.2)
def Similar (x y : Form) : Prop := y ≠ isolated ∨ (x.2 = true ∧ 1 ≤ x.1)
def Congruent (x y : Form) : Prop := x = y ∧ y ≠ isolated
def Simulation (x y : Form) : Prop := x = y ∧ y ≠ isolated
def structContinues (x y : Form) : Prop := Similar x y
def structDistinct (x y : Form) : Prop := ¬ Simulation x y
def structOrbits (x y : Form) : Prop := Similar x y
def HMSyntax (x : Form) : Prop := x ≠ isolated
def Substance (x : Form) : Prop := x ≠ isolated
def Semantics (x : Form) : Prop := x ≠ isolated
def FormClosure (x : Form) : Prop := HMSyntax x ∧ Substance x ∧ Semantics x
def Derives (x y : Form) : Prop := ∃ n : Nat, Congruent (Nat.repeat f2f n x) y
def Discharge (c e : Form) : Prop := Derives e c
def Definition (n x : Form) : Prop := Derives n x

theorem repeat_value (n : Nat) (x : Form) : Nat.repeat f2f n x = (x.1 + n, x.2) := by
  induction n with
  | zero => cases x; rfl
  | succ n ih => simp only [Nat.repeat, ih, f2f, Nat.add_assoc]

/-- Nothing on the ground chain is similar to `isolated`: the escape clause
asks for a true second coordinate, and the ground chain's is false. -/
theorem ground_chain_misses_isolated (n : Nat) :
    ¬ Similar (Nat.repeat f2f n ground) isolated := by
  rw [repeat_value]
  rintro (h | ⟨h, _⟩)
  · exact h rfl
  · exact Bool.noConfusion h

/-- The same 24 logical prefix clauses, interpreted on two chains. -/
structure PrefixAxioms : Prop where
  axDiff : ∀ x, structDistinct (f2f x) ground
  axSim : ∀ x, structContinues (f2f x) ground
  axBox : ∀ x, structOrbits (f2f (f2f x)) x
  axGroundSelf : structContinues ground ground
  closeStructContinues : ∀ x, structContinues x ground ↔ Similar x ground
  closeStructDistinct : ∀ x y, structDistinct x y ↔ ¬ Simulation x y
  closeStructOrbits : ∀ x, structOrbits (f2f (f2f x)) x ↔ Similar (f2f (f2f x)) x
  axSyntaxRequiresSubstance : ∀ x, HMSyntax x → Substance x
  axSubstanceRequiresSemantics : ∀ x, Substance x → Semantics x
  axSemanticsRequiresSyntax : ∀ x, Semantics x → HMSyntax x
  axFormClosesLoop : ∀ x, HMSyntax x → Semantics x → FormClosure x
  axGroundSyntaxAx : HMSyntax ground
  axGroundSubstanceAx : Substance ground
  axGroundSemanticsAx : Semantics ground
  filtrationSimCong : ∀ x y, Simulation x y → Congruent x y
  filtrationCongSim : ∀ x y, Congruent x y → Similar x y
  closeSyntaxOpaque : ∀ x, HMSyntax x ↔ ∃ n : Nat, Similar (Nat.repeat f2f n ground) x
  closeSubstanceOpaque : ∀ x, Substance x ↔ Congruent x x
  closeSemanticsOpaque : ∀ x, Semantics x ↔ Simulation x x
  closeDerivesOpaque : ∀ x y, Derives x y ↔ ∃ n : Nat, Congruent (Nat.repeat f2f n x) y
  closeDischargeOpaque : ∀ c e, Discharge c e ↔ Derives e c
  closeDefinitionOpaque : ∀ n x, Definition n x ↔ Derives n x
  closeFormClosureOpaque : ∀ x, FormClosure x ↔ HMSyntax x ∧ Substance x ∧ Semantics x
  traceLevels : ∀ x, Similar (f2f x) x ∧
    (Congruent (f2f x) x → Similar (f2f x) x) ∧
    (Simulation (f2f x) x → Congruent (f2f x) x)

/-- Every form is similar to its own second and further images, whatever its
chain: the image carries the same second coordinate and a positive first one. -/
theorem similar_from_image (k : Nat) (x : Form) :
    Similar (x.1 + k + 1, x.2) x := by
  cases hx : x.2 with
  | false =>
      refine Or.inl ?_
      intro collapse
      rw [collapse] at hx
      exact Bool.noConfusion hx
  | true => exact Or.inr ⟨rfl, Nat.le_add_left 1 (x.1 + k)⟩

theorem prefixAxioms_hold : PrefixAxioms where
  axDiff := by
    rintro x ⟨h, _⟩
    exact Nat.succ_ne_zero x.1 (congrArg Prod.fst h)
  axSim := fun _ => Or.inl (by intro h; exact Bool.noConfusion (congrArg Prod.snd h))
  axBox := fun x => similar_from_image 1 x
  axGroundSelf := Or.inl (by intro h; exact Bool.noConfusion (congrArg Prod.snd h))
  closeStructContinues := fun _ => Iff.rfl
  closeStructDistinct := fun _ _ => Iff.rfl
  closeStructOrbits := fun _ => Iff.rfl
  axSyntaxRequiresSubstance := fun _ h => h
  axSubstanceRequiresSemantics := fun _ h => h
  axSemanticsRequiresSyntax := fun _ h => h
  axFormClosesLoop := fun _ syn sem => ⟨syn, sem, sem⟩
  axGroundSyntaxAx := by intro h; exact Bool.noConfusion (congrArg Prod.snd h)
  axGroundSubstanceAx := by intro h; exact Bool.noConfusion (congrArg Prod.snd h)
  axGroundSemanticsAx := by intro h; exact Bool.noConfusion (congrArg Prod.snd h)
  filtrationSimCong := fun _ _ h => h
  filtrationCongSim := fun _ _ h => Or.inl h.2
  closeSyntaxOpaque := fun x => ⟨fun h => ⟨0, Or.inl h⟩, fun ⟨n, h⟩ away =>
    ground_chain_misses_isolated n (away ▸ h)⟩
  closeSubstanceOpaque := fun x => ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  closeSemanticsOpaque := fun x => ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  closeDerivesOpaque := fun _ _ => Iff.rfl
  closeDischargeOpaque := fun _ _ => Iff.rfl
  closeDefinitionOpaque := fun _ _ => Iff.rfl
  closeFormClosureOpaque := fun _ => Iff.rfl
  traceLevels := fun x =>
    ⟨similar_from_image 0 x, fun _ => similar_from_image 0 x, fun h =>
      absurd (congrArg Prod.fst h.1) (Nat.succ_ne_self x.1)⟩

/-- The single fact the refutations below rest on. `isolated` heads its chain,
so nothing in the chain precedes it, and the escape clause is empty there. -/
theorem isolated_not_similar_to_itself : ¬ Similar isolated isolated := by
  rintro (h | ⟨_, positive⟩)
  · exact h rfl
  · exact Nat.not_succ_le_zero 0 positive

/-- **`Similar` is not reflexive here.** -/
theorem similar_reflexive_claim_fails : ¬ ∀ x : Form, Similar x x :=
  fun reflexive => isolated_not_similar_to_itself (reflexive isolated)

/-- **No column quotient lands at `Similar`, for any relation at all.**
A clause of the shape "forms with the same R-column are similar" has a
reflexive antecedent, so at `x = y = isolated` it asserts exactly the
reflexivity this model denies. The relation is universally quantified: no
choice of derivation matrix, and no finiteness argument about one, can rescue
the shape. `Hypermath.orbitReflexionQuotient` has this shape with `R := D`. -/
theorem column_quotient_claim_fails (R : Form → Form → Prop) :
    ¬ ∀ x y : Form, (∀ z : Form, R x z ↔ R y z) → Similar x y :=
  fun quotient =>
    isolated_not_similar_to_itself (quotient isolated isolated (fun _ => Iff.rfl))

/-- **`Similar` is not symmetric here.** Ground is similar to nothing on the
other chain's head, while that head is similar to ground. -/
theorem similar_symmetric_claim_fails :
    ¬ ∀ x y : Form, Similar x y → Similar y x := by
  intro symmetric
  rcases symmetric isolated ground (Or.inl (by
    intro h; exact Bool.noConfusion (congrArg Prod.snd h))) with h | ⟨h, _⟩
  · exact h rfl
  · exact Bool.noConfusion h

/-- A Form one step along the second chain. It is not `isolated`, so everything
is similar to it; and it is a later member of `isolated`'s chain, so it is
similar to `isolated`. Those two facts do not compose. -/
def offChain : Form := (1, true)

theorem ground_similar_offChain : Similar ground offChain :=
  Or.inl (fun h => Nat.one_ne_zero (congrArg Prod.fst h))

theorem offChain_similar_isolated : Similar offChain isolated :=
  Or.inr ⟨rfl, Nat.le_refl 1⟩

theorem ground_not_similar_isolated : ¬ Similar ground isolated := by
  rintro (h | ⟨h, _⟩)
  · exact h rfl
  · exact Bool.noConfusion h

/-- **`Similar` is not transitive here.** ground ~~ offChain ~~ isolated, and
not ground ~~ isolated. Transitivity fails for the same reason reflexivity
does: the escape clause that lets the second chain reach its own head is a
statement about the *left* argument, so it is not carried along a composition
that starts on the ground chain. -/
theorem similar_transitive_claim_fails :
    ¬ ∀ x y z : Form, Similar x y → Similar y z → Similar x z :=
  fun transitive =>
    ground_not_similar_isolated
      (transitive ground offChain isolated ground_similar_offChain
        offChain_similar_isolated)

/-- **`=~` is not reflexive here.** -/
theorem congruent_reflexive_claim_fails : ¬ ∀ x : Form, Congruent x x :=
  fun reflexive => (reflexive isolated).2 rfl

/-- **`≡` is not reflexive here.** -/
theorem simulation_reflexive_claim_fails : ¬ ∀ x : Form, Simulation x x :=
  fun reflexive => (reflexive isolated).2 rfl

/-- **The open side of `Hypermath.globalCongruentReflexivityIsCofinality`.**
That theorem proves, from the clauses alone, that `=~` is reflexive everywhere
exactly when the ground chain is `~~`-cofinal in `Form`. This model satisfies
every clause and is not cofinal --- `isolated` heads a chain of its own --- so
neither side holds, and both upper reflexivities fail together, exactly as
`Hypermath.reflexivityLevelsCoincide` says they must. Reflexivity of `=~` and
of `≡` is therefore not a missing lemma about either relation. It is the
unstated assumption that forming from ground reaches everything. -/
theorem congruent_reflexivity_fails_with_unreached_form :
    PrefixAxioms ∧ (¬ ∀ x : Form, Congruent x x) ∧
      (¬ ∀ x : Form, Simulation x x) ∧
      ¬ ∃ n : Nat, Similar (Nat.repeat f2f n ground) isolated :=
  ⟨prefixAxioms_hold, congruent_reflexive_claim_fails,
    simulation_reflexive_claim_fails,
    fun ⟨n, similar⟩ => ground_chain_misses_isolated n similar⟩

/-- One certificate: every L0 and L1 logical clause holds, and both relation
properties that L1 states as its first two derives fail. They are therefore not
consequences of the clauses, and no later layer can supply them. -/
theorem prefix_without_reflexive_or_symmetric_similar :
    PrefixAxioms ∧ (¬ ∀ x : Form, Similar x x) ∧
      (¬ ∀ x y : Form, Similar x y → Similar y x) ∧
      (∀ R : Form → Form → Prop,
        ¬ ∀ x y : Form, (∀ z : Form, R x z ↔ R y z) → Similar x y) :=
  ⟨prefixAxioms_hold, similar_reflexive_claim_fails, similar_symmetric_claim_fails,
    column_quotient_claim_fails⟩

/-- **Reflexivity of `~~` is independent of the 24 L0 and L1 clauses.** The Bool
model reads `Similar` as `True`, which is reflexive; this one denies it at
`isolated`. Both satisfy every clause of the prefix.

The admission this settles is `L1Relations.similarReflexive`. It had a witness
for the failing side and none named for the satisfying side, so the status
`independent` in the clause-independence table was carried by prose. One
satisfying model and one refuting model are what independence is; naming only
the refuting one records a countermodel and calls it independence. -/
theorem similar_reflexivity_independent :
    (HypermathCountermodel.PrefixAxioms ∧ ∀ x : Bool, HypermathCountermodel.Similar x x) ∧
    (PrefixAxioms ∧ ¬ ∀ x : Form, Similar x x) :=
  ⟨⟨HypermathCountermodel.prefixAxioms_hold, fun _ => trivial⟩,
   ⟨prefixAxioms_hold, similar_reflexive_claim_fails⟩⟩

/-- **Symmetry of `~~` is independent of the same 24 clauses**, and for the same
reason: `True` is symmetric and this model is not. Settles
`L1Relations.similarSymmetric`. -/
theorem similar_symmetry_independent :
    (HypermathCountermodel.PrefixAxioms ∧
      ∀ x y : Bool, HypermathCountermodel.Similar x y → HypermathCountermodel.Similar y x) ∧
    (PrefixAxioms ∧ ¬ ∀ x y : Form, Similar x y → Similar y x) :=
  ⟨⟨HypermathCountermodel.prefixAxioms_hold, fun _ _ _ => trivial⟩,
   ⟨prefixAxioms_hold, similar_symmetric_claim_fails⟩⟩

end IrreflexiveSimilar


namespace AsymmetricCongruent

/-- A fourth model family, testing what the L0/L1 clauses force `=~` to be.
Three clauses constrain `Congruent`: `filtrationSimCong` and the third conjunct
of `traceLevels` bound it below by `Simulation`, `filtrationCongSim` bounds it
above by `Similar`, and `closeSubstanceOpaque` fixes its diagonal. Read
`Simulation` as equality and `Similar` as `True` and the lower and upper bounds
become equality and everything, with the diagonal already included. So the
clauses admit *any* relation containing equality: the model is parameterised by
an arbitrary `E`, and the symmetry failure is one instance of that. -/
abbrev Form := Nat
def ground : Form := 0
def f2f (x : Form) : Form := x + 1
def Similar (_ _ : Form) : Prop := True
def Simulation (x y : Form) : Prop := x = y
/-- Equality together with an arbitrary relation `E`. -/
def Congruent (E : Form → Form → Prop) (x y : Form) : Prop := x = y ∨ E x y
def structContinues (_ _ : Form) : Prop := True
def structDistinct (x y : Form) : Prop := ¬ Simulation x y
def structOrbits (_ _ : Form) : Prop := True
def HMSyntax (_ : Form) : Prop := True
def Substance (_ : Form) : Prop := True
def Semantics (_ : Form) : Prop := True
def FormClosure (_ : Form) : Prop := True
def Derives (E : Form → Form → Prop) (x y : Form) : Prop :=
  ∃ n : Nat, Congruent E (Nat.repeat f2f n x) y
def Discharge (E : Form → Form → Prop) (c e : Form) : Prop := Derives E e c
def Definition (E : Form → Form → Prop) (n x : Form) : Prop := Derives E n x

/-- The same 24 logical prefix clauses, with `=~` read as equality plus `E`. -/
structure PrefixAxioms (E : Form → Form → Prop) : Prop where
  axDiff : ∀ x, structDistinct (f2f x) ground
  axSim : ∀ x, structContinues (f2f x) ground
  axBox : ∀ x, structOrbits (f2f (f2f x)) x
  axGroundSelf : structContinues ground ground
  closeStructContinues : ∀ x, structContinues x ground ↔ Similar x ground
  closeStructDistinct : ∀ x y, structDistinct x y ↔ ¬ Simulation x y
  closeStructOrbits : ∀ x, structOrbits (f2f (f2f x)) x ↔ Similar (f2f (f2f x)) x
  axSyntaxRequiresSubstance : ∀ x, HMSyntax x → Substance x
  axSubstanceRequiresSemantics : ∀ x, Substance x → Semantics x
  axSemanticsRequiresSyntax : ∀ x, Semantics x → HMSyntax x
  axFormClosesLoop : ∀ x, HMSyntax x → Semantics x → FormClosure x
  axGroundSyntaxAx : HMSyntax ground
  axGroundSubstanceAx : Substance ground
  axGroundSemanticsAx : Semantics ground
  filtrationSimCong : ∀ x y, Simulation x y → Congruent E x y
  filtrationCongSim : ∀ x y, Congruent E x y → Similar x y
  closeSyntaxOpaque : ∀ x, HMSyntax x ↔ ∃ n : Nat, Similar (Nat.repeat f2f n ground) x
  closeSubstanceOpaque : ∀ x, Substance x ↔ Congruent E x x
  closeSemanticsOpaque : ∀ x, Semantics x ↔ Simulation x x
  closeDerivesOpaque : ∀ x y, Derives E x y ↔ ∃ n : Nat, Congruent E (Nat.repeat f2f n x) y
  closeDischargeOpaque : ∀ c e, Discharge E c e ↔ Derives E e c
  closeDefinitionOpaque : ∀ n x, Definition E n x ↔ Derives E n x
  closeFormClosureOpaque : ∀ x, FormClosure x ↔ HMSyntax x ∧ Substance x ∧ Semantics x
  traceLevels : ∀ x, Similar (f2f x) x ∧
    (Congruent E (f2f x) x → Similar (f2f x) x) ∧
    (Simulation (f2f x) x → Congruent E (f2f x) x)

/-- **`=~` is free above equality.** Every clause holds for every choice of `E`.
The proof never mentions `E`: each field either ignores `Congruent` or uses only
`Or.inl`, the inclusion of equality. -/
theorem prefixAxioms_hold (E : Form → Form → Prop) : PrefixAxioms E where
  axDiff := fun x h => Nat.succ_ne_zero x h
  axSim := fun _ => trivial
  axBox := fun _ => trivial
  axGroundSelf := trivial
  closeStructContinues := fun _ => Iff.rfl
  closeStructDistinct := fun _ _ => Iff.rfl
  closeStructOrbits := fun _ => Iff.rfl
  axSyntaxRequiresSubstance := fun _ _ => trivial
  axSubstanceRequiresSemantics := fun _ _ => trivial
  axSemanticsRequiresSyntax := fun _ _ => trivial
  axFormClosesLoop := fun _ _ _ => trivial
  axGroundSyntaxAx := trivial
  axGroundSubstanceAx := trivial
  axGroundSemanticsAx := trivial
  filtrationSimCong := fun _ _ h => Or.inl h
  filtrationCongSim := fun _ _ _ => trivial
  closeSyntaxOpaque := fun _ => ⟨fun _ => ⟨0, trivial⟩, fun _ => trivial⟩
  closeSubstanceOpaque := fun _ => ⟨fun _ => Or.inl rfl, fun _ => trivial⟩
  closeSemanticsOpaque := fun _ => ⟨fun _ => rfl, fun _ => trivial⟩
  closeDerivesOpaque := fun _ _ => Iff.rfl
  closeDischargeOpaque := fun _ _ => Iff.rfl
  closeDefinitionOpaque := fun _ _ => Iff.rfl
  closeFormClosureOpaque := fun _ => ⟨fun _ => ⟨trivial, trivial, trivial⟩, fun _ => trivial⟩
  traceLevels := fun x =>
    ⟨trivial, fun _ => trivial, fun h => absurd h (Nat.succ_ne_self x)⟩

/-- One ordered pair, without its converse. -/
def asym (x y : Form) : Prop := x = 1 ∧ y = 0

/-- Two composable pairs, without their composite. -/
def skip (x y : Form) : Prop := (x = 2 ∧ y = 1) ∨ (x = 1 ∧ y = 0)

/-- **`=~` is not symmetric here.** `1 =~ 0` holds and `0 =~ 1` does not. -/
theorem congruent_symmetry_claim_fails :
    ¬ ∀ x y : Form, Congruent asym x y → Congruent asym y x := by
  intro symmetric
  rcases symmetric 1 0 (Or.inr ⟨rfl, rfl⟩) with h | ⟨h, _⟩ <;>
    exact absurd h (by decide)

/-- **`=~` is not transitive here.** `2 =~ 1` and `1 =~ 0` hold, `2 =~ 0` does
not. Transitivity and symmetry are independent for the same reason and are not
two findings: neither is a consequence of "contains equality". -/
theorem congruent_transitivity_claim_fails :
    ¬ ∀ x y z : Form, Congruent skip x y → Congruent skip y z → Congruent skip x z := by
  intro transitive
  rcases transitive 2 1 0 (Or.inr (Or.inl ⟨rfl, rfl⟩)) (Or.inr (Or.inr ⟨rfl, rfl⟩)) with
    h | (⟨_, h⟩ | ⟨h, _⟩) <;> exact absurd h (by decide)

/-- Symmetry of `=~` is independent of the 24 L0 and L1 clauses: the Bool model
reads `Congruent` as `True`, which is symmetric, and this one does not. -/
theorem congruent_symmetry_independent :
    (HypermathCountermodel.PrefixAxioms ∧
      ∀ x y : Bool, HypermathCountermodel.Congruent x y →
        HypermathCountermodel.Congruent y x) ∧
    (PrefixAxioms asym ∧ ¬ ∀ x y : Form, Congruent asym x y → Congruent asym y x) :=
  ⟨⟨HypermathCountermodel.prefixAxioms_hold, fun _ _ _ => trivial⟩,
   ⟨prefixAxioms_hold asym, congruent_symmetry_claim_fails⟩⟩

/-- Transitivity of `=~` is independent on the same grounds. -/
theorem congruent_transitivity_independent :
    (HypermathCountermodel.PrefixAxioms ∧
      ∀ x y z : Bool, HypermathCountermodel.Congruent x y →
        HypermathCountermodel.Congruent y z → HypermathCountermodel.Congruent x z) ∧
    (PrefixAxioms skip ∧
      ¬ ∀ x y z : Form, Congruent skip x y → Congruent skip y z → Congruent skip x z) :=
  ⟨⟨HypermathCountermodel.prefixAxioms_hold, fun _ _ _ _ _ => trivial⟩,
   ⟨prefixAxioms_hold skip, congruent_transitivity_claim_fails⟩⟩

/-- **The general statement, with symmetry and transitivity as two instances.**
The clauses admit every relation containing equality as `=~`, so no property of
`=~` that some such relation lacks is a consequence of them. Listing failures
one at a time is the wrong shape of result: the question is settled uniformly,
and settled negatively, for the whole family at once. -/
theorem congruent_is_free_above_equality :
    (∀ E : Form → Form → Prop, PrefixAxioms E) ∧
      (¬ ∀ x y : Form, Congruent asym x y → Congruent asym y x) ∧
      (¬ ∀ x y z : Form,
        Congruent skip x y → Congruent skip y z → Congruent skip x z) :=
  ⟨prefixAxioms_hold, congruent_symmetry_claim_fails,
    congruent_transitivity_claim_fails⟩

/-- **Componentwise agreement at `=~` inherits whatever symmetry `=~` has, and
no more.** `congruentPath` is documented as agreement of `p` and `q` on
(start, end, path-trace, quantification), all four compared at `=~`. Reading it
that way makes its symmetry a theorem *about `=~`*: it follows from symmetry of
`=~`, and in a model where `=~` is not symmetric neither is it. Defining the
parameter therefore does not remove the missing assumption, it relocates it to
a more basic and more widely useful place. -/
theorem componentwise_symmetry_is_exactly_congruent_symmetry
    {Path : Type} (E : Form → Form → Prop) (component : Path → Form) :
    (∀ x y : Form, Congruent E x y → Congruent E y x) →
      ∀ p q : Path, Congruent E (component p) (component q) →
        Congruent E (component q) (component p) :=
  fun symmetric _ _ h => symmetric _ _ h

end AsymmetricCongruent


namespace FreeSimulation

/-- The same question one level up, where the answer is not "no condition".
`≡` is constrained by `closeSemanticsOpaque` on its diagonal, by
`filtrationSimCong` from above, and by `ax-diff`, which denies `f2f x ≡ ground`.
Take `=~` to be `≡` itself and `~~` to be `True` and the first two constraints
are met by any relation containing equality; `ax-diff` is then the only one
left. So `≡` is free above equality *apart from pairs of the shape
`(f2f x, ground)`*, and that side condition is not a gap in the model --- it is
the entire content the clauses have about `≡`. -/
abbrev Form := Nat
def ground : Form := 0
def f2f (x : Form) : Form := x + 1
def Similar (_ _ : Form) : Prop := True
def Simulation (E : Form → Form → Prop) (x y : Form) : Prop := x = y ∨ E x y
def Congruent (E : Form → Form → Prop) (x y : Form) : Prop := x = y ∨ E x y
def structContinues (_ _ : Form) : Prop := True
def structDistinct (E : Form → Form → Prop) (x y : Form) : Prop := ¬ Simulation E x y
def structOrbits (_ _ : Form) : Prop := True
def HMSyntax (_ : Form) : Prop := True
def Substance (_ : Form) : Prop := True
def Semantics (_ : Form) : Prop := True
def FormClosure (_ : Form) : Prop := True
def Derives (E : Form → Form → Prop) (x y : Form) : Prop :=
  ∃ n : Nat, Congruent E (Nat.repeat f2f n x) y
def Discharge (E : Form → Form → Prop) (c e : Form) : Prop := Derives E e c
def Definition (E : Form → Form → Prop) (n x : Form) : Prop := Derives E n x

structure PrefixAxioms (E : Form → Form → Prop) : Prop where
  axDiff : ∀ x, structDistinct E (f2f x) ground
  axSim : ∀ x, structContinues (f2f x) ground
  axBox : ∀ x, structOrbits (f2f (f2f x)) x
  axGroundSelf : structContinues ground ground
  closeStructContinues : ∀ x, structContinues x ground ↔ Similar x ground
  closeStructDistinct : ∀ x y, structDistinct E x y ↔ ¬ Simulation E x y
  closeStructOrbits : ∀ x, structOrbits (f2f (f2f x)) x ↔ Similar (f2f (f2f x)) x
  axSyntaxRequiresSubstance : ∀ x, HMSyntax x → Substance x
  axSubstanceRequiresSemantics : ∀ x, Substance x → Semantics x
  axSemanticsRequiresSyntax : ∀ x, Semantics x → HMSyntax x
  axFormClosesLoop : ∀ x, HMSyntax x → Semantics x → FormClosure x
  axGroundSyntaxAx : HMSyntax ground
  axGroundSubstanceAx : Substance ground
  axGroundSemanticsAx : Semantics ground
  filtrationSimCong : ∀ x y, Simulation E x y → Congruent E x y
  filtrationCongSim : ∀ x y, Congruent E x y → Similar x y
  closeSyntaxOpaque : ∀ x, HMSyntax x ↔ ∃ n : Nat, Similar (Nat.repeat f2f n ground) x
  closeSubstanceOpaque : ∀ x, Substance x ↔ Congruent E x x
  closeSemanticsOpaque : ∀ x, Semantics x ↔ Simulation E x x
  closeDerivesOpaque : ∀ x y, Derives E x y ↔ ∃ n : Nat, Congruent E (Nat.repeat f2f n x) y
  closeDischargeOpaque : ∀ c e, Discharge E c e ↔ Derives E e c
  closeDefinitionOpaque : ∀ n x, Definition E n x ↔ Derives E n x
  closeFormClosureOpaque : ∀ x, FormClosure x ↔ HMSyntax x ∧ Substance x ∧ Semantics x
  traceLevels : ∀ x, Similar (f2f x) x ∧
    (Congruent E (f2f x) x → Similar (f2f x) x) ∧
    (Simulation E (f2f x) x → Congruent E (f2f x) x)

/-- **`≡` is free above equality apart from `ax-diff`.** One hypothesis, and it
is exactly the clause that mentions `≡` outside the closes. -/
theorem prefixAxioms_hold (E : Form → Form → Prop)
    (avoidsGround : ∀ x : Form, ¬ E (f2f x) ground) : PrefixAxioms E where
  axDiff := fun x h => h.elim (Nat.succ_ne_zero x) (avoidsGround x)
  axSim := fun _ => trivial
  axBox := fun _ => trivial
  axGroundSelf := trivial
  closeStructContinues := fun _ => Iff.rfl
  closeStructDistinct := fun _ _ => Iff.rfl
  closeStructOrbits := fun _ => Iff.rfl
  axSyntaxRequiresSubstance := fun _ _ => trivial
  axSubstanceRequiresSemantics := fun _ _ => trivial
  axSemanticsRequiresSyntax := fun _ _ => trivial
  axFormClosesLoop := fun _ _ _ => trivial
  axGroundSyntaxAx := trivial
  axGroundSubstanceAx := trivial
  axGroundSemanticsAx := trivial
  filtrationSimCong := fun _ _ h => h
  filtrationCongSim := fun _ _ _ => trivial
  closeSyntaxOpaque := fun _ => ⟨fun _ => ⟨0, trivial⟩, fun _ => trivial⟩
  closeSubstanceOpaque := fun _ => ⟨fun _ => Or.inl rfl, fun _ => trivial⟩
  closeSemanticsOpaque := fun _ => ⟨fun _ => Or.inl rfl, fun _ => trivial⟩
  closeDerivesOpaque := fun _ _ => Iff.rfl
  closeDischargeOpaque := fun _ _ => Iff.rfl
  closeDefinitionOpaque := fun _ _ => Iff.rfl
  closeFormClosureOpaque := fun _ => ⟨fun _ => ⟨trivial, trivial, trivial⟩, fun _ => trivial⟩
  traceLevels := fun _ => ⟨trivial, fun _ => trivial, fun h => h⟩

/-- One pair, pointing away from ground so `ax-diff` is untouched. -/
def swapPair (x y : Form) : Prop := x = 0 ∧ y = 1

/-- Two composable pairs, both clear of ground. -/
def skipUp (x y : Form) : Prop := (x = 3 ∧ y = 2) ∨ (x = 2 ∧ y = 1)

theorem swapPair_avoids_ground : ∀ x : Form, ¬ swapPair (f2f x) ground :=
  fun _ h => absurd h.2 (by decide)

theorem skipUp_avoids_ground : ∀ x : Form, ¬ skipUp (f2f x) ground := by
  intro _ h
  rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> exact absurd h (by decide)

/-- **`≡` is not symmetric.** -/
theorem simulation_symmetry_claim_fails :
    ¬ ∀ x y : Form, Simulation swapPair x y → Simulation swapPair y x := by
  intro symmetric
  rcases symmetric 0 1 (Or.inr ⟨rfl, rfl⟩) with h | ⟨h, _⟩ <;>
    exact absurd h (by decide)

/-- **`≡` is not transitive.** -/
theorem simulation_transitivity_claim_fails :
    ¬ ∀ x y z : Form,
      Simulation skipUp x y → Simulation skipUp y z → Simulation skipUp x z := by
  intro transitive
  rcases transitive 3 2 1 (Or.inr (Or.inl ⟨rfl, rfl⟩)) (Or.inr (Or.inr ⟨rfl, rfl⟩)) with
    h | (⟨_, h⟩ | ⟨h, _⟩) <;> exact absurd h (by decide)

/-- **The characterisation.** Every relation containing equality and relating no
image to ground satisfies all 24 clauses when read as `≡`. That is sufficiency;
necessity is already a theorem of the development, since
`Hypermath.axDiffInRelationLanguage` derives `¬ (f2f x ≡ ground)` from `ax-diff`
and `closeStructDistinct` and so holds in every model. The two halves together
say the clauses constrain `≡` in exactly one way and no other, which is a
stronger and more useful thing to know than any single missing property:
symmetry and transitivity fall outside it, and so does everything else. -/
theorem simulation_is_free_above_equality_apart_from_axDiff :
    (∀ E : Form → Form → Prop, (∀ x : Form, ¬ E (f2f x) ground) → PrefixAxioms E) ∧
      (¬ ∀ x y : Form, Simulation swapPair x y → Simulation swapPair y x) ∧
      (¬ ∀ x y z : Form,
        Simulation skipUp x y → Simulation skipUp y z → Simulation skipUp x z) :=
  ⟨prefixAxioms_hold, simulation_symmetry_claim_fails,
    simulation_transitivity_claim_fails⟩

end FreeSimulation

/-! ### The nine cells, each as one proposition

The table in `docs/research/CLAUSE_INDEPENDENCE.md` marks all nine cells of
three relations by three properties `independent`, and until now four of them
were declarations and five were readings. The five were sound readings --- the
freedom theorems above settle whole rows at once, and `prefixAxioms_hold` in
this file's outermost model satisfies every cell's property because `~~` and
`=~` are `True` there and `≡` is equality. But a row settled by a freedom
theorem and a cell settled by a pairing are different objects, and the table
made them look the same. These five close the gap, so the grid is nine
propositions and not five propositions and a paragraph.

Each satisfying half is the Bool model, which is why they are short. The point
is not the proofs; it is that the claims now exist. -/

theorem similar_transitivity_independent :
    (PrefixAxioms ∧
      ∀ x y z : Bool, Similar x y → Similar y z → Similar x z) ∧
    (IrreflexiveSimilar.PrefixAxioms ∧
      ¬ ∀ x y z : IrreflexiveSimilar.Form,
        IrreflexiveSimilar.Similar x y → IrreflexiveSimilar.Similar y z →
          IrreflexiveSimilar.Similar x z) :=
  ⟨⟨prefixAxioms_hold, fun _ _ _ _ _ => trivial⟩,
   ⟨IrreflexiveSimilar.prefixAxioms_hold,
    IrreflexiveSimilar.similar_transitive_claim_fails⟩⟩

theorem congruent_reflexivity_independent :
    (PrefixAxioms ∧ ∀ x : Bool, Congruent x x) ∧
    (IrreflexiveSimilar.PrefixAxioms ∧
      ¬ ∀ x : IrreflexiveSimilar.Form, IrreflexiveSimilar.Congruent x x) :=
  ⟨⟨prefixAxioms_hold, fun _ => trivial⟩,
   ⟨IrreflexiveSimilar.prefixAxioms_hold,
    IrreflexiveSimilar.congruent_reflexive_claim_fails⟩⟩

theorem simulation_reflexivity_independent :
    (PrefixAxioms ∧ ∀ x : Bool, Simulation x x) ∧
    (IrreflexiveSimilar.PrefixAxioms ∧
      ¬ ∀ x : IrreflexiveSimilar.Form, IrreflexiveSimilar.Simulation x x) :=
  ⟨⟨prefixAxioms_hold, fun _ => rfl⟩,
   ⟨IrreflexiveSimilar.prefixAxioms_hold,
    IrreflexiveSimilar.simulation_reflexive_claim_fails⟩⟩

theorem simulation_symmetry_independent :
    (PrefixAxioms ∧ ∀ x y : Bool, Simulation x y → Simulation y x) ∧
    (FreeSimulation.PrefixAxioms FreeSimulation.swapPair ∧
      ¬ ∀ x y : FreeSimulation.Form,
        FreeSimulation.Simulation FreeSimulation.swapPair x y →
          FreeSimulation.Simulation FreeSimulation.swapPair y x) :=
  ⟨⟨prefixAxioms_hold, fun _ _ h => h.symm⟩,
   ⟨FreeSimulation.prefixAxioms_hold FreeSimulation.swapPair
      FreeSimulation.swapPair_avoids_ground,
    FreeSimulation.simulation_symmetry_claim_fails⟩⟩

theorem simulation_transitivity_independent :
    (PrefixAxioms ∧
      ∀ x y z : Bool, Simulation x y → Simulation y z → Simulation x z) ∧
    (FreeSimulation.PrefixAxioms FreeSimulation.skipUp ∧
      ¬ ∀ x y z : FreeSimulation.Form,
        FreeSimulation.Simulation FreeSimulation.skipUp x y →
          FreeSimulation.Simulation FreeSimulation.skipUp y z →
            FreeSimulation.Simulation FreeSimulation.skipUp x z) :=
  ⟨⟨prefixAxioms_hold, fun _ _ _ h k => h.trans k⟩,
   ⟨FreeSimulation.prefixAxioms_hold FreeSimulation.skipUp
      FreeSimulation.skipUp_avoids_ground,
    FreeSimulation.simulation_transitivity_claim_fails⟩⟩


namespace FreeFiltration

/-! Each freedom theorem above fixes two of the three relations to answer about
the third, so none of them says what the 24 clauses assert about the filtration
as a whole. Leaving all three free turns the question into one with a complete
answer, and the answer is an iff rather than a one-way construction: a triple
satisfies every clause exactly when it satisfies the eight `Conditions` below.

The carrier is free too, and it has to be. Over the ground chain itself every
Form is an iterate of ground, so the third condition alone makes `Reach` total
and the two diagonal conditions say nothing beyond reflexivity of the upper
relations --- which is exactly the phenomenon `IrreflexiveSimilar` exists to
exhibit, and over a fixed chain carrier it would be invisible.
`reach_is_total_on_the_chain` records that degeneracy and `ext_conditions`
instantiates the characterization where it does not happen.

The auxiliary predicates carry no freedom. Ten of the 24 clauses are closes:
seven read `HMSyntax`, `Substance`, `Semantics`, `FormClosure`, `Derives`,
`Discharge` and `Definition` off the three relations, and three more read
`structContinues`, `structDistinct` and `structOrbits` off them. All ten are
`rfl` here --- `the_closes_are_definitional` proves it of nothing at all, and
`prefix_is_its_fourteen_contentful_clauses` removes them --- so the content of
the clause set is exactly what survives in `Conditions`. -/

variable {Form : Type}
variable {Path : Type}

/-- The ground chain reaches x up to similarity. `closeSyntaxOpaque` makes this
`HMSyntax`, and the two upper diagonals are pinned to it. -/
def Reach (ground : Form) (f2f : Form → Form) (S : Form → Form → Prop)
    (x : Form) : Prop :=
  ∃ n : Nat, S (Nat.repeat f2f n ground) x

def structContinues (ground : Form) (S : Form → Form → Prop)
    (x _ : Form) : Prop := S x ground
def structDistinct (E : Form → Form → Prop) (x y : Form) : Prop := ¬ E x y
def structOrbits (S : Form → Form → Prop) (x y : Form) : Prop := S x y
def HMSyntax (ground : Form) (f2f : Form → Form) (S : Form → Form → Prop)
    (x : Form) : Prop := Reach ground f2f S x
def Substance (C : Form → Form → Prop) (x : Form) : Prop := C x x
def Semantics (E : Form → Form → Prop) (x : Form) : Prop := E x x
def FormClosure (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) (x : Form) : Prop :=
  HMSyntax ground f2f S x ∧ Substance C x ∧ Semantics E x
def Derives (f2f : Form → Form) (C : Form → Form → Prop) (x y : Form) : Prop :=
  ∃ n : Nat, C (Nat.repeat f2f n x) y
def Discharge (f2f : Form → Form) (C : Form → Form → Prop)
    (c e : Form) : Prop := Derives f2f C e c
def Definition (f2f : Form → Form) (C : Form → Form → Prop)
    (n x : Form) : Prop := Derives f2f C n x

/-- The same 24 clauses, with the carrier, `~~`, `=~` and `≡` all left open. -/
structure PrefixAxioms (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) : Prop where
  axDiff : ∀ x, structDistinct E (f2f x) ground
  axSim : ∀ x, structContinues ground S (f2f x) ground
  axBox : ∀ x, structOrbits S (f2f (f2f x)) x
  axGroundSelf : structContinues ground S ground ground
  closeStructContinues : ∀ x, structContinues ground S x ground ↔ S x ground
  closeStructDistinct : ∀ x y, structDistinct E x y ↔ ¬ E x y
  closeStructOrbits : ∀ x, structOrbits S (f2f (f2f x)) x ↔ S (f2f (f2f x)) x
  axSyntaxRequiresSubstance : ∀ x, HMSyntax ground f2f S x → Substance C x
  axSubstanceRequiresSemantics : ∀ x, Substance C x → Semantics E x
  axSemanticsRequiresSyntax : ∀ x, Semantics E x → HMSyntax ground f2f S x
  axFormClosesLoop : ∀ x, HMSyntax ground f2f S x → Semantics E x →
    FormClosure ground f2f S C E x
  axGroundSyntaxAx : HMSyntax ground f2f S ground
  axGroundSubstanceAx : Substance C ground
  axGroundSemanticsAx : Semantics E ground
  filtrationSimCong : ∀ x y, E x y → C x y
  filtrationCongSim : ∀ x y, C x y → S x y
  closeSyntaxOpaque : ∀ x, HMSyntax ground f2f S x ↔ ∃ n : Nat, S (Nat.repeat f2f n ground) x
  closeSubstanceOpaque : ∀ x, Substance C x ↔ C x x
  closeSemanticsOpaque : ∀ x, Semantics E x ↔ E x x
  closeDerivesOpaque : ∀ x y, Derives f2f C x y ↔ ∃ n : Nat, C (Nat.repeat f2f n x) y
  closeDischargeOpaque : ∀ c e, Discharge f2f C c e ↔ Derives f2f C e c
  closeDefinitionOpaque : ∀ n x, Definition f2f C n x ↔ Derives f2f C n x
  closeFormClosureOpaque : ∀ x, FormClosure ground f2f S C E x ↔ HMSyntax ground f2f S x ∧ Substance C x ∧ Semantics E x
  traceLevels : ∀ x, S (f2f x) x ∧ (C (f2f x) x → S (f2f x) x) ∧
    (E (f2f x) x → C (f2f x) x)

/-- Everything the 24 clauses say about the filtration. Two inclusions, three
facts about forming at the bottom level, one denial at the top, and the two
upper diagonals pinned to reachability. `Hypermath.filtrationConditionsHold`
proves each of the eight in the layer, so these are necessary as well as
sufficient. -/
structure Conditions (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) : Prop where
  simIntoCong : ∀ x y, E x y → C x y
  congIntoSim : ∀ x y, C x y → S x y
  imageSimilar : ∀ x, S (f2f x) x
  imageSimilarToGround : ∀ x, S (f2f x) ground
  doubleImageSimilar : ∀ x, S (f2f (f2f x)) x
  imageNotSimulatingGround : ∀ x, ¬ E (f2f x) ground
  congruentDiagonalIsReach : ∀ x, C x x ↔ Reach ground f2f S x
  simulationDiagonalIsReach : ∀ x, E x x ↔ Reach ground f2f S x

theorem conditions_reach_ground {ground : Form} {f2f : Form → Form}
    {S C E : Form → Form → Prop} (h : Conditions ground f2f S C E) :
    Reach ground f2f S ground :=
  ⟨1, h.imageSimilarToGround ground⟩

theorem prefixAxioms_of_conditions {ground : Form} {f2f : Form → Form}
    {S C E : Form → Form → Prop} (h : Conditions ground f2f S C E) :
    PrefixAxioms ground f2f S C E where
  axDiff := h.imageNotSimulatingGround
  axSim := h.imageSimilarToGround
  axBox := h.doubleImageSimilar
  axGroundSelf :=
    h.congIntoSim ground ground
      ((h.congruentDiagonalIsReach ground).mpr (conditions_reach_ground h))
  closeStructContinues := fun _ => Iff.rfl
  closeStructDistinct := fun _ _ => Iff.rfl
  closeStructOrbits := fun _ => Iff.rfl
  axSyntaxRequiresSubstance := fun x r => (h.congruentDiagonalIsReach x).mpr r
  axSubstanceRequiresSemantics := fun x c =>
    (h.simulationDiagonalIsReach x).mpr ((h.congruentDiagonalIsReach x).mp c)
  axSemanticsRequiresSyntax := fun x e => (h.simulationDiagonalIsReach x).mp e
  axFormClosesLoop := fun x r e => ⟨r, (h.congruentDiagonalIsReach x).mpr r, e⟩
  axGroundSyntaxAx := conditions_reach_ground h
  axGroundSubstanceAx :=
    (h.congruentDiagonalIsReach ground).mpr (conditions_reach_ground h)
  axGroundSemanticsAx :=
    (h.simulationDiagonalIsReach ground).mpr (conditions_reach_ground h)
  filtrationSimCong := h.simIntoCong
  filtrationCongSim := h.congIntoSim
  closeSyntaxOpaque := fun _ => Iff.rfl
  closeSubstanceOpaque := fun _ => Iff.rfl
  closeSemanticsOpaque := fun _ => Iff.rfl
  closeDerivesOpaque := fun _ _ => Iff.rfl
  closeDischargeOpaque := fun _ _ => Iff.rfl
  closeDefinitionOpaque := fun _ _ => Iff.rfl
  closeFormClosureOpaque := fun _ => Iff.rfl
  traceLevels := fun x =>
    ⟨h.imageSimilar x, fun _ => h.imageSimilar x, fun e => h.simIntoCong _ _ e⟩

theorem conditions_of_prefixAxioms {ground : Form} {f2f : Form → Form}
    {S C E : Form → Form → Prop} (a : PrefixAxioms ground f2f S C E) :
    Conditions ground f2f S C E where
  simIntoCong := a.filtrationSimCong
  congIntoSim := a.filtrationCongSim
  imageSimilar := fun x => (a.traceLevels x).1
  imageSimilarToGround := fun x => (a.closeStructContinues (f2f x)).mp (a.axSim x)
  doubleImageSimilar := fun x => (a.closeStructOrbits x).mp (a.axBox x)
  imageNotSimulatingGround := fun x =>
    (a.closeStructDistinct (f2f x) ground).mp (a.axDiff x)
  congruentDiagonalIsReach := fun x =>
    ⟨fun c => (a.closeSyntaxOpaque x).mp
        (a.axSemanticsRequiresSyntax x
          (a.axSubstanceRequiresSemantics x ((a.closeSubstanceOpaque x).mpr c))),
     fun r => (a.closeSubstanceOpaque x).mp
        (a.axSyntaxRequiresSubstance x ((a.closeSyntaxOpaque x).mpr r))⟩
  simulationDiagonalIsReach := fun x =>
    ⟨fun e => (a.closeSyntaxOpaque x).mp
        (a.axSemanticsRequiresSyntax x ((a.closeSemanticsOpaque x).mpr e)),
     fun r => (a.closeSemanticsOpaque x).mp
        (a.axSubstanceRequiresSemantics x
          (a.axSyntaxRequiresSubstance x ((a.closeSyntaxOpaque x).mpr r)))⟩

/-- **The characterization.** A triple of relations on any carrier satisfies all
24 L0/L1 clauses exactly when it satisfies the eight conditions. Everything the
clauses prove about the filtration is a consequence of those eight, and
everything they do not is refuted by exhibiting a carrier and a triple. -/
theorem prefixAxioms_iff_conditions (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) :
    PrefixAxioms ground f2f S C E ↔ Conditions ground f2f S C E :=
  ⟨conditions_of_prefixAxioms, prefixAxioms_of_conditions⟩

/-! ### The chain carrier, where two of the eight go vacuous -/

abbrev Chain := Nat
def chainGround : Chain := 0
def chainStep (x : Chain) : Chain := x + 1

theorem repeat_from_chainGround (n : Nat) :
    Nat.repeat chainStep n chainGround = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.repeat, ih, chainStep]

/-- On the chain every Form is an iterate of ground, so the third condition on
its own makes `Reach` total. The two diagonal conditions then say only that the
upper relations are reflexive, and the cofinality content of
`Hypermath.reflexivityIsGroundReachability` cannot be seen at all. That is why
the characterization above leaves the carrier open: a chain-only statement would
have been true and would have hidden its own most interesting clause. -/
theorem reach_is_total_on_the_chain (S : Chain → Chain → Prop)
    (image : ∀ x, S (chainStep x) x) :
    ∀ x, Reach chainGround chainStep S x :=
  fun x => ⟨x + 1, by rw [repeat_from_chainGround]; exact image x⟩

/-- `~~` read as an order: "y is no more formed than x". Forming climbs it,
which is all three `~~` conditions, and it is reflexive so every Form is
reached. -/
def formedAtLeast (x y : Chain) : Prop := y ≤ x

theorem formedAtLeast_conditions :
    Conditions chainGround chainStep formedAtLeast Eq Eq where
  simIntoCong := fun _ _ h => h
  congIntoSim := fun x y h => h ▸ Nat.le_refl x
  imageSimilar := fun x => Nat.le_succ x
  imageSimilarToGround := fun _ => Nat.zero_le _
  doubleImageSimilar := fun x => Nat.le_trans (Nat.le_succ x) (Nat.le_succ (x + 1))
  imageNotSimulatingGround := fun x h => Nat.succ_ne_zero x h
  congruentDiagonalIsReach := fun x =>
    ⟨fun _ => ⟨x, by rw [repeat_from_chainGround]; exact Nat.le_refl x⟩, fun _ => rfl⟩
  simulationDiagonalIsReach := fun x =>
    ⟨fun _ => ⟨x, by rw [repeat_from_chainGround]; exact Nat.le_refl x⟩, fun _ => rfl⟩

/-- `~~` may be a partial order. Every previous witness made it either the
total relation or the ad-hoc irreflexive one, which left open whether assuming
it well behaved settles anything. It does not: reflexive, transitive and
antisymmetric is consistent with every clause, with `=~` and `≡` both equality,
and `~~` still not total. -/
theorem similar_can_be_a_partial_order :
    PrefixAxioms chainGround chainStep formedAtLeast Eq Eq ∧
      (∀ x, formedAtLeast x x) ∧
      (∀ x y z, formedAtLeast x y → formedAtLeast y z → formedAtLeast x z) ∧
      (∀ x y, formedAtLeast x y → formedAtLeast y x → x = y) ∧
      ¬ ∀ x y, formedAtLeast x y :=
  ⟨prefixAxioms_of_conditions formedAtLeast_conditions,
    fun x => Nat.le_refl x,
    fun _ _ _ hxy hyz => Nat.le_trans hyz hxy,
    fun _ _ hxy hyx => Nat.le_antisymm hyx hxy,
    fun total => Nat.not_succ_le_zero 0 (total chainGround (chainStep chainGround))⟩

/-- **Reflexivity of `=~` is not a condition at this corner; it is a
consequence.** The collapse below used to carry it as a fourth conjunct, and the
sentence that read the corner off in prose said "both reflexive" --- two
conditions spoken as one, so the name said three, the statement said four, and
nothing anywhere was false. A count in a name is not a measurement until the
conditions it counts are each shown to be needed. -/
theorem congruent_reflexivity_is_not_a_fourth_condition
    (C E : Form → Form → Prop) (into : ∀ x y, E x y → C x y)
    (reflexive : ∀ x, E x x) : ∀ x, C x x :=
  fun x => into x x (reflexive x)

/-- **A total `~~` reaches everything, on every carrier.** `Reach` asks for an
iterate of ground that the relation connects to `x`, and a total relation
connects the first one, so no property of ground, of forming or of the carrier
is used. This is the second of two ways the ground chain becomes cofinal in this
file and they have nothing in common: `reach_is_total_on_the_chain` gets it from
the carrier and needs the third condition, this gets it from the relation and
needs no condition at all. -/
theorem total_similar_makes_reach_total (ground : Form) (f2f : Form → Form)
    (x : Form) : Reach ground f2f (fun _ _ => True) x :=
  ⟨0, trivial⟩

/-- What is left of the eight when `~~` is the total relation: the inclusion of
`≡` into `=~`, reflexivity of `≡`, and the denial. Named as a structure for the
same reason `SimilarConditions` is --- so each one can be dropped by name, and
so a fourth cannot be added to the right of an iff without a model. -/
structure TotalSimilarConditions (ground : Form) (f2f : Form → Form)
    (C E : Form → Form → Prop) : Prop where
  simulationIntoCongruent : ∀ x y, E x y → C x y
  simulationReflexive : ∀ x, E x x
  imageNotSimulatingGround : ∀ x, ¬ E (f2f x) ground

/-- With `~~` total the eight conditions collapse to three, and they are exactly
the ones the clauses are usually read as asserting: `≡` is contained in `=~`, it
is reflexive, and it denies every image at ground. Reflexivity of `=~` comes
along by `congruent_reflexivity_is_not_a_fourth_condition` and is not one of
them. Nothing further about either relation follows --- which is the two upper
freedom theorems, recovered from the joint statement.

The carrier is arbitrary, as at the other corner. It was the chain here for
longer than it needed to be, and the docstring gave the chain as the reason the
two diagonal conditions turn into plain reflexivity. That was the wrong reason.
They turn into reflexivity because `total_similar_makes_reach_total` empties
`Reach` of content the moment `~~` is total, which happens on every carrier and
uses nothing about this one. `ext_conditions` keeps `~~` partial, and there the
distinction between reflexivity and reachability survives --- so the thing that
decides whether the distinction is visible is the relation, not the carrier. -/
theorem total_similar_leaves_exactly_three_conditions
    (ground : Form) (f2f : Form → Form) (C E : Form → Form → Prop) :
    Conditions ground f2f (fun _ _ => True) C E ↔
      TotalSimilarConditions ground f2f C E :=
  ⟨fun h =>
      { simulationIntoCongruent := h.simIntoCong
        simulationReflexive := fun x =>
          (h.simulationDiagonalIsReach x).mpr ⟨0, trivial⟩
        imageNotSimulatingGround := h.imageNotSimulatingGround },
    fun h =>
      { simIntoCong := h.simulationIntoCongruent
        congIntoSim := fun _ _ _ => trivial
        imageSimilar := fun _ => trivial
        imageSimilarToGround := fun _ => trivial
        doubleImageSimilar := fun _ => trivial
        imageNotSimulatingGround := h.imageNotSimulatingGround
        congruentDiagonalIsReach := fun x =>
          ⟨fun _ => ⟨0, trivial⟩,
           fun _ => h.simulationIntoCongruent x x (h.simulationReflexive x)⟩
        simulationDiagonalIsReach := fun x =>
          ⟨fun _ => ⟨0, trivial⟩, fun _ => h.simulationReflexive x⟩ }⟩

/-! #### Each of the three is needed

The other corner had six conditions and six models. Three here, and the same
question: an iff is exactly as true when one of its conditions follows from the
rest, which is how the fourth conjunct survived. Each of the three is dropped
below on a pair of relations that fails it and satisfies the other two, so three
is a measurement and not a reading of the sentence. -/

/-- `≡` relating ground to the first rung, with `=~` equality. The inclusion is
the only condition this fails. -/
def oneExtraPair (x y : Chain) : Prop := x = y ∨ (x = 0 ∧ y = 1)

theorem two_hold_without_simulationIntoCongruent :
    ((∀ x, oneExtraPair x x) ∧
      ∀ x, ¬ oneExtraPair (chainStep x) chainGround) ∧
    ¬ ∀ x y, oneExtraPair x y → x = y :=
  ⟨⟨fun _ => Or.inl rfl,
    fun _ h => match h with
      | Or.inl e => Nat.noConfusion e
      | Or.inr ⟨e, _⟩ => Nat.noConfusion e⟩,
   fun into => Nat.noConfusion (into 0 1 (Or.inr ⟨rfl, rfl⟩))⟩

/-- `≡` empty. Contained in everything and denying everything, and reflexive
nowhere. -/
def noSimulation (_ _ : Chain) : Prop := False

theorem two_hold_without_simulationReflexive :
    ((∀ x y, noSimulation x y → (fun _ _ : Chain => True) x y) ∧
      ∀ x, ¬ noSimulation (chainStep x) chainGround) ∧
    ¬ ∀ x, noSimulation x x :=
  ⟨⟨fun _ _ _ => trivial, fun _ h => h⟩, fun reflexive => reflexive chainGround⟩

/-- `≡` relating everything into ground, with `=~` total. Reflexive and
contained; the denial is the gap. -/
def simulatesGround (x y : Chain) : Prop := x = y ∨ y = chainGround

theorem two_hold_without_imageNotSimulatingGround :
    ((∀ x y, simulatesGround x y → (fun _ _ : Chain => True) x y) ∧
      ∀ x, simulatesGround x x) ∧
    ¬ ∀ x, ¬ simulatesGround (chainStep x) chainGround :=
  ⟨⟨fun _ _ _ => trivial, fun _ => Or.inl rfl⟩,
   fun denies => denies chainGround (Or.inr rfl)⟩

/-! ### What the eight forbid

Every result above asks what the conditions allow. Freedom at the top, a count
at each corner, a model for each cell: all of them exhibit relations, and a
reader with only those will take "what do the eight rule out?" to be answered
by "not much".

One theorem in the file did ask it. `ground_is_not_an_image` was proved a
thousand lines below, in the transfinite section, as background for a clause
about the limit --- an answer about the eight, filed under the section that
happened to need it, where nothing in the prefix section could find it. It is
moved here. The rest of this section is what it gives once it is read as a
statement about the eight rather than as a lemma for something else. -/

/-- **Ground is not an image.** The prefix conditions already say something
    about the carrier: forming never returns to the ground.
    `imageNotSimulatingGround` denies simulation from an image to the ground,
    `simulationDiagonalIsReach` grants it wherever the chain reaches, and
    `conditions_reach_ground` says the chain reaches the ground. Three of the
    eight say it together and none of them says it alone; the other five are
    unused, and so is the carrier.

    The sixth condition denies `≡` between an image and ground, which is a
    statement about a relation. This turns it into a statement about identity:
    an image is not merely un-simulated at ground, it is not ground.

    So "the clauses constrain the carrier" is true well before the transfinite
    layer appears. What is new there is the *kind* of constraint: this one
    forbids a coincidence inside the chain, and `axLimitNotFinite` demands a
    point the chain never visits. -/
theorem ground_is_not_an_image {ground : Form} {f2f : Form → Form}
    {S C E : Form → Form → Prop} (h : Conditions ground f2f S C E) (x : Form) :
    f2f x ≠ ground := by
  intro hx
  apply h.imageNotSimulatingGround x
  rw [hx]
  exact (h.simulationDiagonalIsReach ground).mpr (conditions_reach_ground h)

/-- In particular forming does not fix ground, which is the case `x = ground`.
    Stating it separately is worth one line: every later use in this section is
    at ground, and the fixed-point reading is the one that makes `~~` never
    equality. -/
theorem ground_is_not_a_fixed_point (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) (h : Conditions ground f2f S C E) :
    f2f ground ≠ ground :=
  ground_is_not_an_image h ground

/-- **`~~` is never equality.** The two relations above it may both be equality
--- that is the lower corner, and it is consistent --- and the one below them
may not be. Equality makes the second condition say that forming is the
identity, so ground is a fixed point of it, which the previous theorem forbids.

So "`≡` and `=~` are free above equality, and `~~` is not free at all" understates
it in one direction: `~~` is not merely constrained, it is kept off the bottom of
the lattice of relations entirely. The clauses require the filtration to identify
something. -/
theorem similar_is_never_equality (ground : Form) (f2f : Form → Form)
    (C E : Form → Form → Prop) :
    ¬ Conditions ground f2f (fun x y => x = y) C E := fun h =>
  ground_is_not_a_fixed_point ground f2f _ C E h (h.imageSimilar ground)

/-- **And `~~` is never `≡` either, at the other end of the same chain.** The
third condition puts every image at ground under `~~` and the sixth keeps every
image off ground under `≡`, so the inclusion `≡ ⊆ =~ ⊆ ~~` is strict as a
composite in every model of the eight, with no model needed to show it. -/
theorem similarity_is_not_contained_in_simulation (ground : Form)
    (f2f : Form → Form) (S C E : Form → Form → Prop)
    (h : Conditions ground f2f S C E) : ¬ ∀ x y, S x y → E x y := fun into =>
  h.imageNotSimulatingGround ground (into _ _ (h.imageSimilarToGround ground))

/-- **So the three relations are never all one.** Immediate from the previous
theorem, and worth its own name: the clause set cannot be read as talking about
a single relation under three spellings, which is the reading a list of freedoms
most invites. -/
theorem the_three_relations_are_never_all_one (ground : Form)
    (f2f : Form → Form) (S : Form → Form → Prop) :
    ¬ Conditions ground f2f S S S := fun h =>
  similarity_is_not_contained_in_simulation ground f2f S S S h (fun _ _ k => k)

/-- Which of the two links is the strict one is not decided. Here `=~` is `~~`,
so the strictness is all in the lower link; `ext_conditions` has `=~` equal to
`≡` instead, and `neither_inclusion_is_forced_to_be_strict` puts the two
together. -/
theorem congruent_may_equal_similar :
    Conditions chainGround chainStep (fun _ _ => True) (fun _ _ => True)
      (fun x y => x = y) :=
  (total_similar_leaves_exactly_three_conditions chainGround chainStep
      (fun _ _ => True) (fun x y => x = y)).mpr
    { simulationIntoCongruent := fun _ _ _ => trivial
      simulationReflexive := fun _ => rfl
      imageNotSimulatingGround := fun _ h => Nat.noConfusion h }

/-! #### How small a carrier can be

`ground_is_not_an_image` is a statement about forming, and it is also the first
statement in this file about the carrier: a Form that is not ground exists,
namely any image. So the eight have no one-point model, and the question of how
small a model can be has an answer rather than a bound. -/

/-- **No model of the eight has one Form.** Forming on a one-point carrier sends
ground to ground, and `ground_is_not_an_image` forbids that. This is also why
`five_hold_without_formingAvoidsGround` had to use the one-point carrier: the
only carrier on which forming can return to ground is one where the eight do not
hold at all, which is a sharper reason than "the chain cannot do it". -/
theorem no_model_on_one_point (f2f : Unit → Unit) (S C E : Unit → Unit → Prop) :
    ¬ Conditions () f2f S C E := fun h =>
  ground_is_not_an_image h () rfl

/-- Forming as the constant map to the second Form. -/
def twoPointStep (_ : Bool) : Bool := true

/-- `~~` relates the image to everything, and is otherwise equality. -/
def twoPointSimilar (x y : Bool) : Prop := x = true ∨ x = y

/-- **And two Forms are enough.** `=~` and `≡` are both equality, which the
lower corner allows, and `~~` is the smallest relation the conditions admit on
two points. The ground chain reaches everything at its first step, so both
diagonal conditions hold; the denial holds because the image is the Form that is
not ground. -/
theorem two_points_are_enough :
    Conditions false twoPointStep twoPointSimilar (fun x y => x = y)
      (fun x y => x = y) where
  simIntoCong := fun _ _ k => k
  congIntoSim := fun _ _ k => Or.inr k
  imageSimilar := fun _ => Or.inl rfl
  imageSimilarToGround := fun _ => Or.inl rfl
  doubleImageSimilar := fun _ => Or.inl rfl
  imageNotSimulatingGround := fun _ h => Bool.noConfusion h
  congruentDiagonalIsReach := fun _ => ⟨fun _ => ⟨1, Or.inl rfl⟩, fun _ => rfl⟩
  simulationDiagonalIsReach := fun _ => ⟨fun _ => ⟨1, Or.inl rfl⟩, fun _ => rfl⟩

/-- **So the smallest model of the eight has exactly two Forms.** Every earlier
result in this file leaves the carrier open and says nothing about its size; the
two halves here bound it from both sides, and the bound is tight. -/
theorem two_is_the_smallest_carrier :
    (∀ (f2f : Unit → Unit) (S C E : Unit → Unit → Prop),
        ¬ Conditions () f2f S C E) ∧
      Conditions false twoPointStep twoPointSimilar (fun x y => x = y)
        (fun x y => x = y) :=
  ⟨no_model_on_one_point, two_points_are_enough⟩

/-! #### The two ends of the lattice of relations

`similar_is_never_equality` said `~~` is kept off the bottom. The question it
poses and does not ask is what happens at the top, and for which of the three
relations. Six settings, three relations at two extremes, and the answer is not
symmetric. -/

/-- **`≡` is never total.** One condition says so on its own: the sixth denies
`≡` between an image and the ground, and a total relation denies nothing. No
carrier and no other condition is consulted, which makes this the cheapest
impossibility in the file. -/
theorem simulation_is_never_total (ground : Form) (f2f : Form → Form)
    (S C : Form → Form → Prop) :
    ¬ Conditions ground f2f S C (fun _ _ => True) := fun h =>
  h.imageNotSimulatingGround ground trivial

/-- A total `=~` forces a total `~~`, by the fifth condition and nothing else,
so the middle relation cannot reach the top without taking the bottom one with
it. -/
theorem total_congruent_forces_total_similar (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) (h : Conditions ground f2f S C E)
    (total : ∀ x y, C x y) : ∀ x y, S x y :=
  fun x y => h.congIntoSim x y (total x y)

/-- **The six extremes, four of them reachable.** Each relation at equality and
at totality, in the order `~~`, `=~`, `≡`:

* `~~` at equality is impossible --- the second condition would make forming the
  identity, and `ground_is_not_an_image` forbids that;
* `~~` total is the upper corner;
* `=~` at equality holds in the two-Form model;
* `=~` total holds in the same model as `~~` total, and by
  `total_congruent_forces_total_similar` it can hold in no other kind;
* `≡` at equality holds in the two-Form model, which is the lower corner;
* `≡` total is impossible, by one condition alone.

The asymmetry is the finding and it has one cause on each side. The bottom
relation cannot be smallest because `imageSimilar` makes it relate an image to
something it is not; the top relation cannot be largest because
`imageNotSimulatingGround` makes it fail somewhere. **The clause set requires the
bottom relation to identify and the top relation to distinguish**, and requires
nothing of either kind from the one in between, which is free at both ends. -/
theorem the_extremes_of_the_three_relations :
    ((∀ (ground : Form) (f2f : Form → Form) (C E : Form → Form → Prop),
        ¬ Conditions ground f2f (fun x y => x = y) C E) ∧
      Conditions chainGround chainStep (fun _ _ => True) (fun _ _ => True)
        (fun x y => x = y)) ∧
    (Conditions false twoPointStep twoPointSimilar (fun x y => x = y)
        (fun x y => x = y) ∧
      Conditions chainGround chainStep (fun _ _ => True) (fun _ _ => True)
        (fun x y => x = y)) ∧
    (Conditions false twoPointStep twoPointSimilar (fun x y => x = y)
        (fun x y => x = y) ∧
      ∀ (ground : Form) (f2f : Form → Form) (S C : Form → Form → Prop),
        ¬ Conditions ground f2f S C (fun _ _ => True)) :=
  ⟨⟨similar_is_never_equality, congruent_may_equal_similar⟩,
   ⟨two_points_are_enough, congruent_may_equal_similar⟩,
   ⟨two_points_are_enough, simulation_is_never_total⟩⟩

/-! #### What is left free at the smallest carrier

Two Forms suffice, and the question that asks is how much of a model the eight
still choose once the carrier is that small. `imageNotSimulatingGround` forbids
one value for each `f2f x`; forbidding one value out of two is naming the other
one. -/

theorem bool_ne_is_not : ∀ a b : Bool, a ≠ b → a = !b := by decide

/-- **Forming is not a choice at two Forms.** `ground_is_not_an_image` says
`f2f x` is never the ground, and on two Forms that leaves exactly one value, so
every model of the eight over `Bool` has the same forming map --- the constant
one to the other Form. No other clause is consulted. -/
theorem forming_is_forced_at_two_points {ground : Bool} {f2f : Bool → Bool}
    {S C E : Bool → Bool → Prop} (h : Conditions ground f2f S C E) (x : Bool) :
    f2f x = !ground :=
  bool_ne_is_not _ _ (ground_is_not_an_image h x)

/-- With forming constant, one step of the chain lands on the image of anything,
    so `imageSimilar` makes every Form reachable. -/
theorem reach_is_total_at_two_points {ground : Bool} {f2f : Bool → Bool}
    {S C E : Bool → Bool → Prop} (h : Conditions ground f2f S C E) (x : Bool) :
    Reach ground f2f S x := by
  refine ⟨1, ?_⟩
  show S (f2f ground) x
  rw [forming_is_forced_at_two_points h ground,
    ← forming_is_forced_at_two_points h x]
  exact h.imageSimilar x

/-- So both upper diagonals are total, by the two reachability clauses. At two
    Forms the clause set has already decided four of the eight cells of `=~` and
    `≡` between them. -/
theorem both_diagonals_are_forced_at_two_points {ground : Bool}
    {f2f : Bool → Bool} {S C E : Bool → Bool → Prop}
    (h : Conditions ground f2f S C E) : (∀ x, C x x) ∧ (∀ x, E x x) :=
  ⟨fun x => (h.congruentDiagonalIsReach x).mpr (reach_is_total_at_two_points h x),
   fun x => (h.simulationDiagonalIsReach x).mpr (reach_is_total_at_two_points h x)⟩

/-- **Three of the four cells of `~~` are forced true.** Everything is similar
    to the ground, because the image is by `imageSimilarToGround` and the ground
    is by its own `≡` diagonal through the two inclusions; and the image is
    similar to everything by `imageSimilar`. What is left is one cell: the
    ground to the other Form. -/
theorem similar_is_forced_off_one_cell_at_two_points {ground : Bool}
    {f2f : Bool → Bool} {S C E : Bool → Bool → Prop}
    (h : Conditions ground f2f S C E) (x y : Bool)
    (off : x ≠ ground ∨ y ≠ !ground) : S x y := by
  cases off with
  | inl hx =>
    have hfx : f2f y = x := by
      rw [forming_is_forced_at_two_points h y, ← bool_ne_is_not x ground hx]
    rw [← hfx]
    exact h.imageSimilar y
  | inr hy =>
    have hyg : y = ground := by
      have step := bool_ne_is_not y (!ground) hy
      rwa [Bool.not_not] at step
    subst hyg
    cases Bool.decEq x y with
    | isTrue hx =>
      subst hx
      exact h.congIntoSim _ _
        (h.simIntoCong _ _ ((both_diagonals_are_forced_at_two_points h).2 x))
    | isFalse hx =>
      have hfx : f2f y = x := by
        rw [forming_is_forced_at_two_points h y, ← bool_ne_is_not x y hx]
      rw [← hfx]
      exact h.imageSimilarToGround y

/-- The all-`True` similarity over two Forms, which differs from
`twoPointSimilar` in the one free cell and nowhere else. -/
theorem two_points_are_enough_with_total_similar :
    Conditions false twoPointStep (fun _ _ => True) (fun x y => x = y)
      (fun x y => x = y) where
  simIntoCong := fun _ _ k => k
  congIntoSim := fun _ _ _ => trivial
  imageSimilar := fun _ => trivial
  imageSimilarToGround := fun _ => trivial
  doubleImageSimilar := fun _ => trivial
  imageNotSimulatingGround := fun _ h => Bool.noConfusion h
  congruentDiagonalIsReach := fun _ => ⟨fun _ => ⟨0, trivial⟩, fun _ => rfl⟩
  simulationDiagonalIsReach := fun _ => ⟨fun _ => ⟨0, trivial⟩, fun _ => rfl⟩

/-- Everything except the one cell the sixth condition denies. -/
def twoPointUpper (x y : Bool) : Prop := ¬ (x = true ∧ y = false)

/-- Simulation as large as the sixth condition permits: the whole square but the
image-to-ground cell. Congruence the same, similarity total. -/
theorem two_points_are_enough_with_maximal_simulation :
    Conditions false twoPointStep (fun _ _ => True) twoPointUpper
      twoPointUpper where
  simIntoCong := fun _ _ k => k
  congIntoSim := fun _ _ _ => trivial
  imageSimilar := fun _ => trivial
  imageSimilarToGround := fun _ => trivial
  doubleImageSimilar := fun _ => trivial
  imageNotSimulatingGround := fun _ k => k ⟨rfl, rfl⟩
  congruentDiagonalIsReach := fun _ =>
    ⟨fun _ => ⟨0, trivial⟩, fun _ h => Bool.noConfusion (h.1.symm.trans h.2)⟩
  simulationDiagonalIsReach := fun _ =>
    ⟨fun _ => ⟨0, trivial⟩, fun _ h => Bool.noConfusion (h.1.symm.trans h.2)⟩

/-- **And the cell that is left is genuinely free, for `~~` and for `≡` both.**
    Three models over the same two Forms and the same forced forming map: the
    first has `~~` false at the ground-to-image cell, the second has it true,
    and the third has `≡` true at that cell where the second has it false. -/
theorem the_free_cells_are_free :
    (Conditions false twoPointStep twoPointSimilar (fun x y => x = y)
        (fun x y => x = y) ∧ ¬ twoPointSimilar false true) ∧
      (Conditions false twoPointStep (fun _ _ => True) (fun x y => x = y)
          (fun x y => x = y) ∧ ¬ (false = true)) ∧
      (Conditions false twoPointStep (fun _ _ => True) twoPointUpper
          twoPointUpper ∧ twoPointUpper false true) :=
  ⟨⟨two_points_are_enough,
     fun k => k.elim (fun e => Bool.noConfusion e) (fun e => Bool.noConfusion e)⟩,
   ⟨two_points_are_enough_with_total_similar, fun e => Bool.noConfusion e⟩,
   ⟨two_points_are_enough_with_maximal_simulation, fun h => Bool.noConfusion h.1⟩⟩

theorem not_self_ne : ∀ b : Bool, (!b) ≠ b := by decide

theorem self_ne_not : ∀ b : Bool, b ≠ !b := by decide

/-- **Eight of the twelve cells are decided.** Similarity holds everywhere but
    the ground-to-image cell, both upper diagonals are total, and simulation
    fails at the image-to-ground cell because the sixth condition says so. That
    is three cells of `~~`, two of `=~` and three of `≡`, in every model of the
    eight over two Forms. -/
theorem eight_cells_are_forced_at_two_points {ground : Bool} {f2f : Bool → Bool}
    {S C E : Bool → Bool → Prop} (h : Conditions ground f2f S C E) :
    (S (!ground) ground ∧ S (!ground) (!ground) ∧ S ground ground) ∧
      (C ground ground ∧ C (!ground) (!ground)) ∧
      (E ground ground ∧ E (!ground) (!ground) ∧ ¬ E (!ground) ground) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact similar_is_forced_off_one_cell_at_two_points h _ _
      (Or.inl (not_self_ne ground))
  · exact similar_is_forced_off_one_cell_at_two_points h _ _
      (Or.inl (not_self_ne ground))
  · exact similar_is_forced_off_one_cell_at_two_points h _ _
      (Or.inr (self_ne_not ground))
  · exact (both_diagonals_are_forced_at_two_points h).1 ground
  · exact (both_diagonals_are_forced_at_two_points h).1 (!ground)
  · exact (both_diagonals_are_forced_at_two_points h).2 ground
  · exact (both_diagonals_are_forced_at_two_points h).2 (!ground)
  · rw [← forming_is_forced_at_two_points h ground]
    exact h.imageNotSimulatingGround ground

/-- Congruence as large as it can be, which no clause forbids: the sixth
condition denies a cell of `≡` and nothing denies any cell of `=~`. -/
theorem two_points_are_enough_with_total_congruent :
    Conditions false twoPointStep (fun _ _ => True) (fun _ _ => True)
      (fun x y => x = y) where
  simIntoCong := fun _ _ _ => trivial
  congIntoSim := fun _ _ _ => trivial
  imageSimilar := fun _ => trivial
  imageSimilarToGround := fun _ => trivial
  doubleImageSimilar := fun _ => trivial
  imageNotSimulatingGround := fun _ h => Bool.noConfusion h
  congruentDiagonalIsReach := fun _ => ⟨fun _ => ⟨0, trivial⟩, fun _ => trivial⟩
  simulationDiagonalIsReach := fun _ => ⟨fun _ => ⟨0, trivial⟩, fun _ => rfl⟩

/-- **Both off-diagonal cells of `=~` are free.** Two models over the same two
    Forms, the same forced forming map and the same total `~~`: one has
    congruence equality, which fails at both off-diagonal cells, and the other
    has it total. Nothing in the eight distinguishes them. -/
theorem congruent_has_two_free_cells_at_two_points :
    Conditions false twoPointStep (fun _ _ => True) (fun x y => x = y)
        (fun x y => x = y) ∧
      Conditions false twoPointStep (fun _ _ => True) (fun _ _ => True)
          (fun x y => x = y) ∧
        ¬ ((true : Bool) = false) ∧ ¬ ((false : Bool) = true) :=
  ⟨two_points_are_enough_with_total_similar,
   two_points_are_enough_with_total_congruent,
   fun e => Bool.noConfusion e, fun e => Bool.noConfusion e⟩

/-- **So the eight decide the operation and two thirds of the relations, and no
    more.** Forming is fixed outright, eight of the twelve relation cells are
    fixed in every model, and the remaining four are each fixed differently by
    two of the four models below --- `~~` at the ground-to-image cell by the
    first two, both off-diagonal cells of `=~` by the second and third, and `≡`
    at the ground-to-image cell by the second and fourth.

    The number to hold is not eight. It is that the clause set at its smallest
    carrier is one model wide in the operation and four cells wide in the
    relations, and "two Forms suffice" says none of that. -/
theorem the_eight_decide_forming_and_eight_of_twelve_cells :
    (∀ (ground : Bool) (f2f : Bool → Bool) (S C E : Bool → Bool → Prop),
        Conditions ground f2f S C E →
          (∀ x, f2f x = !ground) ∧
            (S (!ground) ground ∧ S (!ground) (!ground) ∧ S ground ground) ∧
            (C ground ground ∧ C (!ground) (!ground)) ∧
            (E ground ground ∧ E (!ground) (!ground) ∧ ¬ E (!ground) ground)) ∧
      Conditions false twoPointStep twoPointSimilar (fun x y => x = y)
          (fun x y => x = y) ∧
        Conditions false twoPointStep (fun _ _ => True) (fun x y => x = y)
            (fun x y => x = y) ∧
          Conditions false twoPointStep (fun _ _ => True) (fun _ _ => True)
              (fun x y => x = y) ∧
            Conditions false twoPointStep (fun _ _ => True) twoPointUpper
              twoPointUpper :=
  ⟨fun _ _ _ _ _ h =>
      ⟨forming_is_forced_at_two_points h, eight_cells_are_forced_at_two_points h⟩,
   two_points_are_enough, two_points_are_enough_with_total_similar,
   two_points_are_enough_with_total_congruent,
   two_points_are_enough_with_maximal_simulation⟩

namespace ThreeFormChoice

/-- Forming to the middle Form. -/
def stepOne (_ : Fin 3) : Fin 3 := 1

/-- Forming to the last Form. Everything else about the model is the same. -/
def stepTwo (_ : Fin 3) : Fin 3 := 2

theorem one_holds :
    Conditions (0 : Fin 3) stepOne (fun _ _ => True) (fun _ _ => True) Eq where
  simIntoCong _ _ _ := trivial
  congIntoSim _ _ _ := trivial
  imageSimilar _ := trivial
  imageSimilarToGround _ := trivial
  doubleImageSimilar _ := trivial
  imageNotSimulatingGround _ h := absurd h (by decide : ¬ ((1 : Fin 3) = 0))
  congruentDiagonalIsReach _ := ⟨fun _ => ⟨0, trivial⟩, fun _ => trivial⟩
  simulationDiagonalIsReach _ := ⟨fun _ => ⟨0, trivial⟩, fun _ => rfl⟩

theorem two_holds :
    Conditions (0 : Fin 3) stepTwo (fun _ _ => True) (fun _ _ => True) Eq where
  simIntoCong _ _ _ := trivial
  congIntoSim _ _ _ := trivial
  imageSimilar _ := trivial
  imageSimilarToGround _ := trivial
  doubleImageSimilar _ := trivial
  imageNotSimulatingGround _ h := absurd h (by decide : ¬ ((2 : Fin 3) = 0))
  congruentDiagonalIsReach _ := ⟨fun _ => ⟨0, trivial⟩, fun _ => trivial⟩
  simulationDiagonalIsReach _ := ⟨fun _ => ⟨0, trivial⟩, fun _ => rfl⟩

end ThreeFormChoice

/-- **At three Forms forming is a choice again.** The same relations, the same
    ground, two different forming maps. The sixth condition still forbids one
    value and now two are left, so it no longer names one. -/
theorem forming_is_not_forced_at_three_points :
    Conditions (0 : Fin 3) ThreeFormChoice.stepOne (fun _ _ => True)
        (fun _ _ => True) Eq ∧
      Conditions (0 : Fin 3) ThreeFormChoice.stepTwo (fun _ _ => True)
          (fun _ _ => True) Eq ∧
        ThreeFormChoice.stepOne 0 ≠ ThreeFormChoice.stepTwo 0 :=
  ⟨ThreeFormChoice.one_holds, ThreeFormChoice.two_holds, by decide⟩

/-- **The smallest carrier is the only one where the clause set writes its own
    operation.** Every model of the eight over two Forms has the same forming
    map, and over three Forms two models share everything else and disagree on
    forming. The mechanism is not about `Bool`: the clause set constrains
    forming only by a denial, and a denial of one value determines a function
    exactly when there is one value left. Minimality and rigidity are the same
    fact here, and they come apart at the next size up. -/
theorem two_points_determine_forming_and_three_do_not :
    (∀ (ground : Bool) (f2f : Bool → Bool) (S C E : Bool → Bool → Prop),
        Conditions ground f2f S C E → ∀ x, f2f x = !ground) ∧
      (Conditions (0 : Fin 3) ThreeFormChoice.stepOne (fun _ _ => True)
          (fun _ _ => True) Eq ∧
        Conditions (0 : Fin 3) ThreeFormChoice.stepTwo (fun _ _ => True)
            (fun _ _ => True) Eq ∧
          ThreeFormChoice.stepOne 0 ≠ ThreeFormChoice.stepTwo 0) :=
  ⟨fun _ _ _ _ _ h => forming_is_forced_at_two_points h,
   forming_is_not_forced_at_three_points⟩

/-! ### A carrier with an unreached point, where they do not -/

/-- The chain with one extra Form adjoined. Forming fixes it, so it is its own
image and nothing in the chain ever produces it. -/
abbrev Extended := Option Nat
def extGround : Extended := some 0
def extStep : Extended → Extended
  | some n => some (n + 1)
  | none => none

/-- `x ~~ y` unless y is the adjoined point and x is not. Every clause about
similarity of an image is satisfied, because the adjoined point is its own
image. -/
def extSimilar (x y : Extended) : Prop := y ≠ none ∨ x = none

/-- Equality restricted to the chain: the adjoined point is not `=~` or `≡` to
itself. -/
def extDiagonal (x y : Extended) : Prop := x = y ∧ y ≠ none

theorem ext_repeat (n : Nat) : Nat.repeat extStep n extGround = some n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.repeat, ih, extStep]

theorem ext_none_unreached : ¬ Reach extGround extStep extSimilar none := by
  rintro ⟨n, h⟩
  rw [ext_repeat] at h
  rcases h with h | h
  · exact h rfl
  · exact Option.noConfusion h

theorem ext_reach_some (n : Nat) : Reach extGround extStep extSimilar (some n) :=
  ⟨n + 1, by rw [ext_repeat]; exact Or.inl (fun h => Option.noConfusion h)⟩

theorem ext_conditions :
    Conditions extGround extStep extSimilar extDiagonal extDiagonal where
  simIntoCong := fun _ _ h => h
  congIntoSim := fun _ _ h => Or.inl h.2
  imageSimilar := fun x => match x with
    | some _ => Or.inl (fun h => Option.noConfusion h)
    | none => Or.inr rfl
  imageSimilarToGround := fun _ => Or.inl (fun h => Option.noConfusion h)
  doubleImageSimilar := fun x => match x with
    | some _ => Or.inl (fun h => Option.noConfusion h)
    | none => Or.inr rfl
  imageNotSimulatingGround := by
    rintro (_ | n) ⟨e, -⟩ <;> simp [extStep, extGround] at e
  congruentDiagonalIsReach := by
    intro x
    constructor
    · rintro ⟨-, hne⟩
      match x with
      | some n => exact ext_reach_some n
      | none => exact absurd rfl hne
    · intro hr
      refine ⟨rfl, ?_⟩
      rintro rfl
      exact ext_none_unreached hr
  simulationDiagonalIsReach := by
    intro x
    constructor
    · rintro ⟨-, hne⟩
      match x with
      | some n => exact ext_reach_some n
      | none => exact absurd rfl hne
    · intro hr
      refine ⟨rfl, ?_⟩
      rintro rfl
      exact ext_none_unreached hr

/-- **The reflexivity column, recovered inside the characterization.** All 24
clauses hold, `~~` is reflexive, and `=~` is not.

`IrreflexiveSimilar` already refuted `=~`-reflexivity, but there `~~` was
irreflexive too, which left the reading that a badly behaved bottom level was
doing the work. It was not. The only thing required is a Form the ground chain
never reaches; conditions 7 and 8 then withhold the diagonal at that Form and
nothing else changes. A statement over the chain carrier alone could not have
said this, because there is no such Form there. -/
theorem congruent_reflexivity_needs_an_unreached_point :
    PrefixAxioms extGround extStep extSimilar extDiagonal extDiagonal ∧
      (∀ x, extSimilar x x) ∧
      ¬ (∀ x, extDiagonal x x) :=
  ⟨prefixAxioms_of_conditions ext_conditions,
    fun x => match x with
      | some _ => Or.inl (fun h => Option.noConfusion h)
      | none => Or.inr rfl,
    fun refl => (refl none).2 rfl⟩

/-- **The composite inclusion is always strict and neither link is forced to
be.** `similarity_is_not_contained_in_simulation` says `~~` is never contained
in `≡` in any model of the eight. Which link carries that is open: the first
model here collapses the upper link, the second collapses the lower one. So
three relations is not three by necessity at either link, and is three by
necessity overall: either pair may be made to coincide, and
`the_three_relations_are_never_all_one` says no model collapses both. -/
theorem neither_inclusion_is_forced_to_be_strict :
    Conditions chainGround chainStep (fun _ _ => True) (fun _ _ => True)
        (fun x y => x = y) ∧
      Conditions extGround extStep extSimilar extDiagonal extDiagonal :=
  ⟨congruent_may_equal_similar, ext_conditions⟩

/-! ### The other corner: what the clauses say about `~~`

`total_similar_leaves_exactly_three_conditions` fixes `~~` to answer about the
two relations above it, and the two freedom theorems above fix two relations to
answer about the third. Every one of them holds `~~` still, which is why none of
them says what the clauses assert about `~~` itself --- the relation the others
are measured against was never the subject.

Taking the upper two relations to their minimum answers it. `=~` and `≡` must
contain equality and may be nothing more, so set both to equality. The two
diagonal conditions then read `True ↔ Reach`, which forces the ground chain to
reach everything: `globalCongruentReflexivityIsCofinality` in the layer states
the same implication from the clause side, and here it appears as what happens
to the characterization at its lower corner.

What is left is not freedom. `≡` and `=~` are free above equality, and `~~` is
not free at all. -/

/-- What is left of the eight when both upper relations are equality: five
conditions on `~~` and one on forming. Named as a structure for the same reason
`Conditions` is --- so each one can be dropped by name. -/
structure SimilarConditions (ground : Form) (f2f : Form → Form)
    (S : Form → Form → Prop) : Prop where
  similarReflexive : ∀ x, S x x
  imageSimilar : ∀ x, S (f2f x) x
  imageSimilarToGround : ∀ x, S (f2f x) ground
  doubleImageSimilar : ∀ x, S (f2f (f2f x)) x
  chainIsCofinal : ∀ x, Reach ground f2f S x
  formingAvoidsGround : ∀ x, f2f x ≠ ground

theorem minimal_upper_relations_leave_five_conditions_on_similar
    (ground : Form) (f2f : Form → Form) (S : Form → Form → Prop) :
    Conditions ground f2f S (fun x y => x = y) (fun x y => x = y) ↔
      SimilarConditions ground f2f S :=
  ⟨fun h =>
      { similarReflexive := fun x => h.congIntoSim x x rfl
        imageSimilar := h.imageSimilar
        imageSimilarToGround := h.imageSimilarToGround
        doubleImageSimilar := h.doubleImageSimilar
        chainIsCofinal := fun x => (h.congruentDiagonalIsReach x).mp rfl
        formingAvoidsGround := h.imageNotSimulatingGround },
    fun h =>
      { simIntoCong := fun _ _ k => k
        congIntoSim := fun x y k => k ▸ h.similarReflexive x
        imageSimilar := h.imageSimilar
        imageSimilarToGround := h.imageSimilarToGround
        doubleImageSimilar := h.doubleImageSimilar
        imageNotSimulatingGround := h.formingAvoidsGround
        congruentDiagonalIsReach := fun x => ⟨fun _ => h.chainIsCofinal x, fun _ => rfl⟩
        simulationDiagonalIsReach := fun x => ⟨fun _ => h.chainIsCofinal x, fun _ => rfl⟩ }⟩

/-- **Cofinality is the one of the six that does not come free with the others.**
The adjoined carrier satisfies the four similarity conditions and the denial,
and its extra point is reached by nothing: forming fixes it, so no iterate of
ground produces it and `~~` does not relate it to one. On the chain the question
never arises --- `reach_is_total_on_the_chain` gets cofinality out of the third
condition alone --- which is exactly why the carrier has to be open for the
corner to say anything. -/
theorem five_hold_without_chainIsCofinal :
    ((∀ x, extSimilar x x) ∧ (∀ x, extSimilar (extStep x) x) ∧
      (∀ x, extSimilar (extStep x) extGround) ∧
      (∀ x, extSimilar (extStep (extStep x)) x) ∧
      ∀ x, extStep x ≠ extGround) ∧
    ¬ ∀ x, Reach extGround extStep extSimilar x :=
  ⟨⟨fun x => match x with
      | some _ => Or.inl (fun h => Option.noConfusion h)
      | none => Or.inr rfl,
    fun x => match x with
      | some _ => Or.inl (fun h => Option.noConfusion h)
      | none => Or.inr rfl,
    fun _ => Or.inl (fun h => Option.noConfusion h),
    fun x => match x with
      | some _ => Or.inl (fun h => Option.noConfusion h)
      | none => Or.inr rfl,
    fun x => by
      cases x with
      | some n => intro h; exact Nat.succ_ne_zero n (Option.some.inj h)
      | none => intro h; exact Option.noConfusion h⟩,
   fun reaches => ext_none_unreached (reaches none)⟩

/-! #### Each of the six is needed

Six conditions and an iff say what the clauses assert about `~~`; they do not
say that six is the number of facts. Four of the six could have been consequences
of the others and the statement would read the same. Each is dropped here in
turn, so the list is irredundant and the count is a measurement.

Five of the six are dropped on the chain with a relation chosen to fail exactly
one condition; the sixth needs a carrier where forming returns to ground, which
the chain cannot do, and cofinality needs one where the chain misses a point,
which is `five_hold_without_chainIsCofinal` above. -/

/-- Strictly more formed. Reflexivity is the only condition this fails. -/
def strictlyAbove (x y : Chain) : Prop := y < x

theorem five_hold_without_similarReflexive :
    ((∀ x, strictlyAbove (chainStep x) x) ∧
      (∀ x, strictlyAbove (chainStep x) chainGround) ∧
      (∀ x, strictlyAbove (chainStep (chainStep x)) x) ∧
      (∀ x, Reach chainGround chainStep strictlyAbove x) ∧
      ∀ x, chainStep x ≠ chainGround) ∧
    ¬ ∀ x, strictlyAbove x x :=
  ⟨⟨fun x => Nat.lt_succ_self x,
    fun x => Nat.zero_lt_succ x,
    fun x => Nat.lt_of_lt_of_le (Nat.lt_succ_self x) (Nat.le_succ _),
    fun x => ⟨x + 1, by rw [repeat_from_chainGround]; exact Nat.lt_succ_self x⟩,
    fun x => Nat.succ_ne_zero x⟩,
   fun reflexive => absurd (reflexive 0) (Nat.lt_irrefl 0)⟩

/-- Equal, or at ground, or two steps up. The single step is the gap. -/
def skipsOneStep (x y : Chain) : Prop := x = y ∨ y = 0 ∨ x = y + 2

theorem five_hold_without_imageSimilar :
    ((∀ x, skipsOneStep x x) ∧
      (∀ x, skipsOneStep (chainStep x) chainGround) ∧
      (∀ x, skipsOneStep (chainStep (chainStep x)) x) ∧
      (∀ x, Reach chainGround chainStep skipsOneStep x) ∧
      ∀ x, chainStep x ≠ chainGround) ∧
    ¬ ∀ x, skipsOneStep (chainStep x) x :=
  ⟨⟨fun _ => Or.inl rfl,
    fun _ => Or.inr (Or.inl rfl),
    fun _ => Or.inr (Or.inr rfl),
    fun x => ⟨x, by rw [repeat_from_chainGround]; exact Or.inl rfl⟩,
    fun x => Nat.succ_ne_zero x⟩,
   fun image => by
     rcases image 1 with h | h | h <;> exact absurd h (by decide)⟩

/-- Within two steps. Every image is similar to its source, and to ground only
from the bottom of the chain. -/
def withinTwoSteps (x y : Chain) : Prop := x = y ∨ x = y + 1 ∨ x = y + 2

theorem five_hold_without_imageSimilarToGround :
    ((∀ x, withinTwoSteps x x) ∧
      (∀ x, withinTwoSteps (chainStep x) x) ∧
      (∀ x, withinTwoSteps (chainStep (chainStep x)) x) ∧
      (∀ x, Reach chainGround chainStep withinTwoSteps x) ∧
      ∀ x, chainStep x ≠ chainGround) ∧
    ¬ ∀ x, withinTwoSteps (chainStep x) chainGround :=
  ⟨⟨fun _ => Or.inl rfl,
    fun _ => Or.inr (Or.inl rfl),
    fun _ => Or.inr (Or.inr rfl),
    fun x => ⟨x, by rw [repeat_from_chainGround]; exact Or.inl rfl⟩,
    fun x => Nat.succ_ne_zero x⟩,
   fun toGround => by
     rcases toGround 2 with h | h | h <;> exact absurd h (by decide)⟩

/-- One step, or at ground. The double image is the gap. -/
def oneStepOrGround (x y : Chain) : Prop := x = y ∨ x = y + 1 ∨ y = 0

theorem five_hold_without_doubleImageSimilar :
    ((∀ x, oneStepOrGround x x) ∧
      (∀ x, oneStepOrGround (chainStep x) x) ∧
      (∀ x, oneStepOrGround (chainStep x) chainGround) ∧
      (∀ x, Reach chainGround chainStep oneStepOrGround x) ∧
      ∀ x, chainStep x ≠ chainGround) ∧
    ¬ ∀ x, oneStepOrGround (chainStep (chainStep x)) x :=
  ⟨⟨fun _ => Or.inl rfl,
    fun _ => Or.inr (Or.inl rfl),
    fun _ => Or.inr (Or.inr rfl),
    fun x => ⟨x, by rw [repeat_from_chainGround]; exact Or.inl rfl⟩,
    fun x => Nat.succ_ne_zero x⟩,
   fun double => by
     rcases double 1 with h | h | h <;> exact absurd h (by decide)⟩

/-- The one-point carrier: forming is the identity, so it returns to ground
immediately. Everything else holds because the relation is total. -/
theorem five_hold_without_formingAvoidsGround :
    ((∀ x : Unit, (fun _ _ => True) x x) ∧
      (∀ x : Unit, (fun _ _ => True) (id x) x) ∧
      (∀ x : Unit, (fun _ _ => True) (id x) ()) ∧
      (∀ x : Unit, (fun _ _ => True) (id (id x)) x) ∧
      (∀ x : Unit, Reach () id (fun _ _ => True) x)) ∧
    ¬ ∀ x : Unit, id x ≠ () :=
  ⟨⟨fun _ => trivial, fun _ => trivial, fun _ => trivial, fun _ => trivial,
    fun _ => ⟨0, trivial⟩⟩,
   fun avoids => avoids () rfl⟩

-- ----------------------------------------------------------------------------
-- The operation layer, characterised the same way
--
-- `prefixAxioms_iff_conditions` covers 24 of the 39 clauses. Seven more are the
-- operation clauses, and they are pure `S`/`C`: no operation clause mentions
-- `E`, so whatever they add, they add nothing about simulation.
--
-- They are also mostly each other. `axSeq` and `axCoop` are one proposition,
-- the three identity clauses are one, and both fall out of `axCoopComm` and
-- `axCoopIdentity` -- see `Hypermath.commonWitnessesComeFromCommutativity`.
-- Seven clauses, three conditions.
-- ----------------------------------------------------------------------------

/-- The seven operation clauses over arbitrary `S` and `C`, on any carrier. -/
structure OperationAxioms (S C : Form → Form → Prop) : Prop where
  axSeq : ∀ a b, ∃ c, S c a ∧ S c b
  axSeqAsymm : ∀ a b, ¬ C a b →
    ∃ c d, S c a ∧ S c b ∧ S d b ∧ S d a ∧ ¬ C c d
  axSeqIdentityR : ∀ a, ∃ c, S c a ∧ C c a
  axSeqIdentityL : ∀ a, ∃ c, S c a ∧ C c a
  axCoop : ∀ a b, ∃ c, S c a ∧ S c b
  axCoopComm : ∀ a b, ∃ ca cab, S ca a ∧ S ca b ∧ S cab b ∧ S cab a ∧ C ca cab
  axCoopIdentity : ∀ a, ∃ c, S c a ∧ C c a

/-- What the seven say, without the repetition: a congruent pair of common
    witnesses for every pair, one witness congruent to each Form, and an
    incongruent pair of witnesses whenever two Forms are already incongruent. -/
structure OperationConditions (S C : Form → Form → Prop) : Prop where
  pairedWitnesses : ∀ a b, ∃ ca cab, S ca a ∧ S ca b ∧ S cab b ∧ S cab a ∧ C ca cab
  identityWitness : ∀ a, ∃ c, S c a ∧ C c a
  apartWitnesses : ∀ a b, ¬ C a b →
    ∃ c d, S c a ∧ S c b ∧ S d b ∧ S d a ∧ ¬ C c d

theorem operationConditions_of_operationAxioms {S C : Form → Form → Prop}
    (h : OperationAxioms S C) : OperationConditions S C where
  pairedWitnesses := h.axCoopComm
  identityWitness := h.axCoopIdentity
  apartWitnesses := h.axSeqAsymm

theorem operationAxioms_of_operationConditions {S C : Form → Form → Prop}
    (h : OperationConditions S C) : OperationAxioms S C where
  axSeq := fun a b =>
    let ⟨ca, _, ca_a, ca_b, _, _, _⟩ := h.pairedWitnesses a b
    ⟨ca, ca_a, ca_b⟩
  axSeqAsymm := h.apartWitnesses
  axSeqIdentityR := h.identityWitness
  axSeqIdentityL := h.identityWitness
  axCoop := fun a b =>
    let ⟨ca, _, ca_a, ca_b, _, _, _⟩ := h.pairedWitnesses a b
    ⟨ca, ca_a, ca_b⟩
  axCoopComm := h.pairedWitnesses
  axCoopIdentity := h.identityWitness

/-- **Seven operation clauses, three conditions.** Four of the seven are carried
    by two of the three, and the third is `axSeqAsymm`, which fires only where
    something is already incongruent. -/
theorem operationAxioms_iff_conditions (S C : Form → Form → Prop) :
    OperationAxioms S C ↔ OperationConditions S C :=
  ⟨operationConditions_of_operationAxioms, operationAxioms_of_operationConditions⟩

/-- **31 of the 39 clauses, eleven conditions, arbitrary carrier, no axioms.**
    The two characterisations compose as statements: the eight constrain `S`,
    `C` and `E`, the three add only witnesses in `S` and `C`, and no operation
    clause mentions `E`, so everything the clause set says about simulation is
    already in the eight.

    They do not compose as *freedoms*. See
    `operations_exclude_the_unreached_point`. -/
theorem prefixWithOperations_iff_conditions (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) :
    (PrefixAxioms ground f2f S C E ∧ OperationAxioms S C) ↔
      (Conditions ground f2f S C E ∧ OperationConditions S C) :=
  ⟨fun h => ⟨conditions_of_prefixAxioms h.1, operationConditions_of_operationAxioms h.2⟩,
    fun h => ⟨prefixAxioms_of_conditions h.1, operationAxioms_of_operationConditions h.2⟩⟩

-- ----------------------------------------------------------------------------
-- Incidence one is two answers
--
-- The incidence table settles the row of zero by itself: a symbol no clause
-- mentions cannot be constrained by the clauses. The row of one it does not
-- settle, because two clause shapes sit in it and they point opposite ways.
--
-- `closeDefinitionOpaque` and `closeDischargeOpaque` are biconditionals reading
-- a symbol off another. A symbol named by one of those is *determined*: it has
-- no freedom at all, and the clause adds no strength, only a name.
--
-- `axLimitDerives` names `pathStart` and `pathEnd` under an existential. A
-- symbol named that way is pinned at a single point and free everywhere else.
--
-- Both are proved below over an arbitrary carrier, so the count tells you which
-- symbols to look at and the shape of the clause tells you what you find.
-- ----------------------------------------------------------------------------

/-- The one clause of the 39 that mentions either path endpoint. Stated over an
    arbitrary carrier and an arbitrary path type, because what it does to those
    two symbols does not depend on either. -/
structure LimitPathClause {Path : Type} (S C : Form → Form → Prop)
    (gr lim : Form) (ps pe : Path → Form) : Prop where
  someLimitPath : ∃ p : Path, S (ps p) gr ∧ C (pe p) lim

/-- Overwrite an assignment at one point. -/
def graft {Path : Type} [DecidableEq Path] (w : Path) (a : Form)
    (g : Path → Form) : Path → Form :=
  fun p => if p = w then a else g p

theorem graft_at {Path : Type} [DecidableEq Path] (w : Path) (a : Form)
    (g : Path → Form) : graft w a g w = a := by
  simp [graft]

theorem graft_off {Path : Type} [DecidableEq Path] (w : Path) (a : Form)
    (g : Path → Form) {p : Path} (hp : p ≠ w) : graft w a g p = g p := by
  simp [graft, hp]

/-- **An existential clause pins one point and frees the rest.** Take any model
    of the clause and any two assignments of endpoints whatever. Keeping the
    model's values at its own witness and taking the arbitrary ones everywhere
    else satisfies the clause again.

    So `axLimitDerives` constrains `pathStart` and `pathEnd` at a single path
    and says nothing about either at any other. That is what the note means by
    calling them as free as the symbols no clause mentions: free, but at every
    path except one rather than at every path. -/
theorem endpoints_free_off_one_path {Path : Type} [DecidableEq Path]
    {S C : Form → Form → Prop} {gr lim : Form} {ps pe : Path → Form}
    (h : LimitPathClause S C gr lim ps pe) (g g' : Path → Form) :
    ∃ w : Path,
      LimitPathClause S C gr lim (graft w (ps w) g) (graft w (pe w) g')
      ∧ ∀ p : Path, p ≠ w →
          graft w (ps w) g p = g p ∧ graft w (pe w) g' p = g' p := by
  obtain ⟨w, hs, hc⟩ := h.someLimitPath
  refine ⟨w, ⟨⟨w, ?_, ?_⟩⟩, fun p hp => ⟨graft_off _ _ _ hp, graft_off _ _ _ hp⟩⟩
  · rw [graft_at]; exact hs
  · rw [graft_at]; exact hc

/-- **A closing clause determines its symbol outright.** Two readings that both
    satisfy the same biconditional are the same relation, so a symbol named by
    one of those has no freedom whatever and the clause adds a name rather than
    a constraint.

    This is the opposite end of the row of one from
    `endpoints_free_off_one_path`, and it covers `Definition`, `Discharge`,
    `HMSyntax`, `Substance`, `Semantics`, `FormClosure` and `Derives`: every
    symbol whose only clause is a close. -/
theorem determined_by_its_closing_clause {R : Form → Form → Prop}
    (D₁ D₂ : Form → Form → Prop)
    (h₁ : ∀ x y, D₁ x y ↔ R x y) (h₂ : ∀ x y, D₂ x y ↔ R x y) : D₁ = D₂ := by
  funext x y
  exact propext ((h₁ x y).trans (h₂ x y).symm)

/-- **One clause, two opposite outcomes.** Both halves are about a symbol that
    exactly one of the 39 clauses mentions, and they disagree completely: under
    an existential the symbol keeps every value but one, under a biconditional
    it keeps none.

    The incidence count is therefore a way of choosing what to examine and not
    an answer by itself. It is an answer by itself only at zero, where there is
    no clause whose shape could be read --- which is the case
    `Ordinatics.Transfinite.apply_is_free` settles in the repository this one
    depends on. -/
theorem incidence_one_is_two_cases {Path : Type} [DecidableEq Path]
    {S C R : Form → Form → Prop} {gr lim : Form} {ps pe : Path → Form}
    (h : LimitPathClause S C gr lim ps pe) :
    (∀ g g' : Path → Form, ∃ w : Path,
        LimitPathClause S C gr lim (graft w (ps w) g) (graft w (pe w) g')
        ∧ ∀ p : Path, p ≠ w →
            graft w (ps w) g p = g p ∧ graft w (pe w) g' p = g' p)
    ∧ (∀ D₁ D₂ : Form → Form → Prop,
        (∀ x y, D₁ x y ↔ R x y) → (∀ x y, D₂ x y ↔ R x y) → D₁ = D₂) :=
  ⟨fun g g' => endpoints_free_off_one_path h g g',
    fun _ _ h₁ h₂ => determined_by_its_closing_clause _ _ h₁ h₂⟩

/-- The same 24 clauses again, with three further symbols carried alongside that
    none of them uses. The names are `pathLength`, `pathStep` and `pathTrace`'s
    types: the three symbols the incidence table puts in its zero row.

    Nothing here is a model. `ground`, `f2f`, `S`, `C` and `E` are opaque, so
    `assumption` on a field of this structure can only succeed by matching the
    corresponding hypothesis --- which is what makes the transfer below a check
    rather than a restatement. -/
structure PrefixAxiomsCarrying (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) {Path : Type}
    (pl : Path → Form) (ps : Form → Form → Path) (pt : Path → Form) : Prop where
  axDiff : ∀ x, structDistinct E (f2f x) ground
  axSim : ∀ x, structContinues ground S (f2f x) ground
  axBox : ∀ x, structOrbits S (f2f (f2f x)) x
  axGroundSelf : structContinues ground S ground ground
  closeStructContinues : ∀ x, structContinues ground S x ground ↔ S x ground
  closeStructDistinct : ∀ x y, structDistinct E x y ↔ ¬ E x y
  closeStructOrbits : ∀ x, structOrbits S (f2f (f2f x)) x ↔ S (f2f (f2f x)) x
  axSyntaxRequiresSubstance : ∀ x, HMSyntax ground f2f S x → Substance C x
  axSubstanceRequiresSemantics : ∀ x, Substance C x → Semantics E x
  axSemanticsRequiresSyntax : ∀ x, Semantics E x → HMSyntax ground f2f S x
  axFormClosesLoop : ∀ x, HMSyntax ground f2f S x → Semantics E x →
    FormClosure ground f2f S C E x
  axGroundSyntaxAx : HMSyntax ground f2f S ground
  axGroundSubstanceAx : Substance C ground
  axGroundSemanticsAx : Semantics E ground
  filtrationSimCong : ∀ x y, E x y → C x y
  filtrationCongSim : ∀ x y, C x y → S x y
  closeSyntaxOpaque : ∀ x, HMSyntax ground f2f S x ↔ ∃ n : Nat, S (Nat.repeat f2f n ground) x
  closeSubstanceOpaque : ∀ x, Substance C x ↔ C x x
  closeSemanticsOpaque : ∀ x, Semantics E x ↔ E x x
  closeDerivesOpaque : ∀ x y, Derives f2f C x y ↔ ∃ n : Nat, C (Nat.repeat f2f n x) y
  closeDischargeOpaque : ∀ c e, Discharge f2f C c e ↔ Derives f2f C e c
  closeDefinitionOpaque : ∀ n x, Definition f2f C n x ↔ Derives f2f C n x
  closeFormClosureOpaque : ∀ x, FormClosure ground f2f S C E x ↔ HMSyntax ground f2f S x ∧ Substance C x ∧ Semantics E x
  traceLevels : ∀ x, S (f2f x) x ∧ (C (f2f x) x → S (f2f x) x) ∧
    (E (f2f x) x → C (f2f x) x)

/-- **A symbol no clause mentions is free, and the kernel says so.** Any reading
    of all three at once satisfies the 24 clauses as soon as one does. The proof
    is two tactics, and both of them are the point: `cases` produces the 24
    hypotheses, `constructor` produces the 24 goals at the *new* assignment, and
    `assumption` pairs them off. Over an arbitrary carrier there is nothing to
    unfold, so a clause that mentioned `pl`, `ps` or `pt` would leave a goal no
    hypothesis matches. -/
theorem carried_symbols_are_free {ground : Form} {f2f : Form → Form}
    {S C E : Form → Form → Prop} {Path : Type}
    {pl : Path → Form} {ps : Form → Form → Path} {pt : Path → Form}
    (h : PrefixAxiomsCarrying ground f2f S C E pl ps pt)
    (pl' : Path → Form) (ps' : Form → Form → Path) (pt' : Path → Form) :
    PrefixAxiomsCarrying ground f2f S C E pl' ps' pt' := by
  cases h
  constructor <;> assumption

/-- Carrying the three changes nothing, in either direction: the 24 clauses are
    the same 24 propositions with or without them. -/
theorem carrying_iff_prefix {ground : Form} {f2f : Form → Form}
    {S C E : Form → Form → Prop} {Path : Type}
    (pl : Path → Form) (ps : Form → Form → Path) (pt : Path → Form) :
    PrefixAxiomsCarrying ground f2f S C E pl ps pt ↔ PrefixAxioms ground f2f S C E := by
  constructor
  · intro h; cases h; constructor <;> assumption
  · intro h; cases h; constructor <;> assumption

/-- **The zero row, mechanized.** Read with `prefixAxioms_iff_conditions`, which
    says what the 24 clauses *do* constrain, this says what they constrain
    nothing about: everything the clauses assert is compatible with every
    reading whatever of the three symbols they never name. No model appears, and
    no model could --- a model may interpret an unused symbol's clause vacuously
    and transfer it anyway, which is how the first version of this theorem
    passed while checking nothing. -/
theorem the_unmentioned_are_unconstrained {ground : Form} {f2f : Form → Form}
    {S C E : Form → Form → Prop} {Path : Type}
    {pl : Path → Form} {ps : Form → Form → Path} {pt : Path → Form} :
    PrefixAxioms ground f2f S C E →
      ∀ (pl' : Path → Form) (ps' : Form → Form → Path) (pt' : Path → Form),
        PrefixAxiomsCarrying ground f2f S C E pl' ps' pt' :=
  fun h => carried_symbols_are_free ((carrying_iff_prefix pl ps pt).mpr h)

/-- **The eleven conditions are not eight plus three.** `ext_conditions`
    satisfies the eight with one Form the ground chain never reaches, which is
    what `congruent_reflexivity_needs_an_unreached_point` runs on. The three
    operation conditions are unsatisfiable there.

    `identityWitness` at the unreached point needs some `c` similar to it and
    congruent to it. Nothing is similar to it but itself, and the diagonal
    conditions deny congruence at anything unreached --- so the witness would
    have to be the point, and at the point congruence is exactly what is
    withheld.

    Counting the two lists together is therefore right and reading them as
    independent is not: adding the operation layer to the prefix does not enlarge
    what is constrained about `E`, but it does shrink which prefix models
    survive. A freedom proved against 24 clauses has to be re-checked against
    31. -/
theorem operations_exclude_the_unreached_point :
    Conditions extGround extStep extSimilar extDiagonal extDiagonal ∧
      ¬ OperationConditions extSimilar extDiagonal :=
  ⟨ext_conditions, fun h => by
    obtain ⟨c, similar, congruent⟩ := h.identityWitness none
    rcases similar with h' | rfl
    · exact h' rfl
    · exact congruent.2 rfl⟩

-- ----------------------------------------------------------------------------
-- The third list, and the first join that adds up
--
-- `prefixWithOperations_iff_conditions` reaches 31 of the 39 clauses, and
-- `operations_exclude_the_unreached_point` warns that the two lists it joins do
-- not compose as freedoms: a model of the eight can make the three
-- unsatisfiable, because the operation clauses speak the same `S` and `C` the
-- prefix constrains.
--
-- The three composition clauses are the opposite case, and the incidence table
-- says so before any proof is attempted. They mention `compose`, `pathGround`
-- and `congruentPath`; no condition among the eleven mentions any of the three.
-- Disjoint symbols, disjoint content, and a join that is a union.
-- ----------------------------------------------------------------------------

/-- The three §XIV clauses, over an arbitrary path type. `axComposeNonempty` is
    copied with its binders as the source has them: two `Form` arguments the
    statement never uses. -/
structure ComposeAxioms {Path : Type} (cp : Path → Path → Prop)
    (comp : Path → Path → Path) (e : Path) : Prop where
  axComposeAssoc : ∀ p q r : Path, cp (comp p (comp q r)) (comp (comp p q) r)
  axComposeIdentity : ∀ p : Path, cp (comp p e) p ∧ cp (comp e p) p
  axComposeNonempty : Form → Form → ∃ p : Path, ¬ cp p e

/-- What the three say. Two are copied unchanged, and the third has lost the two
    binders it never used. -/
structure ComposeConditions {Path : Type} (cp : Path → Path → Prop)
    (comp : Path → Path → Path) (e : Path) : Prop where
  associativeUpToCp : ∀ p q r : Path, cp (comp p (comp q r)) (comp (comp p q) r)
  unitalUpToCp : ∀ p : Path, cp (comp p e) p ∧ cp (comp e p) p
  someNonUnit : ∃ p : Path, ¬ cp p e

/-- **`axComposeNonempty`'s two binders are inert.** Its docstring promises a
    path connecting any two Forms; the statement takes two Forms and cannot
    mention them, so one Form is enough to strip both and any Form will do. The
    clause's whole content is that something is not the unit.

    This is the row-of-zero reading applied inside a single clause rather than
    across the clause set: a binder no part of the statement uses constrains
    nothing, exactly as a symbol no clause names does. -/
theorem compose_nonempty_binders_are_inert (x : Form) {Path : Type}
    (cp : Path → Path → Prop) (e : Path) :
    (Form → Form → ∃ p : Path, ¬ cp p e) ↔ (∃ p : Path, ¬ cp p e) :=
  ⟨fun h => h x x, fun h _ _ => h⟩

/-- The three clauses are the three conditions, given one Form to discharge the
    inert binders with. -/
theorem composeAxioms_iff_conditions (x : Form) {Path : Type}
    (cp : Path → Path → Prop) (comp : Path → Path → Path) (e : Path) :
    ComposeAxioms (Form := Form) cp comp e ↔ ComposeConditions cp comp e :=
  ⟨fun h => ⟨h.axComposeAssoc, h.axComposeIdentity, h.axComposeNonempty x x⟩,
   fun h => ⟨h.associativeUpToCp, h.unitalUpToCp, fun _ _ => h.someNonUnit⟩⟩

/-- **34 of the 39 clauses, fourteen conditions, arbitrary carrier and arbitrary
    path type.** What remains outside is the five transfinite projections of the
    `ordinatics` instance, which are declared in another repository. -/
theorem prefixOperationsCompose_iff_conditions (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) {Path : Type} (cp : Path → Path → Prop)
    (comp : Path → Path → Path) (e : Path) :
    (PrefixAxioms ground f2f S C E ∧ OperationAxioms S C ∧
        ComposeAxioms (Form := Form) cp comp e) ↔
      (Conditions ground f2f S C E ∧ OperationConditions S C ∧
        ComposeConditions cp comp e) :=
  ⟨fun h => ⟨conditions_of_prefixAxioms h.1,
      operationConditions_of_operationAxioms h.2.1,
      (composeAxioms_iff_conditions ground cp comp e).mp h.2.2⟩,
   fun h => ⟨prefixAxioms_of_conditions h.1,
      operationAxioms_of_operationConditions h.2.1,
      (composeAxioms_iff_conditions ground cp comp e).mpr h.2.2⟩⟩

/-- **The composition layer excludes nothing.** Any monoid with a non-unit
    satisfies all three conditions with `congruentPath` read as equality --- the
    naturals under addition will do. Compare
    `operations_exclude_the_unreached_point`, where no such witness exists
    because the operation conditions have to be met by relations the prefix has
    already fixed. -/
theorem compose_conditions_are_always_available :
    ComposeConditions (Path := Nat) Eq (· + ·) 0 where
  associativeUpToCp p q r := (Nat.add_assoc p q r).symm
  unitalUpToCp p := ⟨Nat.add_zero p, Nat.zero_add p⟩
  someNonUnit := ⟨1, Nat.succ_ne_zero 0⟩

/-- **Two joins, two answers, and the incidence table predicts both.** The first
    conjunct is `operations_exclude_the_unreached_point`: a model of the eight
    prefix conditions where the three operation conditions cannot be met. The
    second is the composition layer arriving free, on top of *any* model of the
    eleven whatever, because its three conditions constrain three symbols the
    eleven never mention.

    The second proof is `⟨h, hops, …⟩` and that is the whole of it. A trivial
    proof is the right outcome here rather than a weak one: what had to be
    checked was whether anything could obstruct, and disjoint incidence is why
    nothing can. Clause lists compose as freedoms exactly when the symbols they
    name are disjoint; when they overlap, the join has to be measured. -/
theorem lists_join_freely_exactly_on_disjoint_symbols
    {ground : Form} {f2f : Form → Form} {S C E : Form → Form → Prop}
    (h : Conditions ground f2f S C E) (hops : OperationConditions S C) :
    (Conditions extGround extStep extSimilar extDiagonal extDiagonal ∧
        ¬ OperationConditions extSimilar extDiagonal) ∧
      (Conditions ground f2f S C E ∧ OperationConditions S C ∧
        ComposeConditions (Path := Nat) Eq (· + ·) 0) :=
  ⟨operations_exclude_the_unreached_point, h, hops, compose_conditions_are_always_available⟩

-- ----------------------------------------------------------------------------
-- Why the associativity clause is never spent
--
-- `axComposeAssoc` is one of five declared names that nothing in
-- `lean4/Hypermath/` consumes; the sweep says it is idle and does not say why.
-- The reason is a gap between two clauses written apart from each other. The
-- clause asserts associativity *up to* `congruentPath`, and nothing anywhere
-- declares `congruentPath` transitive.
--
-- Associativity is used by chaining. Four factors need two rebracketings with a
-- transitivity step between them, and that step is the one thing missing. The
-- pair below is the whole of it: with transitivity the four-fold law follows
-- from the clause alone, and without it the clause holds in a model where the
-- four-fold law fails. The model keeps its relation reflexive, so reflexivity
-- is not what is wanted here and transitivity is.
-- ----------------------------------------------------------------------------

namespace ComposeNeedsTransitivity

/-- The four-fold law: the two extreme bracketings of `p q r s` are related.
    This is the first consequence of associativity that a single instance of
    the clause cannot reach, and it is one transitivity step away. -/
def FourFold {Path : Type} (cp : Path → Path → Prop)
    (comp : Path → Path → Path) : Prop :=
  ∀ p q r s : Path,
    cp (comp p (comp q (comp r s))) (comp (comp (comp p q) r) s)

/-- **Transitivity is sufficient, and by itself.** No congruence rule, no
    symmetry, no reflexivity, and no use of either other clause: two instances
    of `axComposeAssoc` meet at `comp (comp p q) (comp r s)`, and transitivity
    joins them there. -/
theorem fourFold_of_transitive {Path : Type} {cp : Path → Path → Prop}
    {comp : Path → Path → Path} {e : Path}
    (transitive : ∀ x y z : Path, cp x y → cp y z → cp x z)
    (clauses : ComposeAxioms (Form := Form) cp comp e) :
    FourFold cp comp :=
  fun p q r s =>
    transitive _ _ _
      (clauses.axComposeAssoc p q (comp r s))
      (clauses.axComposeAssoc (comp p q) r s)

/-- Bracketed products over atoms, with a formal unit. Nothing collapses here,
    so two bracketings are equal exactly when they are the same bracketing. -/
inductive Bracketing where
  | one : Bracketing
  | atom : Nat → Bracketing
  | pair : Bracketing → Bracketing → Bracketing

open Bracketing

/-- Equality, one rebracketing step, and the two unit laws --- the three
    clauses and nothing further. Deliberately not closed under composition of
    steps: that closure is exactly what `congruentPath` is never given. -/
def related (p q : Bracketing) : Prop :=
  p = q
    ∨ (∃ a b c : Bracketing, p = pair a (pair b c) ∧ q = pair (pair a b) c)
    ∨ p = pair q one ∨ p = pair one q

/-- All three composition clauses hold of it. -/
theorem related_satisfies_the_clauses :
    ComposeAxioms (Form := Form) related pair one where
  axComposeAssoc p q r := Or.inr (Or.inl ⟨p, q, r, rfl, rfl⟩)
  axComposeIdentity p := ⟨Or.inr (Or.inr (Or.inl rfl)), Or.inr (Or.inr (Or.inr rfl))⟩
  axComposeNonempty _ _ :=
    ⟨atom 1, fun h => by
      rcases h with h | ⟨_, _, _, _, h⟩ | h | h <;> exact Bracketing.noConfusion h⟩

/-- **And the four-fold law fails in it.** One rebracketing carries
    `a (b (c d))` as far as `(a b) (c d)` and no further; reaching `((a b) c) d`
    is a second step, and a second step is what `related` does not have. -/
theorem related_denies_the_four_fold : ¬ FourFold related pair := by
  intro four
  rcases four (atom 1) (atom 2) (atom 3) (atom 4) with
    h | ⟨a, b, c, left, right⟩ | h | h
  · injection h with h _
    exact Bracketing.noConfusion h
  · injection left with la lr
    subst la
    injection lr with lb lc
    subst lb
    subst lc
    injection right with _ h
    exact Bracketing.noConfusion h
  · injection h with h _
    exact Bracketing.noConfusion h
  · injection h with h _
    exact Bracketing.noConfusion h

/-- The relation stays reflexive in the model, so the failure above is not a
    reflexivity failure. Naming this separately keeps the reading honest:
    exactly one of the three equivalence properties is at issue. -/
theorem related_is_reflexive : ∀ p : Bracketing, related p p := fun _ => Or.inl rfl

/-- Addition on the naturals, related by equality except that one chain is
    broken. `2` reaches `1` and `1` reaches `0` and `2` does not reach `0`. -/
def stalled (x y : Nat) : Prop := x = y ∨ (x = 2 ∧ y = 1) ∨ (x = 1 ∧ y = 0)

/-- **Transitivity is sufficient and not necessary.** Saying only the first
    would overstate the pair above. Here all three clauses hold, the four-fold
    law holds, and the relation is not transitive --- the law arrives because
    `comp` is associative outright, so the clause is discharged by equality and
    equality chains whatever the rest of the relation does.

    Compare `congruentPath_is_not_an_equivalence`, which refutes transitivity
    of `congruentPath` from the same three clauses. That model is this case and
    not the other one: its `comp` is `· + · + 1`, both four-fold bracketings are
    the same numeral, and its relation holds there. Transitivity had already
    been shown underivable; what had not been shown is that the consequence the
    clause exists to deliver is underivable too, which needs a carrier where
    the bracketings are genuinely different things.

    So the two are independent of each other over the three clauses, and the
    clause is idle for the reason the sufficiency half gives rather than by an
    equivalence between them. -/
theorem four_fold_without_transitivity :
    ComposeAxioms (Form := Form) stalled (· + ·) 0 ∧ FourFold stalled (· + ·)
      ∧ ¬ (∀ x y z : Nat, stalled x y → stalled y z → stalled x z) :=
  ⟨{ axComposeAssoc := fun p q r => Or.inl (Nat.add_assoc p q r).symm
     axComposeIdentity := fun p => ⟨Or.inl (Nat.add_zero p), Or.inl (Nat.zero_add p)⟩
     axComposeNonempty := fun _ _ => ⟨3, by
       rintro (h | ⟨h, -⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)⟩ },
   fun p q r s =>
     Or.inl ((Nat.add_assoc (p + q) r s).trans (Nat.add_assoc p q (r + s))).symm,
   fun transitive => by
     have := transitive 2 1 0 (Or.inr (Or.inl ⟨rfl, rfl⟩)) (Or.inr (Or.inr ⟨rfl, rfl⟩))
     rcases this with h | ⟨-, h⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)⟩

/-- **The clause is idle because the step that would spend it is undeclared.**
    Associativity up to a relation yields the four-fold law when the relation is
    transitive and does not yield it otherwise. `congruentPath` is declared
    reflexive nowhere, symmetric nowhere and transitive nowhere, so
    `axComposeAssoc` is not unused by oversight: there is no proof in this
    development that could use it twice.

    `congruentPath_symmetry_independent` and `congruentPath_is_not_an_equivalence`
    already record that the missing properties cannot be recovered from the
    other clauses. This records what their absence costs, and it is the first
    statement here whose subject is a clause that nothing consumes. An
    independence result explains why a clause cannot be dropped; this explains
    why one is never picked up. -/
theorem transitivity_is_exactly_the_missing_step :
    (∀ (Path : Type) (cp : Path → Path → Prop) (comp : Path → Path → Path)
        (e : Path), (∀ x y z : Path, cp x y → cp y z → cp x z) →
        ComposeAxioms (Form := Form) cp comp e → FourFold cp comp)
      ∧ ¬ (∀ (Path : Type) (cp : Path → Path → Prop) (comp : Path → Path → Path)
            (e : Path), ComposeAxioms (Form := Form) cp comp e → FourFold cp comp) :=
  ⟨fun _ _ _ _ transitive clauses => fourFold_of_transitive transitive clauses,
   fun derive => related_denies_the_four_fold
     (derive Bracketing related pair one related_satisfies_the_clauses)⟩

end ComposeNeedsTransitivity

-- ----------------------------------------------------------------------------
-- The third idle clause, and the third reason
--
-- Of the three clauses nothing consumes, `axSeqIdentityL` is a duplicate ---
-- `L2Operations.lean` says so and says which clause it duplicates. The one
-- above is unchainable. This one is neither: it is strictly stronger than a
-- clause that *is* consumed, and the strength is all in one direction.
--
-- `closeFormClosureOpaque` reads `FormClosure x` as the conjunction of the
-- three triangle predicates. `axFormClosesLoop` reads two of them as
-- sufficient for it. Relative to the triangle, the first is the second plus
-- its converse, and the converse is an implication out of `FormClosure` ---
-- which appears as a hypothesis in no clause and no theorem anywhere. A clause
-- can be strictly stronger than what is used and still be idle, because what
-- it adds is stated in a direction nothing travels.
-- ----------------------------------------------------------------------------

namespace FormClosureIsOneDirection

/-- The triangle, its three ground inhabitants, and the weaker of the two
    clauses that speak `FormClosure`. Everything about form closure except the
    close clause itself. -/
structure ClosureAxioms {Carrier : Type}
    (HMSyntax Substance Semantics FormClosure : Carrier → Prop)
    (ground : Carrier) : Prop where
  axSyntaxRequiresSubstance : ∀ x, HMSyntax x → Substance x
  axSubstanceRequiresSemantics : ∀ x, Substance x → Semantics x
  axSemanticsRequiresSyntax : ∀ x, Semantics x → HMSyntax x
  axFormClosesLoop : ∀ x, HMSyntax x → Semantics x → FormClosure x
  axGroundSyntaxAx : HMSyntax ground
  axGroundSubstanceAx : Substance ground
  axGroundSemanticsAx : Semantics ground

/-- The clause nothing consumes. -/
def CloseFormClosure {Carrier : Type}
    (HMSyntax Substance Semantics FormClosure : Carrier → Prop) : Prop :=
  ∀ x, FormClosure x ↔ (HMSyntax x ∧ Substance x ∧ Semantics x)

/-- The one implication it adds. Every other part of it is already a clause. -/
def ClosureRequiresSyntax {Carrier : Type}
    (HMSyntax FormClosure : Carrier → Prop) : Prop :=
  ∀ x, FormClosure x → HMSyntax x

/-- **The only theorem about form closure needs only the weaker clause.**
    `groundIsFormClosed` is that theorem, and this is its proof with the
    carrier left open. Nothing here reaches the close. -/
theorem the_ground_closure_needs_only_the_loop {Carrier : Type}
    {HMSyntax Substance Semantics FormClosure : Carrier → Prop} {ground : Carrier}
    (clauses : ClosureAxioms HMSyntax Substance Semantics FormClosure ground) :
    FormClosure ground :=
  clauses.axFormClosesLoop ground clauses.axGroundSyntaxAx clauses.axGroundSemanticsAx

/-- **Relative to the rest, the close clause is exactly its converse.** The
    triangle makes the three predicates interderivable, so the conjunction the
    close asserts is any one of them; the direction into `FormClosure` is
    `axFormClosesLoop` already, and what is left over is the direction out.

    Stated as an equivalence rather than as two implications because the point
    is that nothing else of the close survives the other clauses. A clause that
    restates six things and adds a seventh is idle for whatever reason the
    seventh is idle. -/
theorem the_close_clause_is_exactly_its_converse {Carrier : Type}
    {HMSyntax Substance Semantics FormClosure : Carrier → Prop} {ground : Carrier}
    (clauses : ClosureAxioms HMSyntax Substance Semantics FormClosure ground) :
    CloseFormClosure HMSyntax Substance Semantics FormClosure
      ↔ ClosureRequiresSyntax HMSyntax FormClosure :=
  ⟨fun close x closed => ((close x).mp closed).1,
   fun converse x =>
     ⟨fun closed =>
        let hasSyntax := converse x closed
        let hasSubstance := clauses.axSyntaxRequiresSubstance x hasSyntax
        ⟨hasSyntax, hasSubstance,
          clauses.axSubstanceRequiresSemantics x hasSubstance⟩,
      fun ⟨hasSyntax, _, hasSemantics⟩ =>
        clauses.axFormClosesLoop x hasSyntax hasSemantics⟩⟩

/-- **And the converse is not free.** Everything about form closure holds of a
    carrier whose two Booleans are told apart by the triangle and not by
    closure, and the close clause fails at the one the triangle excludes. So
    the idle clause is not a restatement: it is strictly stronger than what the
    development uses, and strictly stronger in the direction out of
    `FormClosure`, which no clause and no theorem in the development travels.

    That is the third way a clause can go unspent, and it is the only one of
    the three where the clause carries content that nothing has anywhere to
    put. `axSeqIdentityL` is a duplicate and `axComposeAssoc` cannot be
    chained; this one could be used the moment any statement took form closure
    as a hypothesis, and none does. -/
theorem the_other_clauses_do_not_give_the_close :
    ClosureAxioms (· = true) (· = true) (· = true) (fun _ => True) true
      ∧ ¬ CloseFormClosure (· = true) (· = true) (· = true) (fun _ : Bool => True) :=
  ⟨{ axSyntaxRequiresSubstance := fun _ h => h
     axSubstanceRequiresSemantics := fun _ h => h
     axSemanticsRequiresSyntax := fun _ h => h
     axFormClosesLoop := fun _ _ _ => trivial
     axGroundSyntaxAx := rfl
     axGroundSubstanceAx := rfl
     axGroundSemanticsAx := rfl },
   fun close => Bool.noConfusion ((close false).mp trivial).1⟩

end FormClosureIsOneDirection

-- ----------------------------------------------------------------------------
-- The last five clauses, and the third way a join can fail
--
-- `prefixOperationsCompose_iff_conditions` reaches 34. The remaining five are
-- the transfinite projections of the single `ordinatics` instance, and by the
-- incidence table they look like the composition case: `deriver`,
-- `ordinalLimit`, `ordinalSucc`, `pathStart` and `pathEnd` appear in no
-- condition among the fourteen. They are not that case. The clauses also speak
-- `S`, `C`, `E`, `ground` and `f2f`, and one of them denies a relation at every
-- point of the ground chain --- which is a statement about how big the carrier
-- has to be, and the incidence table records symbols rather than carriers.
-- ----------------------------------------------------------------------------

/-- The five transfinite clauses, with every symbol they name left open:
    the carrier, the three relations, the path type and its two projections,
    and the three transfinite constants. -/
structure TransfiniteAxioms {Path : Type} (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) (pathStart pathEnd : Path → Form)
    (deriver ordinalLimit : Form) (ordinalSucc : Form → Form) : Prop where
  axDeriverAtLimit : deriver = ordinalLimit
  axLimitDerives : ∃ p : Path, S (pathStart p) ground ∧ C (pathEnd p) ordinalLimit
  axLimitIsLimit : ∀ y : Form,
    (∀ n : Nat, Derives f2f C (Nat.repeat f2f n ground) y) → Derives f2f C ordinalLimit y
  axLimitNotFinite : ∀ n : Nat, ¬ E (Nat.repeat f2f n ground) ordinalLimit
  axSuccExtends : ∀ x : Form, Derives f2f C x (ordinalSucc x) ∧ ¬ E (ordinalSucc x) x

/-- What the five say once `deriver` and the two path projections are read off
    their own clauses. `deriver` occurs in one clause and occurs there in an
    equation, so it is determined rather than constrained and disappears.
    `pathStart` and `pathEnd` occur in one clause and occur there existentially,
    so they are pinned at one point --- and pinning them *separates* the clause,
    because the single `p` was the only thing tying its two halves together. One
    clause therefore leaves two conditions behind rather than one. -/
structure TransfiniteConditions (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) (ordinalLimit : Form)
    (ordinalSucc : Form → Form) : Prop where
  someStartAtGround : ∃ a, S a ground
  someEndAtLimit : ∃ b, C b ordinalLimit
  limitAbsorbsTheChain : ∀ y : Form,
    (∀ n : Nat, Derives f2f C (Nat.repeat f2f n ground) y) → Derives f2f C ordinalLimit y
  limitNotSimulatedFinitely : ∀ n : Nat, ¬ E (Nat.repeat f2f n ground) ordinalLimit
  succEscapes : ∀ x : Form, Derives f2f C x (ordinalSucc x) ∧ ¬ E (ordinalSucc x) x

/-- **Five clauses, five conditions**, with the path index and `deriver` free.
    The count is unchanged and the content is not: one clause left and two
    conditions arrived, which is what pinning a shared binder does. -/
theorem transfinite_clauses_are_five_conditions
    (ground ordinalLimit : Form) (f2f ordinalSucc : Form → Form)
    (S C E : Form → Form → Prop) :
    (∃ (pathStart pathEnd : Unit → Form) (deriver : Form),
        TransfiniteAxioms ground f2f S C E pathStart pathEnd deriver ordinalLimit ordinalSucc)
      ↔ TransfiniteConditions ground f2f S C E ordinalLimit ordinalSucc := by
  constructor
  · rintro ⟨ps, pe, _, t⟩
    obtain ⟨p, hs, hc⟩ := t.axLimitDerives
    exact { someStartAtGround := ⟨ps p, hs⟩
            someEndAtLimit := ⟨pe p, hc⟩
            limitAbsorbsTheChain := t.axLimitIsLimit
            limitNotSimulatedFinitely := t.axLimitNotFinite
            succEscapes := t.axSuccExtends }
  · intro h
    obtain ⟨a, ha⟩ := h.someStartAtGround
    obtain ⟨b, hb⟩ := h.someEndAtLimit
    exact ⟨fun _ => a, fun _ => b, ordinalLimit,
      { axDeriverAtLimit := rfl
        axLimitDerives := ⟨(), ha, hb⟩
        axLimitIsLimit := h.limitAbsorbsTheChain
        axLimitNotFinite := h.limitNotSimulatedFinitely
        axSuccExtends := h.succEscapes }⟩

/-- **The five closing clauses, with every symbol they name left open.**
    These are the clauses declared at L0 §VIII.b and L2 §II, and they are the
    whole of what the closure added. `axDiffCongruent` denies the ground at
    `=~`; `axSimilarRefl` and `axSimilarSymm` make `~~` reflexive and
    symmetric; `axCongruentTrans` makes `=~` transitive; and
    `axCongruentPathSymm` makes path congruence symmetric.

    The first four speak only of `S`, `C` and `ground`; the fifth speaks of the
    path relation, which is why it is stated over a path type rather than over
    a carrier alone. -/
structure ClosingAxioms {Path : Type} (ground : Form) (f2f : Form → Form)
    (S C : Form → Form → Prop) (cp : Path → Path → Prop) : Prop where
  axDiffCongruent : ∀ x : Form, ¬ C (f2f x) ground
  axSimilarRefl : ∀ x : Form, S x x
  axSimilarSymm : ∀ x y : Form, S x y → S y x
  axCongruentTrans : ∀ x y z : Form, C x y → C y z → C x z
  axCongruentPathSymm : ∀ p q : Path, cp p q → cp q p

/-- **What the five say, with the relations named by their own clauses.**
    `axSimilarRefl` and `axSimilarSymm` are read off as reflexivity and
    symmetry of `S`; `axCongruentTrans` as transitivity of `C`; and
    `axDiffCongruent` as a denial that no image of anything is congruent to
    the ground. `axCongruentPathSymm` is read off the path relation itself.

    The count is five clauses and five conditions, and unlike the transfinite
    tier the two are not the same proposition written twice: each condition here
    is a *property of a relation*, and the clauses are *instances* of those
    properties at the specific arguments the clause names. `axSimilarRefl` is
    reflexivity of `S` at every point; the condition is reflexivity of `S`
    everywhere, which is what the clause says. -/
structure ClosingConditions {Path : Type} (ground : Form) (f2f : Form → Form)
    (S C : Form → Form → Prop) (cp : Path → Path → Prop) : Prop where
  formingIsNotCongruentToGround : ∀ x : Form, ¬ C (f2f x) ground
  similarIsReflexive : ∀ x : Form, S x x
  similarIsSymmetric : ∀ x y : Form, S x y → S y x
  congruentIsTransitive : ∀ x y z : Form, C x y → C y z → C x z
  congruentPathIsSymmetric : ∀ p q : Path, cp p q → cp q p

/-- **Five closing clauses, five conditions.** The correspondence is one to
    one, and it is exact rather than merely by count: each condition is the
    clause with its argument pattern read as a property of the relation.

    The three path-free conditions hold over any carrier and any two
    relations. The fourth clause and the fourth condition are the same
    sentence, and the fifth likewise, which is why this is an `iff` between
    two structures and not a characterisation that removes something. -/
theorem closingAxioms_iff_conditions {Path : Type} {ground : Form}
    {f2f : Form → Form} {S C : Form → Form → Prop}
    (cp : Path → Path → Prop) :
    ClosingAxioms ground f2f S C cp ↔
      ClosingConditions ground f2f S C cp :=
  ⟨fun h =>
    { formingIsNotCongruentToGround := h.axDiffCongruent
      similarIsReflexive := h.axSimilarRefl
      similarIsSymmetric := h.axSimilarSymm
      congruentIsTransitive := h.axCongruentTrans
      congruentPathIsSymmetric := h.axCongruentPathSymm },
   fun h =>
    { axDiffCongruent := h.formingIsNotCongruentToGround
      axSimilarRefl := h.similarIsReflexive
      axSimilarSymm := h.similarIsSymmetric
      axCongruentTrans := h.congruentIsTransitive
      axCongruentPathSymm := h.congruentPathIsSymmetric }⟩

/-- **39 of the 44 clauses, nineteen conditions.** Nothing in the pre-closure
    clause set is outside this statement: eight for the prefix, three for the
    operations, three for composition, five for the transfinite layer. The
    other five are the closing tier, and `all_forty_four_iff_twenty_four_conditions`
    adds them. -/
theorem all_thirty_nine_iff_nineteen_conditions (x ground ordinalLimit : Form)
    (f2f ordinalSucc : Form → Form) (S C E : Form → Form → Prop)
    {CPath : Type} (cp : CPath → CPath → Prop) (comp : CPath → CPath → CPath)
    (e : CPath) :
    (PrefixAxioms ground f2f S C E ∧ OperationAxioms S C ∧
        ComposeAxioms (Form := Form) cp comp e ∧
        ∃ (ps pe : Unit → Form) (deriver : Form),
          TransfiniteAxioms ground f2f S C E ps pe deriver ordinalLimit ordinalSucc)
      ↔ (Conditions ground f2f S C E ∧ OperationConditions S C ∧
          ComposeConditions cp comp e ∧
          TransfiniteConditions ground f2f S C E ordinalLimit ordinalSucc) :=
  ⟨fun h => ⟨conditions_of_prefixAxioms h.1,
      operationConditions_of_operationAxioms h.2.1,
      (composeAxioms_iff_conditions x cp comp e).mp h.2.2.1,
      (transfinite_clauses_are_five_conditions ground ordinalLimit f2f ordinalSucc
        S C E).mp h.2.2.2⟩,
   fun h => ⟨prefixAxioms_of_conditions h.1,
      operationAxioms_of_operationConditions h.2.1,
      (composeAxioms_iff_conditions x cp comp e).mpr h.2.2.1,
      (transfinite_clauses_are_five_conditions ground ordinalLimit f2f ordinalSucc
        S C E).mpr h.2.2.2⟩⟩

/-- **44 of the 44 clauses, twenty-four conditions.** The closing tier adds
    five clauses and five conditions to the statement above, and the join is
    the same shape as every other tier: the five conditions are the five
    clauses read as properties of their relations.

    The count moves from thirty-nine to forty-four and from nineteen to
    twenty-four, and nothing else in the reduction moves. The two counts that
    were argued down to seventeen and twenty-eight are unchanged, because the
    closing clauses are none of the definitional ones and none of them is
    implied by the layers beneath. -/
theorem all_forty_four_iff_twenty_four_conditions (x ground ordinalLimit : Form)
    (f2f ordinalSucc : Form → Form) (S C E : Form → Form → Prop)
    {CPath : Type} (cp : CPath → CPath → Prop) (comp : CPath → CPath → CPath)
    (e : CPath) :
    (PrefixAxioms ground f2f S C E ∧ OperationAxioms S C ∧
        ComposeAxioms (Form := Form) cp comp e ∧
        ∃ (ps pe : Unit → Form) (deriver : Form),
          TransfiniteAxioms ground f2f S C E ps pe deriver ordinalLimit ordinalSucc ∧
        ClosingAxioms (Path := CPath) ground f2f S C cp)
      ↔ (Conditions ground f2f S C E ∧ OperationConditions S C ∧
          ComposeConditions cp comp e ∧
          TransfiniteConditions ground f2f S C E ordinalLimit ordinalSucc ∧
          ClosingConditions ground f2f S C cp) :=
  ⟨fun h => by
    obtain ⟨ps, pe, deriver, t, k⟩ := h.2.2.2
    exact ⟨conditions_of_prefixAxioms h.1,
      operationConditions_of_operationAxioms h.2.1,
      (composeAxioms_iff_conditions x cp comp e).mp h.2.2.1,
      (transfinite_clauses_are_five_conditions ground ordinalLimit f2f ordinalSucc
        S C E).mp ⟨ps, pe, deriver, t⟩,
      (closingAxioms_iff_conditions cp).mp k⟩,
   fun h => by
    obtain ⟨ps, pe, deriver, t⟩ :=
      (transfinite_clauses_are_five_conditions ground ordinalLimit f2f ordinalSucc
        S C E).mpr h.2.2.2.1
    exact ⟨prefixAxioms_of_conditions h.1,
      operationAxioms_of_operationConditions h.2.1,
      (composeAxioms_iff_conditions x cp comp e).mpr h.2.2.1,
      ⟨ps, pe, deriver, t,
        (closingAxioms_iff_conditions cp).mpr h.2.2.2.2⟩⟩⟩

/-! #### The zero row, at the whole clause set

`the_unmentioned_are_unconstrained` is a theorem about the 24-clause prefix.
The reading taken off it is about all 39, and what stood at 39 was a scan of a
model's clause statements for three words. This is the same result where the
claim is made. -/

/-- **The 44 clauses again, carrying the three symbols none of them names.**
    Every field is copied verbatim out of the five structures that partition
    the clause set --- 24 from `PrefixAxiomsCarrying`, seven from
    `OperationAxioms`, three from `ComposeAxioms`, five from
    `TransfiniteAxioms`, five from `ClosingAxioms` --- so a clause that did
    mention `pl`, `ps` or `pt` would leave `assumption` a goal with no
    hypothesis to match, exactly as it would at 24.

    Assembling them costs one collision. `closeDischargeOpaque` binds `c` and
    `e`, and `ComposeAxioms` calls its identity path `e`, so inside that one
    field the path parameter is shadowed by a `Form`. Shadowing is quiet, which
    is the problem with it: nothing in this declaration says the field still
    means what it meant. `carrying_iff_the_whole_clause_set` is what says so,
    by taking the structure back apart into the four it was built from, where
    the two `e`s are in different scopes and cannot be confused. -/
structure FullAxiomsCarrying {Path : Type} (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) (cp : Path → Path → Prop)
    (comp : Path → Path → Path) (e : Path)
    (pathStart pathEnd : Path → Form) (deriver ordinalLimit : Form)
    (ordinalSucc : Form → Form)
    (pl : Path → Form) (ps : Form → Form → Path) (pt : Path → Form) : Prop where
  axDiff : ∀ x, structDistinct E (f2f x) ground
  axSim : ∀ x, structContinues ground S (f2f x) ground
  axBox : ∀ x, structOrbits S (f2f (f2f x)) x
  axGroundSelf : structContinues ground S ground ground
  closeStructContinues : ∀ x, structContinues ground S x ground ↔ S x ground
  closeStructDistinct : ∀ x y, structDistinct E x y ↔ ¬ E x y
  closeStructOrbits : ∀ x, structOrbits S (f2f (f2f x)) x ↔ S (f2f (f2f x)) x
  axSyntaxRequiresSubstance : ∀ x, HMSyntax ground f2f S x → Substance C x
  axSubstanceRequiresSemantics : ∀ x, Substance C x → Semantics E x
  axSemanticsRequiresSyntax : ∀ x, Semantics E x → HMSyntax ground f2f S x
  axFormClosesLoop : ∀ x, HMSyntax ground f2f S x → Semantics E x →
    FormClosure ground f2f S C E x
  axGroundSyntaxAx : HMSyntax ground f2f S ground
  axGroundSubstanceAx : Substance C ground
  axGroundSemanticsAx : Semantics E ground
  filtrationSimCong : ∀ x y, E x y → C x y
  filtrationCongSim : ∀ x y, C x y → S x y
  closeSyntaxOpaque : ∀ x, HMSyntax ground f2f S x ↔ ∃ n : Nat, S (Nat.repeat f2f n ground) x
  closeSubstanceOpaque : ∀ x, Substance C x ↔ C x x
  closeSemanticsOpaque : ∀ x, Semantics E x ↔ E x x
  closeDerivesOpaque : ∀ x y, Derives f2f C x y ↔ ∃ n : Nat, C (Nat.repeat f2f n x) y
  closeDischargeOpaque : ∀ c e, Discharge f2f C c e ↔ Derives f2f C e c
  closeDefinitionOpaque : ∀ n x, Definition f2f C n x ↔ Derives f2f C n x
  closeFormClosureOpaque : ∀ x, FormClosure ground f2f S C E x ↔ HMSyntax ground f2f S x ∧ Substance C x ∧ Semantics E x
  traceLevels : ∀ x, S (f2f x) x ∧ (C (f2f x) x → S (f2f x) x) ∧
    (E (f2f x) x → C (f2f x) x)
  axSeq : ∀ a b, ∃ c, S c a ∧ S c b
  axSeqAsymm : ∀ a b, ¬ C a b →
    ∃ c d, S c a ∧ S c b ∧ S d b ∧ S d a ∧ ¬ C c d
  axSeqIdentityR : ∀ a, ∃ c, S c a ∧ C c a
  axSeqIdentityL : ∀ a, ∃ c, S c a ∧ C c a
  axCoop : ∀ a b, ∃ c, S c a ∧ S c b
  axCoopComm : ∀ a b, ∃ ca cab, S ca a ∧ S ca b ∧ S cab b ∧ S cab a ∧ C ca cab
  axCoopIdentity : ∀ a, ∃ c, S c a ∧ C c a
  axComposeAssoc : ∀ p q r : Path, cp (comp p (comp q r)) (comp (comp p q) r)
  axComposeIdentity : ∀ p : Path, cp (comp p e) p ∧ cp (comp e p) p
  axComposeNonempty : Form → Form → ∃ p : Path, ¬ cp p e
  axDeriverAtLimit : deriver = ordinalLimit
  axLimitDerives : ∃ p : Path, S (pathStart p) ground ∧ C (pathEnd p) ordinalLimit
  axLimitIsLimit : ∀ y : Form,
    (∀ n : Nat, Derives f2f C (Nat.repeat f2f n ground) y) → Derives f2f C ordinalLimit y
  axLimitNotFinite : ∀ n : Nat, ¬ E (Nat.repeat f2f n ground) ordinalLimit
  axSuccExtends : ∀ x : Form, Derives f2f C x (ordinalSucc x) ∧ ¬ E (ordinalSucc x) x
  axDiffCongruent : ∀ x : Form, ¬ C (f2f x) ground
  axSimilarRefl : ∀ x : Form, S x x
  axSimilarSymm : ∀ x y : Form, S x y → S y x
  axCongruentTrans : ∀ x y z : Form, C x y → C y z → C x z
  axCongruentPathSymm : ∀ p q : Path, cp p q → cp q p

/-- **The assembly changed no clause.** Writing 44 clauses into one scope is
    the step where a clause could quietly acquire a different meaning, and this
    is the round trip that denies it: the structure holds exactly when the five
    it was copied from all hold. Every field is discharged by `assumption` in
    both directions, so a field that had drifted --- by a shadowed binder, a
    renamed parameter, or a copy that was not one --- would leave a goal no
    hypothesis matches. -/
theorem carrying_iff_the_whole_clause_set {Path : Type} {ground : Form}
    {f2f : Form → Form} {S C E : Form → Form → Prop} {cp : Path → Path → Prop}
    {comp : Path → Path → Path} {e : Path} {pathStart pathEnd : Path → Form}
    {deriver ordinalLimit : Form} {ordinalSucc : Form → Form}
    (pl : Path → Form) (ps : Form → Form → Path) (pt : Path → Form) :
    FullAxiomsCarrying ground f2f S C E cp comp e pathStart pathEnd deriver
        ordinalLimit ordinalSucc pl ps pt
      ↔ (PrefixAxioms ground f2f S C E ∧ OperationAxioms S C
          ∧ ComposeAxioms (Form := Form) cp comp e
          ∧ TransfiniteAxioms ground f2f S C E pathStart pathEnd deriver
              ordinalLimit ordinalSucc
          ∧ ClosingAxioms (Path := Path) ground f2f S C cp) := by
  constructor
  · intro h
    cases h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> constructor <;> assumption
  · rintro ⟨p, o, c, t, k⟩
    cases p
    cases o
    cases c
    cases t
    cases k
    constructor <;> assumption

/-- **A symbol no clause mentions is free, at every clause there is.** Any
    reading of all three at once satisfies the 44 clauses as soon as one does.
    The proof is the two tactics it is at 24, and they are doing more work
    here: `constructor` now produces 44 goals rather than 24, and the twenty
    it did not have to produce before are exactly the ones the earlier theorem
    could say nothing about. -/
theorem carried_symbols_are_free_at_forty_four {Path : Type} {ground : Form}
    {f2f : Form → Form} {S C E : Form → Form → Prop} {cp : Path → Path → Prop}
    {comp : Path → Path → Path} {e : Path} {pathStart pathEnd : Path → Form}
    {deriver ordinalLimit : Form} {ordinalSucc : Form → Form}
    {pl : Path → Form} {ps : Form → Form → Path} {pt : Path → Form}
    (h : FullAxiomsCarrying ground f2f S C E cp comp e pathStart pathEnd
      deriver ordinalLimit ordinalSucc pl ps pt)
    (pl' : Path → Form) (ps' : Form → Form → Path) (pt' : Path → Form) :
    FullAxiomsCarrying ground f2f S C E cp comp e pathStart pathEnd deriver
      ordinalLimit ordinalSucc pl' ps' pt' := by
  cases h
  constructor <;> assumption

/-- **The zero row, mechanized where the claim is made.** The scan says no
    clause of the 44 contains the three names. This says what that is worth:
    everything the 44 assert is compatible with every reading whatever of the
    three. The scan cannot say it --- a word it failed to find and a word that
    is not there look the same from outside --- and the 24-clause theorem could
    not either, because twenty of the clauses were not in its statement. -/
theorem the_unmentioned_are_unconstrained_at_forty_four {Path : Type}
    {ground : Form} {f2f : Form → Form} {S C E : Form → Form → Prop}
    {cp : Path → Path → Prop} {comp : Path → Path → Path} {e : Path}
    {pathStart pathEnd : Path → Form} {deriver ordinalLimit : Form}
    {ordinalSucc : Form → Form}
    {pl : Path → Form} {ps : Form → Form → Path} {pt : Path → Form} :
    PrefixAxioms ground f2f S C E → OperationAxioms S C →
      ComposeAxioms (Form := Form) cp comp e →
      TransfiniteAxioms ground f2f S C E pathStart pathEnd deriver ordinalLimit
        ordinalSucc →
      ClosingAxioms (Path := Path) ground f2f S C cp →
      ∀ (pl' : Path → Form) (ps' : Form → Form → Path) (pt' : Path → Form),
        FullAxiomsCarrying ground f2f S C E cp comp e pathStart pathEnd deriver
          ordinalLimit ordinalSucc pl' ps' pt' :=
  fun p o c t k => carried_symbols_are_free_at_forty_four
    ((carrying_iff_the_whole_clause_set pl ps pt).mpr ⟨p, o, c, t, k⟩)

/-- Every point of the ground chain is reached by it. One step of
    `imageSimilar` at the point itself is the whole proof, and it is what makes
    the next theorem bite. -/
theorem chain_points_are_reached {ground : Form} {f2f : Form → Form}
    {S C E : Form → Form → Prop} (h : Conditions ground f2f S C E) (k : Nat) :
    Reach ground f2f S (Nat.repeat f2f k ground) :=
  ⟨k + 1, h.imageSimilar (Nat.repeat f2f k ground)⟩

/-! `ground_is_not_an_image` used to be proved here, because this is the
section that first needed it. It is a statement about the prefix eight and about
no clause of this layer, so it now lives with them, under `What the eight
forbid`. -/

/-- **`axLimitNotFinite` puts the limit off the chain.** The clause denies
    simulation from every finite position; `simulationDiagonalIsReach` grants it
    at every reached point; and every chain point is reached. So the limit is
    not any `f2f^k ground`.

    This used to be called the first clause in the whole set that says anything
    about how large the carrier must be. It is not: `two_is_the_smallest_carrier`
    shows the prefix eight already force a second Form and are satisfiable with
    exactly two. What this clause adds is a point off the chain, which is a
    different demand from a second point, not a larger one in the same
    direction. -/
theorem the_limit_is_off_the_chain {ground ordinalLimit : Form} {f2f : Form → Form}
    {S C E : Form → Form → Prop} (h : Conditions ground f2f S C E)
    (notFinite : ∀ n : Nat, ¬ E (Nat.repeat f2f n ground) ordinalLimit) (k : Nat) :
    Nat.repeat f2f k ground ≠ ordinalLimit := by
  intro hk
  apply notFinite k
  rw [← hk]
  exact (h.simulationDiagonalIsReach _).mpr (chain_points_are_reached h k)

/-- A carrier the chain exhausts carries no transfinite layer at all. -/
theorem spanned_carriers_admit_no_limit
    {ground ordinalLimit deriver : Form} {f2f ordinalSucc : Form → Form}
    {S C E : Form → Form → Prop} {Path : Type} {pathStart pathEnd : Path → Form}
    (h : Conditions ground f2f S C E)
    (spanned : ∀ y : Form, ∃ n : Nat, y = Nat.repeat f2f n ground)
    (t : TransfiniteAxioms ground f2f S C E pathStart pathEnd deriver ordinalLimit
      ordinalSucc) : False :=
  let ⟨k, hk⟩ := spanned ordinalLimit
  the_limit_is_off_the_chain h t.axLimitNotFinite k hk.symm

/-! #### How small a carrier with a limit can be

`two_is_the_smallest_carrier` answered that for the prefix eight. The limit
moves the answer by one, and the interesting part is that it does not move it to
infinity --- which is what the only model of all nineteen in this file, on
`Option Nat`, invites a reader to assume, and what "transfinite" invites a reader
to assume before that. -/

/-- Two Booleans are not three things. -/
theorem no_three_distinct_booleans : ∀ a b c : Bool, a ≠ b → a ≠ c → b ≠ c →
    False := by decide

/-- **No model of the nineteen has two Forms.** Ground, its image and the limit
    are three distinct Forms. `ground_is_not_an_image` separates the first two;
    `the_limit_is_off_the_chain` separates the limit from each of them, at the
    chain's zeroth and first positions. Neither the operations nor the
    composition is consulted, so it is the prefix eight and one transfinite
    condition that spend the third Form. -/
theorem no_limit_on_two_points {ground ordinalLimit : Bool}
    {f2f ordinalSucc : Bool → Bool} {S C E : Bool → Bool → Prop}
    (h : Conditions ground f2f S C E)
    (t : TransfiniteConditions ground f2f S C E ordinalLimit ordinalSucc) :
    False :=
  no_three_distinct_booleans _ _ _ (Ne.symm (ground_is_not_an_image h ground))
    (the_limit_is_off_the_chain h t.limitNotSimulatedFinitely 0)
    (the_limit_is_off_the_chain h t.limitNotSimulatedFinitely 1)

/-! Which of the layers is spending those Forms is a separate question from how
many there are, and the answer is not the one the counts suggest. -/

/-- **The operation conditions hold on one Form.** Every witness they ask for may
    be the ground, and the one negative field is vacuous when congruence is
    total. So the seven operation clauses demand no Form whatever. -/
theorem operation_conditions_hold_on_one_point :
    OperationConditions (fun _ _ : Unit => True) (fun _ _ : Unit => True) where
  pairedWitnesses _ _ := ⟨(), (), trivial, trivial, trivial, trivial, trivial⟩
  identityWitness _ := ⟨(), trivial, trivial⟩
  apartWitnesses _ _ h := absurd trivial h

/-- **And so do the transfinite conditions, on their own.** Ground and limit are
    the one Form, forming and the successor are the identity on it, `~~` and `=~`
    are total and `≡` is empty. `limitNotSimulatedFinitely` is satisfied by an
    empty `≡` rather than by a large carrier, and `succEscapes` by the same.

    The layer named for the transfinite is the one that asks least of the
    carrier: by itself it does not even ask for a second Form. -/
theorem transfinite_conditions_hold_on_one_point :
    TransfiniteConditions () (fun _ => ()) (fun _ _ => True) (fun _ _ => True)
      (fun _ _ => False) () (fun _ => ()) where
  someStartAtGround := ⟨(), trivial⟩
  someEndAtLimit := ⟨(), trivial⟩
  limitAbsorbsTheChain _ _ := ⟨0, trivial⟩
  limitNotSimulatedFinitely _ := fun empty => empty
  succEscapes _ := ⟨⟨0, trivial⟩, fun empty => empty⟩

/-- **Only the prefix asks for a second Form.** Of the three layers that speak of
    Forms at all, one has no one-point model and two do. Every demand the clause
    set makes on the size of the carrier passes through the eight. -/
theorem only_the_prefix_demands_a_second_form :
    (∀ (f2f : Unit → Unit) (S C E : Unit → Unit → Prop),
        ¬ Conditions () f2f S C E) ∧
      OperationConditions (fun _ _ : Unit => True) (fun _ _ : Unit => True) ∧
      TransfiniteConditions () (fun _ => ()) (fun _ _ => True) (fun _ _ => True)
        (fun _ _ => False) () (fun _ => ()) :=
  ⟨no_model_on_one_point, operation_conditions_hold_on_one_point,
   transfinite_conditions_hold_on_one_point⟩

/-- **The third Form is demanded by neither layer and by both together.** The
    eight have a two-Form model and the transfinite conditions have a one-Form
    model, so neither asks for a third; their conjunction has no two-Form model
    at all.

    `nineteen_is_not_fourteen_plus_five` found a join that fails because one side
    fixes relations the other must then meet. This is a join that fails on the
    carrier instead: each side is satisfiable at a size, and the size at which
    both are satisfiable is larger than either. An incidence table over symbols
    cannot see this any more than it could see that one, and for the same
    reason --- `axLimitNotFinite` is a demand about a carrier. -/
theorem the_third_form_is_a_joint_demand :
    Conditions false twoPointStep twoPointSimilar (fun x y => x = y)
        (fun x y => x = y) ∧
      TransfiniteConditions () (fun _ => ()) (fun _ _ => True) (fun _ _ => True)
        (fun _ _ => False) () (fun _ => ()) ∧
      (∀ (ground ordinalLimit : Bool) (f2f ordinalSucc : Bool → Bool)
          (S C E : Bool → Bool → Prop),
          ¬ (Conditions ground f2f S C E ∧
              TransfiniteConditions ground f2f S C E ordinalLimit ordinalSucc)) :=
  ⟨two_points_are_enough, transfinite_conditions_hold_on_one_point,
   fun _ _ _ _ _ _ _ both => no_limit_on_two_points both.1 both.2⟩

/-! The paths are a second carrier, and the composition conditions are the only
ones that speak of it. It has a size too, and the same two questions settle it.
-/

/-- **No model of the composition conditions has one path.** `unitalUpToCp`
    relates `comp p e` to `p`, both of which are the one path, so `cp` holds
    between the unit and itself --- and `someNonUnit` demands a path where it
    does not. This is the composition layer's only demand on anything: the other
    two conditions are equations that one path satisfies. -/
theorem no_compose_on_one_path (cp : Unit → Unit → Prop)
    (comp : Unit → Unit → Unit) (e : Unit) (h : ComposeConditions cp comp e) :
    False :=
  let ⟨p, notUnit⟩ := h.someNonUnit
  notUnit (h.unitalUpToCp p).1

/-- **And two paths are enough**, with disjunction for composition and `false`
    for the unit, which is the smallest monoid with a non-unit there is.
    `compose_conditions_are_always_available` already said the layer excludes
    nothing; this says what the layer costs, which is one path more than
    nothing. -/
theorem two_paths_are_enough : ComposeConditions (Path := Bool) Eq or false := by
  refine ⟨?_, ?_, ⟨true, by decide⟩⟩ <;> decide

/-- **So the smallest path carrier has two paths**, against three Forms for the
    rest of the clause set. -/
theorem two_is_the_smallest_path_carrier :
    (∀ (cp : Unit → Unit → Prop) (comp : Unit → Unit → Unit) (e : Unit),
        ¬ ComposeConditions cp comp e) ∧
      ComposeConditions (Path := Bool) Eq or false :=
  ⟨fun cp comp e h => no_compose_on_one_path cp comp e h, two_paths_are_enough⟩

namespace ThreePointLimit

/-- Ground, one image and the limit, and nothing else. Forming is constant at
    the image, so the chain is `0, 1, 1, ...` and never meets the limit; the
    successor is the three-cycle, the cheapest map with no fixed point;
    similarity and congruence are total and simulation is equality, as in
    `LimitAdjoined`. -/
def step (_ : Fin 3) : Fin 3 := 1
def succ (x : Fin 3) : Fin 3 := x + 1
def S (_ _ : Fin 3) : Prop := True
def C (_ _ : Fin 3) : Prop := True

theorem succ_moves : ∀ x : Fin 3, ¬ (succ x = x) := by decide

theorem chain_avoids_limit (n : Nat) : ¬ (Nat.repeat step n (0 : Fin 3) = 2) := by
  cases n with
  | zero => decide
  | succ _ => exact fun h => absurd h (by decide : (1 : Fin 3) ≠ 2)

theorem conditions_hold : Conditions (0 : Fin 3) step S C Eq where
  simIntoCong _ _ _ := trivial
  congIntoSim _ _ _ := trivial
  imageSimilar _ := trivial
  imageSimilarToGround _ := trivial
  doubleImageSimilar _ := trivial
  imageNotSimulatingGround _ := fun h => absurd h (by decide : (1 : Fin 3) ≠ 0)
  congruentDiagonalIsReach _ := ⟨fun _ => ⟨0, trivial⟩, fun _ => trivial⟩
  simulationDiagonalIsReach _ := ⟨fun _ => ⟨0, trivial⟩, fun _ => rfl⟩

theorem operation_conditions_hold : OperationConditions S C where
  pairedWitnesses _ _ := ⟨0, 0, trivial, trivial, trivial, trivial, trivial⟩
  identityWitness _ := ⟨0, trivial, trivial⟩
  apartWitnesses _ _ h := absurd trivial h

theorem transfinite_conditions_hold :
    TransfiniteConditions (0 : Fin 3) step S C Eq 2 succ where
  someStartAtGround := ⟨0, trivial⟩
  someEndAtLimit := ⟨0, trivial⟩
  limitAbsorbsTheChain _ _ := ⟨0, trivial⟩
  limitNotSimulatedFinitely n := chain_avoids_limit n
  succEscapes x := ⟨⟨0, trivial⟩, succ_moves x⟩

/-- All nineteen conditions on three Forms and two paths. -/
theorem all_nineteen_conditions_hold :
    Conditions (0 : Fin 3) step S C Eq ∧ OperationConditions S C ∧
      ComposeConditions (Path := Bool) Eq or false ∧
      TransfiniteConditions (0 : Fin 3) step S C Eq 2 succ :=
  ⟨conditions_hold, operation_conditions_hold,
   two_paths_are_enough, transfinite_conditions_hold⟩

end ThreePointLimit

/-- **So the smallest carrier under all nineteen conditions has three Forms.**
    Two is refuted and three is exhibited, so the transfinite layer costs
    exactly one Form over `two_is_the_smallest_carrier` and no more.

    The layer is named for the transfinite and its only model here is
    `Option Nat`; neither fact is a demand of the clauses. What `axLimitNotFinite`
    asks is that no *position* of the chain simulate the limit, and a chain that
    stops moving has one position after its first step. The clause is read as
    though it forced the chain to be infinite --- `spanned_carriers_admit_no_limit`
    is the nearest thing to that, and it says something weaker: a carrier the
    chain exhausts admits no limit, which a constant forming satisfies by not
    exhausting three points.

    The paths are a second carrier and are counted separately, just above: two
    of them, which is also exactly the minimum. -/
theorem three_is_the_smallest_carrier_with_a_limit :
    (∀ (ground ordinalLimit : Bool) (f2f ordinalSucc : Bool → Bool)
        (S C E : Bool → Bool → Prop),
        ¬ (Conditions ground f2f S C E ∧
            TransfiniteConditions ground f2f S C E ordinalLimit ordinalSucc)) ∧
      (Conditions (0 : Fin 3) ThreePointLimit.step ThreePointLimit.S
            ThreePointLimit.C Eq ∧
          OperationConditions ThreePointLimit.S ThreePointLimit.C ∧
          ComposeConditions (Path := Bool) Eq or false ∧
          TransfiniteConditions (0 : Fin 3) ThreePointLimit.step ThreePointLimit.S
            ThreePointLimit.C Eq 2 ThreePointLimit.succ) :=
  ⟨fun _ _ _ _ _ _ _ both => no_limit_on_two_points both.1 both.2,
   ThreePointLimit.all_nineteen_conditions_hold⟩

namespace BareChain

/-- The ground chain and nothing else: similarity and congruence total,
    simulation the diagonal. -/
def S (_ _ : Nat) : Prop := True
def C (_ _ : Nat) : Prop := True

theorem repeat_succ (n : Nat) : Nat.repeat Nat.succ n 0 = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [Nat.repeat, ih]

theorem spanned : ∀ y : Nat, ∃ n : Nat, y = Nat.repeat Nat.succ n 0 :=
  fun y => ⟨y, (repeat_succ y).symm⟩

theorem conditions_hold : Conditions (0 : Nat) Nat.succ S C Eq where
  simIntoCong _ _ _ := trivial
  congIntoSim _ _ _ := trivial
  imageSimilar _ := trivial
  imageSimilarToGround _ := trivial
  doubleImageSimilar _ := trivial
  imageNotSimulatingGround x := Nat.succ_ne_zero x
  congruentDiagonalIsReach _ := ⟨fun _ => ⟨0, trivial⟩, fun _ => trivial⟩
  simulationDiagonalIsReach _ := ⟨fun _ => ⟨0, trivial⟩, fun _ => rfl⟩

theorem operation_conditions_hold : OperationConditions S C where
  pairedWitnesses _ _ := ⟨0, 0, trivial, trivial, trivial, trivial, trivial⟩
  identityWitness _ := ⟨0, trivial, trivial⟩
  apartWitnesses _ _ h := absurd trivial h

end BareChain

namespace LimitAdjoined

/-- The chain with the limit adjoined. Similarity and congruence are total,
    simulation is the diagonal, and the successor moves the adjoined point back
    onto the chain --- it has to move it somewhere, because `axSuccExtends`
    denies simulation between a point and its successor and simulation here is
    equality. `extStep` will not serve: it fixes the adjoined point. -/
def S (_ _ : Extended) : Prop := True
def C (_ _ : Extended) : Prop := True

def succ : Extended → Extended
  | some n => some (n + 1)
  | none => some 0

theorem step_never_ground (x : Extended) : ¬ (extStep x = extGround) := by
  cases x <;> simp [extStep, extGround]

theorem succ_moves (x : Extended) : ¬ (succ x = x) := by
  cases x <;> simp [succ]

theorem conditions_hold : Conditions extGround extStep S C Eq where
  simIntoCong _ _ _ := trivial
  congIntoSim _ _ _ := trivial
  imageSimilar _ := trivial
  imageSimilarToGround _ := trivial
  doubleImageSimilar _ := trivial
  imageNotSimulatingGround x := step_never_ground x
  congruentDiagonalIsReach _ := ⟨fun _ => ⟨0, trivial⟩, fun _ => trivial⟩
  simulationDiagonalIsReach _ := ⟨fun _ => ⟨0, trivial⟩, fun _ => rfl⟩

theorem operation_conditions_hold : OperationConditions S C where
  pairedWitnesses _ _ := ⟨extGround, extGround, trivial, trivial, trivial, trivial, trivial⟩
  identityWitness _ := ⟨extGround, trivial, trivial⟩
  apartWitnesses _ _ h := absurd trivial h

theorem transfinite_conditions_hold :
    TransfiniteConditions extGround extStep S C Eq none succ where
  someStartAtGround := ⟨extGround, trivial⟩
  someEndAtLimit := ⟨extGround, trivial⟩
  limitAbsorbsTheChain _ _ := ⟨0, trivial⟩
  limitNotSimulatedFinitely n := by
    rw [ext_repeat]
    exact fun h => Option.noConfusion h
  succEscapes x := ⟨⟨0, trivial⟩, succ_moves x⟩

/-- All nineteen conditions at once, on one carrier. -/
theorem all_nineteen_conditions_hold :
    Conditions extGround extStep S C Eq ∧ OperationConditions S C ∧
      ComposeConditions (Path := Nat) Eq (· + ·) 0 ∧
      TransfiniteConditions extGround extStep S C Eq none succ :=
  ⟨conditions_hold, operation_conditions_hold,
   compose_conditions_are_always_available, transfinite_conditions_hold⟩

end LimitAdjoined

/-- **Nineteen is not fourteen plus five, and the reason is new.**

    The left conjunct is a model of all fourteen conditions --- prefix,
    operations, composition --- whose carrier is exactly the ground chain. The
    right conjunct says no transfinite layer sits on top of it, for any choice
    of limit, successor, deriver and path projections.

    `operations_exclude_the_unreached_point` obstructs because the operation
    clauses speak the prefix's own `S` and `C`.
    `lists_join_freely_exactly_on_disjoint_symbols` does not obstruct because
    the composition clauses speak three symbols no condition mentions. This
    obstruction is neither: the five transfinite symbols appear in no condition
    either, and the join still fails, because `axLimitNotFinite` is a demand on
    the *carrier* and an incidence table over symbols cannot see one. -/
theorem nineteen_is_not_fourteen_plus_five :
    (Conditions extGround extStep
        LimitAdjoined.S LimitAdjoined.C Eq ∧
      OperationConditions LimitAdjoined.S LimitAdjoined.C ∧
      ComposeConditions (Path := Nat) Eq (· + ·) 0 ∧
      TransfiniteConditions extGround extStep
        LimitAdjoined.S LimitAdjoined.C Eq none LimitAdjoined.succ) ∧
    (Conditions (0 : Nat) Nat.succ BareChain.S BareChain.C Eq ∧
        OperationConditions BareChain.S BareChain.C ∧
        ComposeConditions (Path := Nat) Eq (· + ·) 0) ∧
      ∀ (ordinalLimit deriver : Nat) (ordinalSucc : Nat → Nat)
        (pathStart pathEnd : Unit → Nat),
        ¬ TransfiniteAxioms (0 : Nat) Nat.succ BareChain.S BareChain.C Eq
            pathStart pathEnd deriver ordinalLimit ordinalSucc :=
  ⟨LimitAdjoined.all_nineteen_conditions_hold,
   ⟨BareChain.conditions_hold, BareChain.operation_conditions_hold,
     compose_conditions_are_always_available⟩,
   fun _ _ _ _ _ t =>
     spanned_carriers_admit_no_limit BareChain.conditions_hold BareChain.spanned t⟩

/-- **Ten of the 39 clauses hold of nothing.**

Each of these is a clause of `PrefixAxioms`, and each is `Iff.rfl`: no carrier,
no relation and no hypothesis appears in the proof, because `FreeFiltration`
*defines* every auxiliary predicate to be the reading its closing clause
asserts. The layers do not. There `HMSyntax`, `Substance`, `Semantics`,
`FormClosure`, `Derives`, `Discharge`, `Definition` and the three `struct`
predicates are opaque parameters, and these ten clauses are exactly what pins
them.

So the ten are not free in hypermath. They are discharged by the free reading,
which is a choice made here and paid for here: anything a model of the layers
could do by reading an auxiliary predicate some other way is outside every
result stated over `PrefixAxioms`. -/
theorem the_closes_are_definitional (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) :
    (∀ x, structContinues ground S x ground ↔ S x ground) ∧
    (∀ x y, structDistinct E x y ↔ ¬ E x y) ∧
    (∀ x, structOrbits S (f2f (f2f x)) x ↔ S (f2f (f2f x)) x) ∧
    (∀ x, HMSyntax ground f2f S x ↔ ∃ n : Nat, S (Nat.repeat f2f n ground) x) ∧
    (∀ x, Substance C x ↔ C x x) ∧
    (∀ x, Semantics E x ↔ E x x) ∧
    (∀ x y, Derives f2f C x y ↔ ∃ n : Nat, C (Nat.repeat f2f n x) y) ∧
    (∀ c e, Discharge f2f C c e ↔ Derives f2f C e c) ∧
    (∀ n x, Definition f2f C n x ↔ Derives f2f C n x) ∧
    (∀ x, FormClosure ground f2f S C E x ↔
      HMSyntax ground f2f S x ∧ Substance C x ∧ Semantics E x) :=
  ⟨fun _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl,
   fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl,
   fun _ _ => Iff.rfl, fun _ => Iff.rfl⟩

/-- The 14 clauses of `PrefixAxioms` that are left once the ten closes are
removed. Stated in the relations directly, since that is all the auxiliary
predicates were.

"Contentful" here means only *not discharged by the reading*. It does not mean
irredundant, and these are not: `axGroundSelf` is `filtrationCongSim` applied to
`axGroundSubstanceAx`, `axGroundSyntaxAx` is `axSim` at one step, and
`axFormClosesLoop` is `filtrationSimCong` rearranged --- all three proved in
`three_of_the_fourteen_are_derivable` rather than asserted here. The reduction
to eight `Conditions` measures the list as a whole;
`eleven_prefix_clauses_carry_the_content` measures it clause by clause and
removes the three, leaving `NeededPrefixAxioms`. -/
structure ContentfulPrefixAxioms (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) : Prop where
  axDiff : ∀ x, ¬ E (f2f x) ground
  axSim : ∀ x, S (f2f x) ground
  axBox : ∀ x, S (f2f (f2f x)) x
  axGroundSelf : S ground ground
  axSyntaxRequiresSubstance : ∀ x, Reach ground f2f S x → C x x
  axSubstanceRequiresSemantics : ∀ x, C x x → E x x
  axSemanticsRequiresSyntax : ∀ x, E x x → Reach ground f2f S x
  axFormClosesLoop : ∀ x, Reach ground f2f S x → E x x →
    Reach ground f2f S x ∧ C x x ∧ E x x
  axGroundSyntaxAx : Reach ground f2f S ground
  axGroundSubstanceAx : C ground ground
  axGroundSemanticsAx : E ground ground
  filtrationSimCong : ∀ x y, E x y → C x y
  filtrationCongSim : ∀ x y, C x y → S x y
  traceLevels : ∀ x, S (f2f x) x ∧ (C (f2f x) x → S (f2f x) x) ∧
    (E (f2f x) x → C (f2f x) x)

/-- The docstring above, proved. Each of the three is derived from clauses
named individually, so nothing here depends on the rest of the list. -/
theorem three_of_the_fourteen_are_derivable {ground : Form} {f2f : Form → Form}
    {S C E : Form → Form → Prop}
    (congSim : ∀ x y, C x y → S x y) (simCong : ∀ x y, E x y → C x y)
    (groundSubstance : C ground ground) (imageToGround : ∀ x, S (f2f x) ground) :
    S ground ground ∧ Reach ground f2f S ground ∧
      (∀ x, Reach ground f2f S x → E x x →
        Reach ground f2f S x ∧ C x x ∧ E x x) :=
  ⟨congSim ground ground groundSubstance,
   ⟨1, imageToGround ground⟩,
   fun _ hr he => ⟨hr, simCong _ _ he, he⟩⟩

/-- **The ten are removable.** Dropping them from the clause list changes
nothing, which is the operative form of `the_closes_are_definitional`: a proof
that consumed a close was consuming a definition. -/
theorem prefix_is_its_fourteen_contentful_clauses (ground : Form)
    (f2f : Form → Form) (S C E : Form → Form → Prop) :
    PrefixAxioms ground f2f S C E ↔ ContentfulPrefixAxioms ground f2f S C E := by
  constructor
  · intro h
    exact { axDiff := h.axDiff
            axSim := h.axSim
            axBox := h.axBox
            axGroundSelf := h.axGroundSelf
            axSyntaxRequiresSubstance := h.axSyntaxRequiresSubstance
            axSubstanceRequiresSemantics := h.axSubstanceRequiresSemantics
            axSemanticsRequiresSyntax := h.axSemanticsRequiresSyntax
            axFormClosesLoop := h.axFormClosesLoop
            axGroundSyntaxAx := h.axGroundSyntaxAx
            axGroundSubstanceAx := h.axGroundSubstanceAx
            axGroundSemanticsAx := h.axGroundSemanticsAx
            filtrationSimCong := h.filtrationSimCong
            filtrationCongSim := h.filtrationCongSim
            traceLevels := h.traceLevels }
  · intro h
    exact { axDiff := h.axDiff
            axSim := h.axSim
            axBox := h.axBox
            axGroundSelf := h.axGroundSelf
            closeStructContinues := fun _ => Iff.rfl
            closeStructDistinct := fun _ _ => Iff.rfl
            closeStructOrbits := fun _ => Iff.rfl
            axSyntaxRequiresSubstance := h.axSyntaxRequiresSubstance
            axSubstanceRequiresSemantics := h.axSubstanceRequiresSemantics
            axSemanticsRequiresSyntax := h.axSemanticsRequiresSyntax
            axFormClosesLoop := h.axFormClosesLoop
            axGroundSyntaxAx := h.axGroundSyntaxAx
            axGroundSubstanceAx := h.axGroundSubstanceAx
            axGroundSemanticsAx := h.axGroundSemanticsAx
            filtrationSimCong := h.filtrationSimCong
            filtrationCongSim := h.filtrationCongSim
            closeSyntaxOpaque := fun _ => Iff.rfl
            closeSubstanceOpaque := fun _ => Iff.rfl
            closeSemanticsOpaque := fun _ => Iff.rfl
            closeDerivesOpaque := fun _ _ => Iff.rfl
            closeDischargeOpaque := fun _ _ => Iff.rfl
            closeDefinitionOpaque := fun _ _ => Iff.rfl
            closeFormClosureOpaque := fun _ => Iff.rfl
            traceLevels := h.traceLevels }

/-- **Twenty-nine clauses carry the content, and they are nineteen conditions.**

`all_thirty_nine_iff_nineteen_conditions` reduces 39 to nineteen. Ten of the 39
were already discharged before any of it began, so the reduction that was
actually performed is 29 to nineteen --- fourteen prefix clauses to eight
conditions, seven operation clauses to three, three composition clauses to
three, five transfinite clauses to five.

Stating it this way keeps the two numbers from being read as one result. The
ten come free with the reading; the other ten are proved. -/
theorem twenty_nine_clauses_carry_the_content (x ground ordinalLimit : Form)
    (f2f ordinalSucc : Form → Form) (S C E : Form → Form → Prop)
    {CPath : Type} (cp : CPath → CPath → Prop) (comp : CPath → CPath → CPath)
    (e : CPath) :
    (ContentfulPrefixAxioms ground f2f S C E ∧ OperationAxioms S C ∧
        ComposeAxioms (Form := Form) cp comp e ∧
        ∃ (ps pe : Unit → Form) (deriver : Form),
          TransfiniteAxioms ground f2f S C E ps pe deriver ordinalLimit ordinalSucc)
      ↔ (Conditions ground f2f S C E ∧ OperationConditions S C ∧
          ComposeConditions cp comp e ∧
          TransfiniteConditions ground f2f S C E ordinalLimit ordinalSucc) := by
  have whole := all_thirty_nine_iff_nineteen_conditions x ground ordinalLimit f2f
    ordinalSucc S C E cp comp e
  have closes := prefix_is_its_fourteen_contentful_clauses (Form := Form) ground f2f S C E
  constructor
  · rintro ⟨hp, rest⟩
    exact whole.mp ⟨closes.mpr hp, rest⟩
  · intro h
    obtain ⟨hp, rest⟩ := whole.mpr h
    exact ⟨closes.mp hp, rest⟩

/-- The canonical clause list with the interpretation left open.

The 44 fields below are the fields of `TransportCountermodel.FullAxioms`,
character for character; `test_the_canonical_list_is_the_declared_one` checks
that they still are. What differs is the binding: that structure states the
clauses over one model's definitions, and this one takes the carrier, the three
relations and the ten auxiliary predicates as parameters, so the same statements
can be read at any interpretation --- including the free one, which is what
`the_canonical_clauses_are_the_free_ones` does with them.

The five closing clauses of L0 §VIII.b and L2 §II are at the end. They are
stated over the same free relations as everything else, which is the point of
the free reading: `axDiffCongruent` and `axCongruentTrans` say what `=~` is
and `axSimilarRefl` and `axSimilarSymm` say what `~~` is, and at the free
reading those are properties of the relations themselves rather than of any
particular interpretation of them. -/
structure CanonicalAxioms (ground ordinalLimit deriver : Form)
    (f2f ordinalSucc : Form → Form)
    (Similar Congruent Simulation structContinues structDistinct structOrbits :
      Form → Form → Prop)
    (HMSyntax Substance Semantics FormClosure : Form → Prop)
    (Derives Discharge Definition : Form → Form → Prop)
    {DerivationPath : Type} (compose : DerivationPath → DerivationPath → DerivationPath)
    (pathGround : DerivationPath) (congruentPath : DerivationPath → DerivationPath → Prop)
    (pathStart pathEnd : DerivationPath → Form) : Prop where
  axBox : ∀ (x : Form), structOrbits (f2f (f2f x)) x
  axComposeAssoc : ∀ (p q r : DerivationPath), congruentPath (compose p (compose q r)) (compose (compose p q) r)
  axComposeIdentity : ∀ (p : DerivationPath), And (congruentPath (compose p pathGround) p) (congruentPath (compose pathGround p) p)
  axComposeNonempty : Form → Form → Exists fun p => Not (congruentPath p pathGround)
  axCoop : ∀ (a b : Form), Exists fun c => And (Similar c a) (Similar c b)
  axCoopComm : ∀ (a b : Form), Exists fun ca => Exists fun cab => And (Similar ca a) (And (Similar ca b) (And (Similar cab b) (And (Similar cab a) (Congruent ca cab))))
  axCoopIdentity : ∀ (a : Form), Exists fun c => And (Similar c a) (Congruent c a)
  axDeriverAtLimit : Eq deriver ordinalLimit
  axDiff : ∀ (x : Form), structDistinct (f2f x) ground
  axFormClosesLoop : ∀ (x : Form), HMSyntax x → Semantics x → FormClosure x
  axGroundSelf : structContinues ground ground
  axGroundSemanticsAx : Semantics ground
  axGroundSubstanceAx : Substance ground
  axGroundSyntaxAx : HMSyntax ground
  axLimitDerives : Exists fun limitPath => And (Similar (pathStart limitPath) ground) (Congruent (pathEnd limitPath) ordinalLimit)
  axLimitIsLimit : ∀ (y : Form), (∀ (n : Nat), Derives (Nat.repeat f2f n ground) y) → Derives ordinalLimit y
  axLimitNotFinite : ∀ (n : Nat), Not (Simulation (Nat.repeat f2f n ground) ordinalLimit)
  axSemanticsRequiresSyntax : ∀ (x : Form), Semantics x → HMSyntax x
  axSeq : ∀ (a b : Form), Exists fun c => And (Similar c a) (Similar c b)
  axSeqAsymm : ∀ (a b : Form), Not (Congruent a b) → Exists fun c => Exists fun d => And (Similar c a) (And (Similar c b) (And (Similar d b) (And (Similar d a) (Not (Congruent c d)))))
  axSeqIdentityL : ∀ (a : Form), Exists fun c => And (Similar c a) (Congruent c a)
  axSeqIdentityR : ∀ (a : Form), Exists fun c => And (Similar c a) (Congruent c a)
  axSim : ∀ (x : Form), structContinues (f2f x) ground
  axSubstanceRequiresSemantics : ∀ (x : Form), Substance x → Semantics x
  axSuccExtends : ∀ (x : Form), And (Derives x (ordinalSucc x)) (Not (Simulation (ordinalSucc x) x))
  axSyntaxRequiresSubstance : ∀ (x : Form), HMSyntax x → Substance x
  closeDefinitionOpaque : ∀ (n x : Form), Iff (Definition n x) (Derives n x)
  closeDerivesOpaque : ∀ (x y : Form), Iff (Derives x y) (Exists fun n => Congruent (Nat.repeat f2f n x) y)
  closeDischargeOpaque : ∀ (c e : Form), Iff (Discharge c e) (Derives e c)
  closeFormClosureOpaque : ∀ (x : Form), Iff (FormClosure x) (And (HMSyntax x) (And (Substance x) (Semantics x)))
  closeSemanticsOpaque : ∀ (x : Form), Iff (Semantics x) (Simulation x x)
  closeStructContinues : ∀ (x : Form), Iff (structContinues x ground) (Similar x ground)
  closeStructDistinct : ∀ (x y : Form), Iff (structDistinct x y) (Not (Simulation x y))
  closeStructOrbits : ∀ (x : Form), Iff (structOrbits (f2f (f2f x)) x) (Similar (f2f (f2f x)) x)
  closeSubstanceOpaque : ∀ (x : Form), Iff (Substance x) (Congruent x x)
  closeSyntaxOpaque : ∀ (x : Form), Iff (HMSyntax x) (Exists fun n => Similar (Nat.repeat f2f n ground) x)
  filtrationCongSim : ∀ (x y : Form), Congruent x y → Similar x y
  filtrationSimCong : ∀ (x y : Form), Simulation x y → Congruent x y
  traceLevels : ∀ (x : Form), And (Similar (f2f x) x) (And (Congruent (f2f x) x → Similar (f2f x) x) (Simulation (f2f x) x → Congruent (f2f x) x))
  axDiffCongruent : ∀ (x : Form), Not (Congruent (f2f x) ground)
  axSimilarRefl : ∀ (x : Form), Similar x x
  axSimilarSymm : ∀ (x y : Form), Similar x y → Similar y x
  axCongruentTrans : ∀ (x y z : Form), Congruent x y → Congruent y z → Congruent x z
  axCongruentPathSymm : ∀ (p q : DerivationPath), congruentPath p q → congruentPath q p

/-- **The canonical clauses are the free ones.** Every earlier result about the
clause set is stated over the five structures below; every model states the
list above. The two were joined by the names of the clauses and by nothing
else --- and a name says which clause is meant, never what it says. This joins
them by what they say: read the canonical list at the free interpretation of
its ten auxiliary predicates and it *is* the conjunction of the five.

The proof is field projections and no tactic, which is the sharp form of the
result. The two lists are not merely equivalent, and not equivalent by way of
the `close*` clauses that fix the auxiliary predicates --- each clause is
definitionally the one it corresponds to, so what a model has to satisfy is
the same object under both readings and stays the same under any change that
keeps the definitions. -/
theorem the_canonical_clauses_are_the_free_ones (ground ordinalLimit deriver : Form)
    (f2f ordinalSucc : Form → Form) (S C E : Form → Form → Prop)
    {Path : Type} (comp : Path → Path → Path) (e : Path) (cp : Path → Path → Prop)
    (ps pe : Path → Form) :
    CanonicalAxioms ground ordinalLimit deriver f2f ordinalSucc S C E
        (structContinues ground S) (structDistinct E) (structOrbits S)
        (HMSyntax ground f2f S) (Substance C) (Semantics E)
        (FormClosure ground f2f S C E) (Derives f2f C) (Discharge f2f C)
        (Definition f2f C) comp e cp ps pe ↔
      (PrefixAxioms ground f2f S C E ∧ OperationAxioms S C ∧
        ComposeAxioms (Form := Form) cp comp e ∧
        TransfiniteAxioms ground f2f S C E ps pe deriver ordinalLimit ordinalSucc ∧
        ClosingAxioms (Path := Path) ground f2f S C cp) := by
  constructor
  · intro h
    exact ⟨{ axDiff := h.axDiff,
             axSim := h.axSim,
             axBox := h.axBox,
             axGroundSelf := h.axGroundSelf,
             closeStructContinues := h.closeStructContinues,
             closeStructDistinct := h.closeStructDistinct,
             closeStructOrbits := h.closeStructOrbits,
             axSyntaxRequiresSubstance := h.axSyntaxRequiresSubstance,
             axSubstanceRequiresSemantics := h.axSubstanceRequiresSemantics,
             axSemanticsRequiresSyntax := h.axSemanticsRequiresSyntax,
             axFormClosesLoop := h.axFormClosesLoop,
             axGroundSyntaxAx := h.axGroundSyntaxAx,
             axGroundSubstanceAx := h.axGroundSubstanceAx,
             axGroundSemanticsAx := h.axGroundSemanticsAx,
             filtrationSimCong := h.filtrationSimCong,
             filtrationCongSim := h.filtrationCongSim,
             closeSyntaxOpaque := h.closeSyntaxOpaque,
             closeSubstanceOpaque := h.closeSubstanceOpaque,
             closeSemanticsOpaque := h.closeSemanticsOpaque,
             closeDerivesOpaque := h.closeDerivesOpaque,
             closeDischargeOpaque := h.closeDischargeOpaque,
             closeDefinitionOpaque := h.closeDefinitionOpaque,
             closeFormClosureOpaque := h.closeFormClosureOpaque,
             traceLevels := h.traceLevels },
           { axSeq := h.axSeq,
             axSeqAsymm := h.axSeqAsymm,
             axSeqIdentityR := h.axSeqIdentityR,
             axSeqIdentityL := h.axSeqIdentityL,
             axCoop := h.axCoop,
             axCoopComm := h.axCoopComm,
             axCoopIdentity := h.axCoopIdentity },
           { axComposeAssoc := h.axComposeAssoc,
             axComposeIdentity := h.axComposeIdentity,
             axComposeNonempty := h.axComposeNonempty },
           { axDeriverAtLimit := h.axDeriverAtLimit,
             axLimitDerives := h.axLimitDerives,
             axLimitIsLimit := h.axLimitIsLimit,
             axLimitNotFinite := h.axLimitNotFinite,
             axSuccExtends := h.axSuccExtends },
           { axDiffCongruent := h.axDiffCongruent,
             axSimilarRefl := h.axSimilarRefl,
             axSimilarSymm := h.axSimilarSymm,
             axCongruentTrans := h.axCongruentTrans,
             axCongruentPathSymm := h.axCongruentPathSymm }⟩
  · rintro ⟨hp, ho, hc, ht, hk⟩
    exact { axDiff := hp.axDiff
            axSim := hp.axSim
            axBox := hp.axBox
            axGroundSelf := hp.axGroundSelf
            closeStructContinues := hp.closeStructContinues
            closeStructDistinct := hp.closeStructDistinct
            closeStructOrbits := hp.closeStructOrbits
            axSyntaxRequiresSubstance := hp.axSyntaxRequiresSubstance
            axSubstanceRequiresSemantics := hp.axSubstanceRequiresSemantics
            axSemanticsRequiresSyntax := hp.axSemanticsRequiresSyntax
            axFormClosesLoop := hp.axFormClosesLoop
            axGroundSyntaxAx := hp.axGroundSyntaxAx
            axGroundSubstanceAx := hp.axGroundSubstanceAx
            axGroundSemanticsAx := hp.axGroundSemanticsAx
            filtrationSimCong := hp.filtrationSimCong
            filtrationCongSim := hp.filtrationCongSim
            closeSyntaxOpaque := hp.closeSyntaxOpaque
            closeSubstanceOpaque := hp.closeSubstanceOpaque
            closeSemanticsOpaque := hp.closeSemanticsOpaque
            closeDerivesOpaque := hp.closeDerivesOpaque
            closeDischargeOpaque := hp.closeDischargeOpaque
            closeDefinitionOpaque := hp.closeDefinitionOpaque
            closeFormClosureOpaque := hp.closeFormClosureOpaque
            traceLevels := hp.traceLevels
            axSeq := ho.axSeq
            axSeqAsymm := ho.axSeqAsymm
            axSeqIdentityR := ho.axSeqIdentityR
            axSeqIdentityL := ho.axSeqIdentityL
            axCoop := ho.axCoop
            axCoopComm := ho.axCoopComm
            axCoopIdentity := ho.axCoopIdentity
            axComposeAssoc := hc.axComposeAssoc
            axComposeIdentity := hc.axComposeIdentity
            axComposeNonempty := hc.axComposeNonempty
            axDeriverAtLimit := ht.axDeriverAtLimit
            axLimitDerives := ht.axLimitDerives
            axLimitIsLimit := ht.axLimitIsLimit
            axLimitNotFinite := ht.axLimitNotFinite
            axSuccExtends := ht.axSuccExtends
            axDiffCongruent := hk.axDiffCongruent
            axSimilarRefl := hk.axSimilarRefl
            axSimilarSymm := hk.axSimilarSymm
            axCongruentTrans := hk.axCongruentTrans
            axCongruentPathSymm := hk.axCongruentPathSymm }

/-! ### Is any one of the eight implied by the other seven?

`prefixAxioms_iff_conditions` reduces the clause list to eight conditions and says
nothing about how the eight stand to each other. The names below make that
question askable: each is one field of `Conditions` as a proposition of its own,
`conditions_iff_the_eight` checks that the list is the same list, and the two
lemmas after it find the only implications that hold between them --- one half
of each diagonal biconditional, from the other diagonal and the inclusion. -/

def SimIntoCong (C E : Form → Form → Prop) : Prop := ∀ x y, E x y → C x y
def CongIntoSim (S C : Form → Form → Prop) : Prop := ∀ x y, C x y → S x y
def ImageSimilar (f2f : Form → Form) (S : Form → Form → Prop) : Prop :=
  ∀ x, S (f2f x) x
def ImageSimilarToGround (ground : Form) (f2f : Form → Form)
    (S : Form → Form → Prop) : Prop := ∀ x, S (f2f x) ground
def DoubleImageSimilar (f2f : Form → Form) (S : Form → Form → Prop) : Prop :=
  ∀ x, S (f2f (f2f x)) x
def ImageNotSimulatingGround (ground : Form) (f2f : Form → Form)
    (E : Form → Form → Prop) : Prop := ∀ x, ¬ E (f2f x) ground
def CongruentDiagonalIsReach (ground : Form) (f2f : Form → Form)
    (S C : Form → Form → Prop) : Prop := ∀ x, C x x ↔ Reach ground f2f S x
def SimulationDiagonalIsReach (ground : Form) (f2f : Form → Form)
    (S E : Form → Form → Prop) : Prop := ∀ x, E x x ↔ Reach ground f2f S x

/-- The eight names are the eight fields, in order and with nothing added. -/
theorem conditions_iff_the_eight (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) :
    Conditions ground f2f S C E ↔
      (SimIntoCong C E ∧ CongIntoSim S C ∧ ImageSimilar f2f S ∧
        ImageSimilarToGround ground f2f S ∧ DoubleImageSimilar f2f S ∧
        ImageNotSimulatingGround ground f2f E ∧
        CongruentDiagonalIsReach ground f2f S C ∧
        SimulationDiagonalIsReach ground f2f S E) := by
  constructor
  · intro h
    exact ⟨h.simIntoCong, h.congIntoSim, h.imageSimilar, h.imageSimilarToGround,
      h.doubleImageSimilar, h.imageNotSimulatingGround, h.congruentDiagonalIsReach,
      h.simulationDiagonalIsReach⟩
  · rintro ⟨a, b, c, d, e, f, g, i⟩
    exact { simIntoCong := a, congIntoSim := b, imageSimilar := c,
            imageSimilarToGround := d, doubleImageSimilar := e,
            imageNotSimulatingGround := f, congruentDiagonalIsReach := g,
            simulationDiagonalIsReach := i }

/-- Half of `CongruentDiagonalIsReach` is free. A reached point self-simulates
by the other diagonal, and self-simulation is self-congruence by the inclusion,
so nothing has to assume that reaching a point makes it congruent to itself. -/
theorem reached_points_are_self_congruent {ground : Form} {f2f : Form → Form}
    {S C E : Form → Form → Prop} (inclusion : SimIntoCong C E)
    (simulation : SimulationDiagonalIsReach ground f2f S E) :
    ∀ x, Reach ground f2f S x → C x x :=
  fun x hx => inclusion x x ((simulation x).mpr hx)

/-- And half of `SimulationDiagonalIsReach` is free for the mirror reason: a
self-simulating point is self-congruent by the inclusion, and self-congruence is
reachability by the other diagonal. -/
theorem self_simulating_points_are_reached {ground : Form} {f2f : Form → Form}
    {S C E : Form → Form → Prop} (inclusion : SimIntoCong C E)
    (congruence : CongruentDiagonalIsReach ground f2f S C) :
    ∀ x, E x x → Reach ground f2f S x :=
  fun x hx => (congruence x).mp (inclusion x x hx)

/-- The eight with both free halves removed: six conditions and two
implications, one running each way between the two diagonals and `Reach`. -/
structure SharpConditions (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) : Prop where
  simIntoCong : ∀ x y, E x y → C x y
  congIntoSim : ∀ x y, C x y → S x y
  imageSimilar : ∀ x, S (f2f x) x
  imageSimilarToGround : ∀ x, S (f2f x) ground
  doubleImageSimilar : ∀ x, S (f2f (f2f x)) x
  imageNotSimulatingGround : ∀ x, ¬ E (f2f x) ground
  congruentDiagonalReaches : ∀ x, C x x → Reach ground f2f S x
  reachedIsSelfSimulating : ∀ x, Reach ground f2f S x → E x x

/-- **Irredundant is not minimal.** The two biconditionals can be replaced by
one implication each --- congruence descending to `Reach` and `Reach` rising to
simulation --- and the other halves come back through the inclusion. Which two
halves to keep is forced: the inclusion runs from simulation to congruence, so
the halves that survive are the ones that run against it. -/
theorem conditions_iff_six_and_two_implications (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) :
    Conditions ground f2f S C E ↔ SharpConditions ground f2f S C E := by
  constructor
  · intro h
    exact { simIntoCong := h.simIntoCong
            congIntoSim := h.congIntoSim
            imageSimilar := h.imageSimilar
            imageSimilarToGround := h.imageSimilarToGround
            doubleImageSimilar := h.doubleImageSimilar
            imageNotSimulatingGround := h.imageNotSimulatingGround
            congruentDiagonalReaches := fun x => (h.congruentDiagonalIsReach x).mp
            reachedIsSelfSimulating := fun x => (h.simulationDiagonalIsReach x).mpr }
  · intro h
    exact { simIntoCong := h.simIntoCong
            congIntoSim := h.congIntoSim
            imageSimilar := h.imageSimilar
            imageSimilarToGround := h.imageSimilarToGround
            doubleImageSimilar := h.doubleImageSimilar
            imageNotSimulatingGround := h.imageNotSimulatingGround
            congruentDiagonalIsReach := fun x =>
              ⟨h.congruentDiagonalReaches x,
               fun hr => h.simIntoCong x x (h.reachedIsSelfSimulating x hr)⟩
            simulationDiagonalIsReach := fun x =>
              ⟨fun he => h.congruentDiagonalReaches x (h.simIntoCong x x he),
               h.reachedIsSelfSimulating x⟩ }

/-! Eight models follow, one per condition: each satisfies the other seven and
refutes its own. Four of them keep similarity total, which makes `Reach` total
and reduces both diagonals to reflexivity of the relation named. -/

namespace NeedsSimIntoCong

/-- Simulation reaching past congruence at one off-diagonal pair. Both diagonals
still agree with `Reach`, which is total here, so only the inclusion fails. -/
def S (_ _ : Nat) : Prop := True
def C (a b : Nat) : Prop := a = b
def E (a b : Nat) : Prop := a = b ∨ b = 1

theorem reach (x : Nat) : Reach 0 Nat.succ S x := ⟨0, trivial⟩

theorem seven_hold_and_the_inclusion_fails :
    CongIntoSim S C ∧ ImageSimilar Nat.succ S ∧ ImageSimilarToGround 0 Nat.succ S ∧
      DoubleImageSimilar Nat.succ S ∧ ImageNotSimulatingGround 0 Nat.succ E ∧
      CongruentDiagonalIsReach 0 Nat.succ S C ∧
      SimulationDiagonalIsReach 0 Nat.succ S E ∧
      ¬ SimIntoCong C E :=
  ⟨fun _ _ _ => trivial, fun _ => trivial, fun _ => trivial, fun _ => trivial,
   fun x h => h.elim (Nat.succ_ne_zero x) (fun k => Nat.noConfusion k),
   fun x => ⟨fun _ => reach x, fun _ => rfl⟩,
   fun x => ⟨fun _ => reach x, fun _ => Or.inl rfl⟩,
   fun h => Nat.noConfusion (h 0 1 (Or.inr rfl))⟩

end NeedsSimIntoCong

namespace NeedsCongIntoSim

/-- Congruence reaching past similarity at one off-diagonal pair. Similarity is
still total everywhere the other seven look at it. -/
def S (a b : Nat) : Prop := ¬ (a = 0 ∧ b = 1)
def C (_ _ : Nat) : Prop := True
def E (a b : Nat) : Prop := a = b

theorem reach (x : Nat) : Reach 0 Nat.succ S x :=
  ⟨1, fun h => Nat.succ_ne_zero 0 h.1⟩

theorem seven_hold_and_the_descent_fails :
    SimIntoCong C E ∧ ImageSimilar Nat.succ S ∧ ImageSimilarToGround 0 Nat.succ S ∧
      DoubleImageSimilar Nat.succ S ∧ ImageNotSimulatingGround 0 Nat.succ E ∧
      CongruentDiagonalIsReach 0 Nat.succ S C ∧
      SimulationDiagonalIsReach 0 Nat.succ S E ∧
      ¬ CongIntoSim S C :=
  ⟨fun _ _ _ => trivial,
   fun x h => Nat.succ_ne_zero x h.1,
   fun x h => Nat.succ_ne_zero x h.1,
   fun x h => Nat.succ_ne_zero (Nat.succ x) h.1,
   fun x h => Nat.succ_ne_zero x h,
   fun x => ⟨fun _ => reach x, fun _ => trivial⟩,
   fun x => ⟨fun _ => reach x, fun _ => rfl⟩,
   fun h => h 0 1 trivial ⟨rfl, rfl⟩⟩

end NeedsCongIntoSim

namespace NeedsImageNotSimulatingGround

/-- Everything total. The seven that remain are satisfied by the largest reading
of all three relations, and the only clause such a reading can break is the one
denial in the list. -/
def S (_ _ : Nat) : Prop := True
def C (_ _ : Nat) : Prop := True
def E (_ _ : Nat) : Prop := True

theorem reach (x : Nat) : Reach 0 Nat.succ S x := ⟨0, trivial⟩

theorem seven_hold_and_the_denial_fails :
    SimIntoCong C E ∧ CongIntoSim S C ∧ ImageSimilar Nat.succ S ∧
      ImageSimilarToGround 0 Nat.succ S ∧ DoubleImageSimilar Nat.succ S ∧
      CongruentDiagonalIsReach 0 Nat.succ S C ∧
      SimulationDiagonalIsReach 0 Nat.succ S E ∧
      ¬ ImageNotSimulatingGround 0 Nat.succ E :=
  ⟨fun _ _ _ => trivial, fun _ _ _ => trivial, fun _ => trivial, fun _ => trivial,
   fun _ => trivial,
   fun x => ⟨fun _ => reach x, fun _ => trivial⟩,
   fun x => ⟨fun _ => reach x, fun _ => trivial⟩,
   fun h => h 0 trivial⟩

end NeedsImageNotSimulatingGround

namespace NeedsSimulationDiagonalIsReach

/-- Simulation empty. The inclusion is then vacuous and the congruent diagonal
still agrees with `Reach`, so the only thing left to fail is the simulation
diagonal --- and it fails in the direction `self_simulating_points_are_reached`
does not cover, which is what the model is for. -/
def S (_ _ : Nat) : Prop := True
def C (_ _ : Nat) : Prop := True
def E (_ _ : Nat) : Prop := False

theorem reach (x : Nat) : Reach 0 Nat.succ S x := ⟨0, trivial⟩

theorem seven_hold_and_the_simulation_diagonal_fails :
    SimIntoCong C E ∧ CongIntoSim S C ∧ ImageSimilar Nat.succ S ∧
      ImageSimilarToGround 0 Nat.succ S ∧ DoubleImageSimilar Nat.succ S ∧
      ImageNotSimulatingGround 0 Nat.succ E ∧
      CongruentDiagonalIsReach 0 Nat.succ S C ∧
      ¬ SimulationDiagonalIsReach 0 Nat.succ S E :=
  ⟨fun _ _ h => h.elim, fun _ _ _ => trivial, fun _ => trivial, fun _ => trivial,
   fun _ => trivial, fun _ h => h,
   fun x => ⟨fun _ => reach x, fun _ => trivial⟩,
   fun h => (h 0).mpr (reach 0)⟩

/-- And the same here, on the other side: what fails is `Reach` rising to
simulation. Between them these two say the sharp list is irredundant where the
sharpening happened. -/
theorem the_rising_half_is_not_derivable :
    ¬ (∀ x : Nat, Reach 0 Nat.succ S x → E x x) :=
  fun h => h 0 (reach 0)

end NeedsSimulationDiagonalIsReach

namespace NeedsImageSimilar

/-- Forming is similar to the ground and to its own double image, but not to its
argument: one pair thinned, at every step but the first. -/
def S (a b : Nat) : Prop := b = 0 ∨ a ≠ b + 1
def C (a b : Nat) : Prop := S a b
def E (a b : Nat) : Prop := a = b

theorem reach (x : Nat) : Reach 0 Nat.succ S x :=
  ⟨0, Or.inr (fun h => Nat.succ_ne_zero x h.symm)⟩

theorem seven_hold_and_the_image_is_not_similar :
    SimIntoCong C E ∧ CongIntoSim S C ∧ ImageSimilarToGround 0 Nat.succ S ∧
      DoubleImageSimilar Nat.succ S ∧ ImageNotSimulatingGround 0 Nat.succ E ∧
      CongruentDiagonalIsReach 0 Nat.succ S C ∧
      SimulationDiagonalIsReach 0 Nat.succ S E ∧
      ¬ ImageSimilar Nat.succ S :=
  ⟨fun x y h => by subst h; exact Or.inr (by omega),
   fun _ _ h => h,
   fun _ => Or.inl rfl,
   fun _ => Or.inr (by omega),
   fun x h => Nat.succ_ne_zero x h,
   fun x => ⟨fun _ => reach x, fun _ => Or.inr (by omega)⟩,
   fun x => ⟨fun _ => reach x, fun _ => rfl⟩,
   fun h => (h 1).elim (fun k => Nat.noConfusion k) (fun k => k rfl)⟩

end NeedsImageSimilar

namespace NeedsImageSimilarToGround

/-- One image is not similar to the ground, chosen far enough along the chain
that neither the image clause nor the double-image clause can see the pair. -/
def S (a b : Nat) : Prop := ¬ (a = 3 ∧ b = 0)
def C (a b : Nat) : Prop := S a b
def E (a b : Nat) : Prop := a = b

theorem reach (x : Nat) : Reach 0 Nat.succ S x :=
  ⟨0, fun h => absurd h.1 (by decide)⟩

theorem seven_hold_and_the_image_misses_the_ground :
    SimIntoCong C E ∧ CongIntoSim S C ∧ ImageSimilar Nat.succ S ∧
      DoubleImageSimilar Nat.succ S ∧ ImageNotSimulatingGround 0 Nat.succ E ∧
      CongruentDiagonalIsReach 0 Nat.succ S C ∧
      SimulationDiagonalIsReach 0 Nat.succ S E ∧
      ¬ ImageSimilarToGround 0 Nat.succ S :=
  ⟨fun x y h => by subst h; intro k; omega,
   fun _ _ h => h,
   fun _ => by intro h; omega,
   fun _ => by intro h; omega,
   fun x h => Nat.succ_ne_zero x h,
   fun x => ⟨fun _ => reach x, fun _ => by intro h; omega⟩,
   fun x => ⟨fun _ => reach x, fun _ => rfl⟩,
   fun h => h 2 ⟨rfl, rfl⟩⟩

end NeedsImageSimilarToGround

namespace NeedsDoubleImageSimilar

/-- Forming is similar to its argument and to the ground; forming twice is not
similar to where it started. The pair the other two similarity clauses never
mention. -/
def S (a b : Nat) : Prop := b = 0 ∨ a ≠ b + 2
def C (a b : Nat) : Prop := S a b
def E (a b : Nat) : Prop := a = b

theorem reach (x : Nat) : Reach 0 Nat.succ S x :=
  ⟨0, Or.inr (fun h => Nat.succ_ne_zero (x + 1) h.symm)⟩

theorem seven_hold_and_the_double_image_is_not_similar :
    SimIntoCong C E ∧ CongIntoSim S C ∧ ImageSimilar Nat.succ S ∧
      ImageSimilarToGround 0 Nat.succ S ∧ ImageNotSimulatingGround 0 Nat.succ E ∧
      CongruentDiagonalIsReach 0 Nat.succ S C ∧
      SimulationDiagonalIsReach 0 Nat.succ S E ∧
      ¬ DoubleImageSimilar Nat.succ S :=
  ⟨fun x y h => by subst h; exact Or.inr (by omega),
   fun _ _ h => h,
   fun _ => Or.inr (by omega),
   fun _ => Or.inl rfl,
   fun x h => Nat.succ_ne_zero x h,
   fun x => ⟨fun _ => reach x, fun _ => Or.inr (by omega)⟩,
   fun x => ⟨fun _ => reach x, fun _ => rfl⟩,
   fun h => (h 1).elim (fun k => Nat.noConfusion k) (fun k => k rfl)⟩

end NeedsDoubleImageSimilar

namespace NeedsCongruentDiagonalIsReach

/-- Every point is congruent to itself, and the chain never reaches the adjoined
one.

This is the one condition of the eight that cannot be refuted on the chain
carrier. `reached_points_are_self_congruent` already proves the direction
`Reach x → x =~ x` from the other seven, so a refutation has to withhold
`Reach` from a point that is congruent to itself --- and on `Nat` every point is
reached. The model is the existing extended carrier with `~~` and `≡`
unchanged and `=~` widened to plain equality, which is exactly the widening
`ext_conditions` refused to make. -/
def C : Extended → Extended → Prop := Eq

theorem eq_into_similar (x y : Extended) (h : C x y) : extSimilar x y := by
  subst h
  cases x with
  | none => exact Or.inr rfl
  | some n => exact Or.inl (fun k => Option.noConfusion k)

theorem seven_hold_and_the_congruent_diagonal_fails :
    SimIntoCong C extDiagonal ∧ CongIntoSim extSimilar C ∧
      ImageSimilar extStep extSimilar ∧
      ImageSimilarToGround extGround extStep extSimilar ∧
      DoubleImageSimilar extStep extSimilar ∧
      ImageNotSimulatingGround extGround extStep extDiagonal ∧
      SimulationDiagonalIsReach extGround extStep extSimilar extDiagonal ∧
      ¬ CongruentDiagonalIsReach extGround extStep extSimilar C :=
  ⟨fun _ _ h => h.1,
   eq_into_similar,
   ext_conditions.imageSimilar,
   ext_conditions.imageSimilarToGround,
   ext_conditions.doubleImageSimilar,
   ext_conditions.imageNotSimulatingGround,
   ext_conditions.simulationDiagonalIsReach,
   fun h => ext_none_unreached ((h none).mp rfl)⟩

/-- The same model refutes the sharp half, so nothing was lost in sharpening:
what fails is congruence descending to `Reach`, not the half the inclusion
already gives. -/
theorem the_descending_half_is_not_derivable :
    ¬ (∀ x : Extended, C x x → Reach extGround extStep extSimilar x) :=
  fun h => ext_none_unreached (h none rfl)

end NeedsCongruentDiagonalIsReach

/-! ### And the three the operations add?

`prefixWithOperations_iff_conditions` reaches 31 of the clauses with eleven
conditions, and `operations_exclude_the_unreached_point` already shows the three
are not implied by the eight. Whether any one of the three is implied by the
other ten is the same question asked where the two lists meet, and it is not the
same question as whether it is implied by the other two: the eight constrain the
same `S` and `C` the three quantify over. -/

def PairedWitnesses (S C : Form → Form → Prop) : Prop :=
  ∀ a b, ∃ ca cab, S ca a ∧ S ca b ∧ S cab b ∧ S cab a ∧ C ca cab
def IdentityWitness (S C : Form → Form → Prop) : Prop := ∀ a, ∃ c, S c a ∧ C c a
def ApartWitnesses (S C : Form → Form → Prop) : Prop :=
  ∀ a b, ¬ C a b → ∃ c d, S c a ∧ S c b ∧ S d b ∧ S d a ∧ ¬ C c d

/-- The three names are the three fields, in order and with nothing added. -/
theorem operationConditions_iff_the_three (S C : Form → Form → Prop) :
    OperationConditions S C ↔
      (PairedWitnesses S C ∧ IdentityWitness S C ∧ ApartWitnesses S C) :=
  ⟨fun h => ⟨h.pairedWitnesses, h.identityWitness, h.apartWitnesses⟩,
   fun ⟨paired, identity, apart⟩ => ⟨paired, identity, apart⟩⟩

/-- **A reached point is its own identity witness.** `congruentDiagonalIsReach`
gives `C x x` and `congIntoSim` turns that into `S x x`, so `IdentityWitness` is
already proved wherever `Reach` arrives. Refuting it needs a point the chain
does not reach --- the same conclusion `reached_points_are_self_congruent`
forced on `CongruentDiagonalIsReach`, reached here from the other list. -/
theorem reached_points_are_their_own_identity_witness {ground : Form}
    {f2f : Form → Form} {S C E : Form → Form → Prop}
    (h : Conditions ground f2f S C E) {a : Form}
    (hr : Reach ground f2f S a) : ∃ c, S c a ∧ C c a :=
  have hc : C a a := (h.congruentDiagonalIsReach a).mpr hr
  ⟨a, h.congIntoSim a a hc, hc⟩

/-- **A reached common predecessor pairs the two points it lies under.** Serve
it as both witnesses and the last conjunct is `C c c`, which is `Reach c`. So a
pair refuting `PairedWitnesses` must have *every* common predecessor unreached
--- and each of those still owes an identity witness, which by the lemma above
cannot be a reached point either. That is why the model refuting it adjoins four
points and not one. -/
theorem a_reached_common_predecessor_pairs_them {ground : Form}
    {f2f : Form → Form} {S C E : Form → Form → Prop}
    (h : Conditions ground f2f S C E) {a b c : Form}
    (hca : S c a) (hcb : S c b) (hr : Reach ground f2f S c) :
    ∃ ca cab, S ca a ∧ S ca b ∧ S cab b ∧ S cab a ∧ C ca cab :=
  ⟨c, c, hca, hcb, hcb, hca, (h.congruentDiagonalIsReach c).mpr hr⟩

/-- **Two points lying under each other are their own apartness witnesses.**
Nothing from `Conditions` is used: `ApartWitnesses` at `(a, b)` is free as soon
as `S` holds at the four pairs drawn from `a` and `b`, because the hypothesis it
is given is exactly the denial its conclusion has to produce. Where `S` is total
that is every pair, so a model refuting it has to keep `S` thin --- and thin `S`
is what makes common predecessors scarce, which is the tension the three
conditions are balanced on. -/
theorem mutual_predecessors_are_apart_witnesses {S C : Form → Form → Prop}
    {a b : Form} (haa : S a a) (hab : S a b) (hba : S b a) (hbb : S b b)
    (hne : ¬ C a b) : ∃ c d, S c a ∧ S c b ∧ S d b ∧ S d a ∧ ¬ C c d :=
  ⟨a, b, haa, hab, hbb, hba, hne⟩

/-! Three models follow, one per operation condition. Each satisfies the eight
and the other two, and refutes its own. -/

namespace NeedsApartWitnesses

/-- The chain with one point adjoined. Every relation below is stated by cases
on the constructors, so the chain part can be kept as thin as the eight allow
while the adjoined point stays universal. -/
inductive Pt where
  | chain (n : Nat)
  | omega
  deriving DecidableEq

open Pt

def ground : Pt := chain 0

def step : Pt → Pt
  | chain n => chain (n + 1)
  | omega => omega

/-- `omega` lies under everything and everything lies under `omega`, so it is
both reached and a common predecessor of every pair. On the chain `S` is as thin
as `imageSimilar`, `doubleImageSimilar` and `imageSimilarToGround` permit: three
steps up, and the ground below everything. -/
def S : Pt → Pt → Prop
  | omega, _ => True
  | chain _, omega => True
  | chain m, chain n => (n ≤ m ∧ m ≤ n + 2) ∨ n = 0

def C : Pt → Pt → Prop := Eq

theorem repeat_step (n : Nat) : Nat.repeat step n ground = chain n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.repeat, ih, step]

theorem self (x : Pt) : S x x := by
  cases x with
  | chain m => exact Or.inl ⟨Nat.le_refl m, by omega⟩
  | omega => trivial

theorem reach (x : Pt) : Reach ground step S x := by
  cases x with
  | chain m => exact ⟨m, by rw [repeat_step]; exact Or.inl ⟨Nat.le_refl m, by omega⟩⟩
  | omega => exact ⟨0, by rw [repeat_step]; trivial⟩

theorem conditions : Conditions ground step S C C where
  simIntoCong := fun _ _ h => h
  congIntoSim := fun x y h => h ▸ self x
  imageSimilar := fun x => by
    cases x with
    | chain m => exact Or.inl ⟨Nat.le_succ m, by omega⟩
    | omega => trivial
  imageSimilarToGround := fun x => by
    cases x with
    | chain m => exact Or.inr rfl
    | omega => trivial
  doubleImageSimilar := fun x => by
    cases x with
    | chain m => exact Or.inl ⟨by omega, by omega⟩
    | omega => trivial
  imageNotSimulatingGround := fun x => by
    cases x with
    | chain m => exact fun h => Pt.noConfusion h (fun k => Nat.succ_ne_zero m k)
    | omega => exact fun h => Pt.noConfusion h
  congruentDiagonalIsReach := fun x => ⟨fun _ => reach x, fun _ => rfl⟩
  simulationDiagonalIsReach := fun x => ⟨fun _ => reach x, fun _ => rfl⟩

/-- The only common predecessor of `chain 1` and `chain 5` is `omega`. Three
steps do not span four, so no chain point lies under both. -/
theorem common_predecessor_is_omega {c : Pt}
    (one : S c (chain 1)) (five : S c (chain 5)) : c = omega := by
  cases c with
  | chain m =>
    rcases one with ⟨_, _⟩ | h
    · rcases five with ⟨_, _⟩ | h'
      · omega
      · exact absurd h' (by decide)
    · exact absurd h (by decide)
  | omega => rfl

theorem one_is_not_five : ¬ C (chain 1) (chain 5) := by
  intro h
  injection h with k
  exact absurd k (by decide)

theorem ten_hold_and_nothing_is_apart :
    Conditions ground step S C C ∧ PairedWitnesses S C ∧ IdentityWitness S C ∧
      ¬ ApartWitnesses S C :=
  ⟨conditions,
   fun _ _ => ⟨omega, omega, trivial, trivial, trivial, trivial, rfl⟩,
   fun a => ⟨a, self a, rfl⟩,
   fun h => by
     obtain ⟨c, d, hc1, hc5, hd5, hd1, hne⟩ := h (chain 1) (chain 5) one_is_not_five
     exact hne ((common_predecessor_is_omega hc1 hc5).trans
       (common_predecessor_is_omega hd1 hd5).symm)⟩

end NeedsApartWitnesses

namespace NeedsIdentityWitness

/-- The chain with two points adjoined, both off it. `p` and `q` lie under
everything and nothing on the chain lies under either, so both are unreached and
both are common predecessors of every pair. -/
inductive Pt where
  | chain (n : Nat)
  | p
  | q
  deriving DecidableEq

open Pt

def ground : Pt := chain 0

def step : Pt → Pt
  | chain n => chain (n + 1)
  | p => p
  | q => q

def S : Pt → Pt → Prop
  | Pt.p, _ => True
  | Pt.q, _ => True
  | chain _, Pt.p => False
  | chain _, Pt.q => False
  | chain m, chain n => (n ≤ m ∧ m ≤ n + 2) ∨ n = 0

/-- Congruence is equality on the chain and the single pair `p =~ q`. One pair
is what `imageSimilar` and the diagonal leave room for: the diagonal is fixed to
`Reach`, so neither adjoined point may be congruent to itself, and the direction
`q =~ p` is the one `IdentityWitness` would use. -/
def C : Pt → Pt → Prop
  | chain m, chain n => m = n
  | Pt.p, Pt.q => True
  | _, _ => False

theorem repeat_step (n : Nat) : Nat.repeat step n ground = chain n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.repeat, ih, step]

theorem reach_chain (m : Nat) : Reach ground step S (chain m) :=
  ⟨m, by rw [repeat_step]; exact Or.inl ⟨Nat.le_refl m, by omega⟩⟩

theorem p_unreached : ¬ Reach ground step S Pt.p := by
  rintro ⟨n, h⟩
  rw [repeat_step] at h
  exact h.elim

theorem q_unreached : ¬ Reach ground step S Pt.q := by
  rintro ⟨n, h⟩
  rw [repeat_step] at h
  exact h.elim

theorem conditions : Conditions ground step S C C where
  simIntoCong := fun _ _ h => h
  congIntoSim := fun x y h => by
    cases x with
    | chain m => cases y with
      | chain n =>
        have hmn : m = n := h
        exact Or.inl ⟨Nat.le_of_eq hmn.symm, by omega⟩
      | p => exact h.elim
      | q => exact h.elim
    | p => trivial
    | q => trivial
  imageSimilar := fun x => by
    cases x with
    | chain m => exact Or.inl ⟨Nat.le_succ m, by omega⟩
    | p => trivial
    | q => trivial
  imageSimilarToGround := fun x => by
    cases x with
    | chain m => exact Or.inr rfl
    | p => trivial
    | q => trivial
  doubleImageSimilar := fun x => by
    cases x with
    | chain m => exact Or.inl ⟨by omega, by omega⟩
    | p => trivial
    | q => trivial
  imageNotSimulatingGround := fun x => by
    cases x with
    | chain m => exact fun h => Nat.succ_ne_zero m h
    | p => exact fun h => h.elim
    | q => exact fun h => h.elim
  congruentDiagonalIsReach := fun x => by
    cases x with
    | chain m => exact ⟨fun _ => reach_chain m, fun _ => rfl⟩
    | p => exact ⟨fun h => h.elim, fun hr => absurd hr p_unreached⟩
    | q => exact ⟨fun h => h.elim, fun hr => absurd hr q_unreached⟩
  simulationDiagonalIsReach := fun x => by
    cases x with
    | chain m => exact ⟨fun _ => reach_chain m, fun _ => rfl⟩
    | p => exact ⟨fun h => h.elim, fun hr => absurd hr p_unreached⟩
    | q => exact ⟨fun h => h.elim, fun hr => absurd hr q_unreached⟩

/-- Only `p` and `q` lie under `p`, and neither is congruent to it. -/
theorem no_identity_witness_at_p : ¬ (∃ c, S c Pt.p ∧ C c Pt.p) := by
  rintro ⟨c, _, congruent⟩
  cases c with
  | chain m => exact congruent.elim
  | p => exact congruent.elim
  | q => exact congruent.elim

theorem ten_hold_and_one_point_has_no_identity_witness :
    Conditions ground step S C C ∧ PairedWitnesses S C ∧ ApartWitnesses S C ∧
      ¬ IdentityWitness S C :=
  ⟨conditions,
   fun _ _ => ⟨Pt.p, Pt.q, trivial, trivial, trivial, trivial, trivial⟩,
   fun a b _ => ⟨Pt.p, Pt.p, trivial, trivial, trivial, trivial, fun h => h.elim⟩,
   fun h => no_identity_witness_at_p (h Pt.p)⟩

end NeedsIdentityWitness

namespace NeedsPairedWitnesses

/-- The chain with four points adjoined. `p` and `q` lie under everything, so
they are the only common predecessors a pair of distant chain points has; `r`
and `s` lie under nothing but `p` and `q` respectively, and exist only to be the
identity witnesses `p` and `q` would otherwise lack. Four is the smallest number
that works, and `a_reached_common_predecessor_pairs_them` together with
`reached_points_are_their_own_identity_witness` is why: the common predecessors
must all be unreached and pairwise incongruent, and each of them still owes an
identity witness that cannot be reached either. -/
inductive Pt where
  | chain (n : Nat)
  | p
  | q
  | r
  | s
  deriving DecidableEq

open Pt

def ground : Pt := chain 0

def step : Pt → Pt
  | chain n => chain (n + 1)
  | Pt.p => Pt.p
  | Pt.q => Pt.q
  | Pt.r => Pt.p
  | Pt.s => Pt.q

def S : Pt → Pt → Prop
  | Pt.p, _ => True
  | Pt.q, _ => True
  | Pt.r, Pt.p => True
  | Pt.s, Pt.q => True
  | Pt.r, _ => False
  | Pt.s, _ => False
  | chain _, Pt.p => False
  | chain _, Pt.q => False
  | chain _, Pt.r => False
  | chain _, Pt.s => False
  | chain m, chain n => (n ≤ m ∧ m ≤ n + 2) ∨ n = 0

/-- Equality on the chain, and the two two-cycles `r =~ p =~ r` and
`s =~ q =~ s`. Nothing relates `p` to `q`, which is the whole refutation. -/
def C : Pt → Pt → Prop
  | chain m, chain n => m = n
  | Pt.r, Pt.p => True
  | Pt.p, Pt.r => True
  | Pt.s, Pt.q => True
  | Pt.q, Pt.s => True
  | _, _ => False

theorem repeat_step (n : Nat) : Nat.repeat step n ground = chain n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.repeat, ih, step]

theorem reach_chain (m : Nat) : Reach ground step S (chain m) :=
  ⟨m, by rw [repeat_step]; exact Or.inl ⟨Nat.le_refl m, by omega⟩⟩

theorem adjoined_unreached {x : Pt} (h : Reach ground step S x)
    (hx : ∀ n : Nat, ¬ S (chain n) x) : False := by
  obtain ⟨n, hn⟩ := h
  rw [repeat_step] at hn
  exact hx n hn

theorem conditions : Conditions ground step S C C where
  simIntoCong := fun _ _ h => h
  congIntoSim := fun x y h => by
    cases x with
    | chain m => cases y with
      | chain n =>
        have hmn : m = n := h
        exact Or.inl ⟨Nat.le_of_eq hmn.symm, by omega⟩
      | p => exact h.elim
      | q => exact h.elim
      | r => exact h.elim
      | s => exact h.elim
    | p => trivial
    | q => trivial
    | r => cases y with
      | chain n => exact h.elim
      | p => trivial
      | q => exact h.elim
      | r => exact h.elim
      | s => exact h.elim
    | s => cases y with
      | chain n => exact h.elim
      | p => exact h.elim
      | q => trivial
      | r => exact h.elim
      | s => exact h.elim
  imageSimilar := fun x => by
    cases x with
    | chain m => exact Or.inl ⟨Nat.le_succ m, by omega⟩
    | p => trivial
    | q => trivial
    | r => trivial
    | s => trivial
  imageSimilarToGround := fun x => by
    cases x with
    | chain m => exact Or.inr rfl
    | p => trivial
    | q => trivial
    | r => trivial
    | s => trivial
  doubleImageSimilar := fun x => by
    cases x with
    | chain m => exact Or.inl ⟨by omega, by omega⟩
    | p => trivial
    | q => trivial
    | r => trivial
    | s => trivial
  imageNotSimulatingGround := fun x => by
    cases x with
    | chain m => exact fun h => Nat.succ_ne_zero m h
    | p => exact fun h => h.elim
    | q => exact fun h => h.elim
    | r => exact fun h => h.elim
    | s => exact fun h => h.elim
  congruentDiagonalIsReach := fun x => by
    cases x with
    | chain m => exact ⟨fun _ => reach_chain m, fun _ => rfl⟩
    | p => exact ⟨fun h => h.elim, fun hr => (adjoined_unreached hr fun _ h => h).elim⟩
    | q => exact ⟨fun h => h.elim, fun hr => (adjoined_unreached hr fun _ h => h).elim⟩
    | r => exact ⟨fun h => h.elim, fun hr => (adjoined_unreached hr fun _ h => h).elim⟩
    | s => exact ⟨fun h => h.elim, fun hr => (adjoined_unreached hr fun _ h => h).elim⟩
  simulationDiagonalIsReach := fun x => by
    cases x with
    | chain m => exact ⟨fun _ => reach_chain m, fun _ => rfl⟩
    | p => exact ⟨fun h => h.elim, fun hr => (adjoined_unreached hr fun _ h => h).elim⟩
    | q => exact ⟨fun h => h.elim, fun hr => (adjoined_unreached hr fun _ h => h).elim⟩
    | r => exact ⟨fun h => h.elim, fun hr => (adjoined_unreached hr fun _ h => h).elim⟩
    | s => exact ⟨fun h => h.elim, fun hr => (adjoined_unreached hr fun _ h => h).elim⟩

/-- Three steps do not span four, so no chain point lies under both `chain 1`
and `chain 5`, and `r` and `s` lie under neither. -/
theorem common_predecessor_is_p_or_q {c : Pt}
    (one : S c (chain 1)) (five : S c (chain 5)) : c = Pt.p ∨ c = Pt.q := by
  cases c with
  | chain m =>
    rcases one with ⟨a1, a2⟩ | h
    · rcases five with ⟨b1, b2⟩ | h'
      · omega
      · exact absurd h' (by decide)
    · exact absurd h (by decide)
  | p => exact Or.inl rfl
  | q => exact Or.inr rfl
  | r => exact one.elim
  | s => exact one.elim

theorem ten_hold_and_one_pair_is_unpaired :
    Conditions ground step S C C ∧ IdentityWitness S C ∧ ApartWitnesses S C ∧
      ¬ PairedWitnesses S C :=
  ⟨conditions,
   fun a => by
     cases a with
     | chain m => exact ⟨chain m, Or.inl ⟨Nat.le_refl m, by omega⟩, rfl⟩
     | p => exact ⟨Pt.r, trivial, trivial⟩
     | q => exact ⟨Pt.s, trivial, trivial⟩
     | r => exact ⟨Pt.p, trivial, trivial⟩
     | s => exact ⟨Pt.q, trivial, trivial⟩,
   fun _ _ _ => ⟨Pt.p, Pt.p, trivial, trivial, trivial, trivial, fun h => h.elim⟩,
   fun h => by
     obtain ⟨ca, cab, hca1, hca5, hcab5, hcab1, hc⟩ := h (chain 1) (chain 5)
     rcases common_predecessor_is_p_or_q hca1 hca5 with rfl | rfl <;>
       rcases common_predecessor_is_p_or_q hcab1 hcab5 with rfl | rfl <;>
         exact hc.elim⟩

end NeedsPairedWitnesses

/-! ### And the three the composition adds?

`compose_conditions_are_always_available` shows the three are met by some path
structure whatever the eleven say, because the symbols are disjoint. Whether any
one of the three is implied by the other two is what that leaves --- and here,
unlike the operations, it is a question about the list alone. The path type, its
composition, its unit and `congruentPath` are all free, so a model is a small
algebra and there is no carrier to satisfy first. -/

def AssociativeUpToCp {Path : Type} (cp : Path → Path → Prop)
    (comp : Path → Path → Path) : Prop :=
  ∀ p q r : Path, cp (comp p (comp q r)) (comp (comp p q) r)
def UnitalUpToCp {Path : Type} (cp : Path → Path → Prop)
    (comp : Path → Path → Path) (e : Path) : Prop :=
  ∀ p : Path, cp (comp p e) p ∧ cp (comp e p) p
def SomeNonUnit {Path : Type} (cp : Path → Path → Prop) (e : Path) : Prop :=
  ∃ p : Path, ¬ cp p e

/-- The three names are the three fields, in order and with nothing added. -/
theorem composeConditions_iff_the_three {Path : Type} (cp : Path → Path → Prop)
    (comp : Path → Path → Path) (e : Path) :
    ComposeConditions cp comp e ↔
      (AssociativeUpToCp cp comp ∧ UnitalUpToCp cp comp e ∧ SomeNonUnit cp e) :=
  ⟨fun h => ⟨h.associativeUpToCp, h.unitalUpToCp, h.someNonUnit⟩,
   fun ⟨assoc, unital, nonUnit⟩ => ⟨assoc, unital, nonUnit⟩⟩

/-- **On the nose is up to anything reflexive.** The first condition is free as
soon as `congruentPath` is reflexive and `compose` is strictly associative. The
clause set declares neither, which is why both are hypotheses here and why the
model refuting the condition can leave `congruentPath` as equality and break the
composition instead. -/
theorem strictly_associative_is_associative_up_to_cp {Path : Type}
    {cp : Path → Path → Prop} {comp : Path → Path → Path}
    (refl : ∀ p, cp p p)
    (assoc : ∀ p q r, comp p (comp q r) = comp (comp p q) r) :
    AssociativeUpToCp cp comp := by
  intro p q r
  rw [assoc p q r]
  exact refl _

/-- And the second is free on the same reflexivity and a strict unit. Both
equational conditions are therefore about the pair `(compose, congruentPath)`
and never about either alone. -/
theorem strict_unit_is_unital_up_to_cp {Path : Type}
    {cp : Path → Path → Prop} {comp : Path → Path → Path} {e : Path}
    (refl : ∀ p, cp p p) (unit : ∀ p, comp p e = p ∧ comp e p = p) :
    UnitalUpToCp cp comp e := by
  intro p
  rw [(unit p).1, (unit p).2]
  exact ⟨refl p, refl p⟩

/-- **Refuting the third collapses `congruentPath` to one class.** If nothing is
a non-unit and `cp` is symmetric and transitive, `cp` relates every pair of
paths. So the third condition is free wherever `cp` is a partial equivalence
with two classes --- but `congruentPath_is_not_an_equivalence` shows the three
clauses that mention it leave it neither reflexive nor symmetric nor
transitive, so this says what *would* make the condition free, not what
does. The model refuting it takes the collapse literally and keeps one path. -/
theorem no_non_unit_collapses_cp {Path : Type} {cp : Path → Path → Prop}
    {e : Path} (symm : ∀ p q, cp p q → cp q p)
    (trans : ∀ p q r, cp p q → cp q r → cp p r)
    (h : ∀ p, cp p e) (a b : Path) : cp a b :=
  trans a e b (h a) (symm b e (h b))

/-! Three models follow, one per composition condition. Each satisfies the other
two and refutes its own, and none of them mentions the carrier. -/

namespace NeedsAssociativeUpToCp

/-- Composition that doubles its left argument once both sides are non-units.
Zero stays a unit and nothing else survives: `comp 1 (comp 1 1)` is five where
`comp (comp 1 1) 1` is seven. -/
def comp : Nat → Nat → Nat
  | 0, q => q
  | p + 1, 0 => p + 1
  | p + 1, q + 1 => 2 * (p + 1) + (q + 1)

theorem two_hold_and_composition_is_not_associative :
    UnitalUpToCp (Path := Nat) Eq comp 0 ∧ SomeNonUnit (Path := Nat) Eq 0 ∧
      ¬ AssociativeUpToCp (Path := Nat) Eq comp :=
  ⟨fun p => by cases p <;> exact ⟨rfl, rfl⟩,
   ⟨1, by decide⟩,
   fun h => absurd (h 1 1 1) (by decide)⟩

end NeedsAssociativeUpToCp

namespace NeedsUnitalUpToCp

/-- Addition on the naturals with the unit misdeclared as one. Associativity and
the non-unit are untouched; the unit law fails, and it fails at zero. -/
theorem two_hold_and_the_unit_is_not_a_unit :
    AssociativeUpToCp (Path := Nat) Eq (· + ·) ∧ SomeNonUnit (Path := Nat) Eq 1 ∧
      ¬ UnitalUpToCp (Path := Nat) Eq (· + ·) 1 :=
  ⟨fun p q r => (Nat.add_assoc p q r).symm,
   ⟨0, by decide⟩,
   fun h => absurd (h 0).1 (by decide)⟩

end NeedsUnitalUpToCp

namespace NeedsSomeNonUnit

/-- One path. The other two hold by reflexivity of equality, and there is
nothing left to be a non-unit --- which is the collapse
`no_non_unit_collapses_cp` describes, built rather than derived. -/
theorem two_hold_and_everything_is_the_unit :
    AssociativeUpToCp (Path := Unit) Eq (fun _ _ => ()) ∧
      UnitalUpToCp (Path := Unit) Eq (fun _ _ => ()) () ∧
      ¬ SomeNonUnit (Path := Unit) Eq () :=
  ⟨fun _ _ _ => rfl, fun _ => ⟨rfl, rfl⟩, fun ⟨_, h⟩ => h rfl⟩

end NeedsSomeNonUnit

/-! ### And the five the closing tier adds?

Five clauses, five conditions, and unlike the transfinite tier the two are
not the same proposition written twice: each condition is a *property of a
relation*, and each clause is an *instance* of that property at the arguments
the clause names.  What has to be shown is that none of the five follows from
the other four, and the five models below each satisfy four and refute one.

The carrier is finite, so every statement here is decidable and each model is
settled by computation over it rather than by a hand proof.  The ground sits
at `0` and the image of everything at `1`.  None of the models mentions the
layers beneath, and that is not laziness: the closing tier was closed on its
own, and a condition a layer beneath could break would not have been a
closing clause.

The path condition is stated over a path type the other four do not mention,
so its Prop binds the path type itself.  That is a choice about the reading
and not about the content: a path relation over a two-point type is still a
path relation. -/

/-- No image of anything is congruent to the ground. -/
def FormingIsNotCongruentToGround (Form : Type) (ground : Form)
    (f2f : Form → Form) (C : Form → Form → Prop) : Prop :=
  ∀ x : Form, ¬ C (f2f x) ground

/-- Similarity is reflexive at every point. -/
def SimilarIsReflexive (Form : Type) (S : Form → Form → Prop) : Prop :=
  ∀ x : Form, S x x

/-- Similarity is symmetric at every pair. -/
def SimilarIsSymmetric (Form : Type) (S : Form → Form → Prop) : Prop :=
  ∀ x y : Form, S x y → S y x

/-- Congruence is transitive at every triple. -/
def CongruentIsTransitive (Form : Type) (C : Form → Form → Prop) : Prop :=
  ∀ x y z : Form, C x y → C y z → C x z

/-- The path relation is symmetric at every pair. -/
def CongruentPathIsSymmetric (Path : Type) (cp : Path → Path → Prop) : Prop :=
  ∀ p q : Path, cp p q → cp q p

namespace NeedsFormingIsNotCongruentToGround

/-- Congruence is total, so the image is congruent to the ground and the
denial fails.  Similarity is total, so it is reflexive and symmetric; the
path relation is total, so it is symmetric. -/
def S (_ _ : Fin 2) : Prop := True
def C (_ _ : Fin 2) : Prop := True
def cp (_ _ : Fin 2) : Prop := True
def formImage (_ : Fin 2) : Fin 2 := 1
def groundPoint : Fin 2 := 0

theorem four_hold_and_the_denial_fails :
    ¬ FormingIsNotCongruentToGround (Fin 2) groundPoint formImage C ∧
      SimilarIsReflexive (Fin 2) S ∧
      SimilarIsSymmetric (Fin 2) S ∧
      CongruentIsTransitive (Fin 2) C ∧
      CongruentPathIsSymmetric (Fin 2) cp :=
  by
    simp only [FormingIsNotCongruentToGround, SimilarIsReflexive,
      SimilarIsSymmetric, CongruentIsTransitive, CongruentPathIsSymmetric,
      S, C, cp, formImage, groundPoint]
    decide

end NeedsFormingIsNotCongruentToGround

namespace NeedsSimilarIsReflexive

/-- Similarity is equality except that the point `1` is related to nothing.
It is symmetric and transitive still --- the missing pair is a single
diagonal one --- congruence is equality and so transitive, the path relation
is equality and so symmetric, and congruence does not run from the image back
to the ground, so no image is congruent to the ground. -/
def S (a b : Fin 2) : Prop := a = b ∧ a ≠ 1
def C (a b : Fin 2) : Prop := a = b
def cp (a b : Fin 2) : Prop := a = b
def formImage (_ : Fin 2) : Fin 2 := 1
def groundPoint : Fin 2 := 0

theorem four_hold_and_similarity_is_not_reflexive :
    ¬ SimilarIsReflexive (Fin 2) S ∧
      SimilarIsSymmetric (Fin 2) S ∧
      CongruentIsTransitive (Fin 2) C ∧
      CongruentPathIsSymmetric (Fin 2) cp ∧
      FormingIsNotCongruentToGround (Fin 2) groundPoint formImage C :=
  by
    simp only [FormingIsNotCongruentToGround, SimilarIsReflexive,
      SimilarIsSymmetric, CongruentIsTransitive, CongruentPathIsSymmetric,
      S, C, cp, formImage, groundPoint]
    decide

end NeedsSimilarIsReflexive

namespace NeedsSimilarIsSymmetric

/-- Similarity is equality, widened by one directed arrow: the ground
reaches the image and the image does not reach the ground.  It is reflexive
everywhere, congruence is equality and so transitive, the path relation is
equality and so symmetric, and congruence does not run from the image back to
the ground. -/
def S (a b : Fin 2) : Prop := a = b ∨ (a = 0 ∧ b = 1)
def C (a b : Fin 2) : Prop := a = b
def cp (a b : Fin 2) : Prop := a = b
def formImage (_ : Fin 2) : Fin 2 := 1
def groundPoint : Fin 2 := 0

theorem four_hold_and_similarity_is_not_symmetric :
    ¬ SimilarIsSymmetric (Fin 2) S ∧
      SimilarIsReflexive (Fin 2) S ∧
      CongruentIsTransitive (Fin 2) C ∧
      CongruentPathIsSymmetric (Fin 2) cp ∧
      FormingIsNotCongruentToGround (Fin 2) groundPoint formImage C :=
  by
    simp only [FormingIsNotCongruentToGround, SimilarIsReflexive,
      SimilarIsSymmetric, CongruentIsTransitive, CongruentPathIsSymmetric,
      S, C, cp, formImage, groundPoint]
    decide

end NeedsSimilarIsSymmetric

namespace NeedsCongruentIsTransitive

/-- Congruence is equality, widened by two directed arrows: the ground
reaches one, one reaches two, and the ground does not reach two.  It is
reflexive, and it is symmetric --- the mirror of each added arrow is absent
--- and similarity is total, so it is reflexive and symmetric.  The path
relation is equality, so it is symmetric.  Three points are needed here and
two in the models above, which is the only difference between them. -/
def C (a b : Fin 3) : Prop := a = b ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2)
def S (_ _ : Fin 3) : Prop := True
def cp (a b : Fin 3) : Prop := a = b
def formImage (_ : Fin 3) : Fin 3 := 1
def groundPoint : Fin 3 := 0

theorem four_hold_and_congruence_is_not_transitive :
    ¬ CongruentIsTransitive (Fin 3) C ∧
      SimilarIsReflexive (Fin 3) S ∧
      SimilarIsSymmetric (Fin 3) S ∧
      CongruentPathIsSymmetric (Fin 3) cp ∧
      FormingIsNotCongruentToGround (Fin 3) groundPoint formImage C :=
  by
    simp only [FormingIsNotCongruentToGround, SimilarIsReflexive,
      SimilarIsSymmetric, CongruentIsTransitive, CongruentPathIsSymmetric,
      S, C, cp, formImage, groundPoint]
    decide

end NeedsCongruentIsTransitive

namespace NeedsCongruentPathIsSymmetric

/-- The path relation is equality, widened by one directed arrow: the ground
reaches the image and the image does not reach the ground.  Similarity is
total, congruence is equality, and congruence does not run from the image
back to the ground. -/
def cp (a b : Fin 2) : Prop := a = b ∨ (a = 0 ∧ b = 1)
def S (_ _ : Fin 2) : Prop := True
def C (a b : Fin 2) : Prop := a = b
def formImage (_ : Fin 2) : Fin 2 := 1
def groundPoint : Fin 2 := 0

theorem four_hold_and_path_congruence_is_not_symmetric :
    ¬ CongruentPathIsSymmetric (Fin 2) cp ∧
      SimilarIsReflexive (Fin 2) S ∧
      SimilarIsSymmetric (Fin 2) S ∧
      CongruentIsTransitive (Fin 2) C ∧
      FormingIsNotCongruentToGround (Fin 2) groundPoint formImage C :=
  by
    simp only [FormingIsNotCongruentToGround, SimilarIsReflexive,
      SimilarIsSymmetric, CongruentIsTransitive, CongruentPathIsSymmetric,
      S, C, cp, formImage, groundPoint]
    decide

end NeedsCongruentPathIsSymmetric

/-! ### And the five the transfinite layer adds?

Not five. Two of them are proved outright by conditions already stated, so the
nineteen-condition characterisation is not minimal and no countermodel to either
can exist. The other three are independent of *everything* --- of the eight, of
the operations, of the composition and of each other --- which makes the three
models below the sharpest in the file: each satisfies eighteen conditions and
refutes one. -/

def SomeStartAtGround (S : Form → Form → Prop) (ground : Form) : Prop :=
  ∃ a, S a ground
def SomeEndAtLimit (C : Form → Form → Prop) (ordinalLimit : Form) : Prop :=
  ∃ b, C b ordinalLimit
def LimitAbsorbsTheChain (ground : Form) (f2f : Form → Form)
    (C : Form → Form → Prop) (ordinalLimit : Form) : Prop :=
  ∀ y : Form,
    (∀ n : Nat, Derives f2f C (Nat.repeat f2f n ground) y) → Derives f2f C ordinalLimit y
def LimitNotSimulatedFinitely (ground : Form) (f2f : Form → Form)
    (E : Form → Form → Prop) (ordinalLimit : Form) : Prop :=
  ∀ n : Nat, ¬ E (Nat.repeat f2f n ground) ordinalLimit
def SuccEscapes (f2f : Form → Form) (C E : Form → Form → Prop)
    (ordinalSucc : Form → Form) : Prop :=
  ∀ x : Form, Derives f2f C x (ordinalSucc x) ∧ ¬ E (ordinalSucc x) x

/-- The five names are the five fields, in order and with nothing added. -/
theorem transfiniteConditions_iff_the_five (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) (ordinalLimit : Form)
    (ordinalSucc : Form → Form) :
    TransfiniteConditions ground f2f S C E ordinalLimit ordinalSucc ↔
      (SomeStartAtGround S ground ∧ SomeEndAtLimit C ordinalLimit ∧
        LimitAbsorbsTheChain ground f2f C ordinalLimit ∧
        LimitNotSimulatedFinitely ground f2f E ordinalLimit ∧
        SuccEscapes f2f C E ordinalSucc) :=
  ⟨fun h => ⟨h.someStartAtGround, h.someEndAtLimit, h.limitAbsorbsTheChain,
             h.limitNotSimulatedFinitely, h.succEscapes⟩,
   fun ⟨start, finish, absorbs, notFinite, escapes⟩ =>
     ⟨start, finish, absorbs, notFinite, escapes⟩⟩

/-- **The eight already start at the ground.** `imageSimilarToGround` says every
image is similar to the ground, so the image of the ground is a witness. The
limit is not mentioned, the successor is not mentioned, and nothing is assumed
about where the chain goes: `SomeStartAtGround` holds of every model of the
prefix whatsoever. -/
theorem someStartAtGround_is_implied_by_the_eight {ground : Form}
    {f2f : Form → Form} {S C E : Form → Form → Prop}
    (h : Conditions ground f2f S C E) : SomeStartAtGround S ground :=
  ⟨f2f ground, h.imageSimilarToGround ground⟩

/-- **The operations already end at the limit.** `identityWitness` produces, for
*every* point, something both similar and congruent to it; the second half of
that, read at the limit, is the condition. The asymmetry is the whole content:
the transfinite clause asks for one congruent predecessor of one distinguished
point, and the operation clause hands over one for each point there is. -/
theorem someEndAtLimit_is_implied_by_the_operations {S C : Form → Form → Prop}
    (h : OperationConditions S C) (ordinalLimit : Form) :
    SomeEndAtLimit C ordinalLimit :=
  let ⟨c, _, hc⟩ := h.identityWitness ordinalLimit
  ⟨c, hc⟩

/-- **Nineteen conditions, seventeen of them load-bearing.**
`nineteen_is_not_fourteen_plus_five` showed the transfinite list is not free over
the other fourteen. This shows the list is not minimal either: two of its five
members are theorems of the fourteen, for every limit and every successor at
once. Neither proof looks at where the limit sits, which is why
`spanned_carriers_admit_no_limit` does not obstruct them. That obstruction is
about `limitNotSimulatedFinitely`, and these two are not that. -/
theorem two_of_the_nineteen_are_theorems_of_the_others {ground : Form}
    {f2f : Form → Form} {S C E : Form → Form → Prop}
    (h : Conditions ground f2f S C E) (o : OperationConditions S C)
    (ordinalLimit : Form) :
    SomeStartAtGround S ground ∧ SomeEndAtLimit C ordinalLimit :=
  ⟨someStartAtGround_is_implied_by_the_eight h,
   someEndAtLimit_is_implied_by_the_operations o ordinalLimit⟩

/-- **A limit on the chain absorbs it.** If the limit is a chain point, the
hypothesis at that point *is* the conclusion. So `LimitAbsorbsTheChain` is
already proved wherever the limit is finite, and the model refuting it must put
the limit off the chain --- which is where the transfinite layer wants it
anyway. -/
theorem a_limit_on_the_chain_absorbs_it {ground : Form} {f2f : Form → Form}
    {C : Form → Form → Prop} {ordinalLimit : Form} {n : Nat}
    (hn : ordinalLimit = Nat.repeat f2f n ground) :
    LimitAbsorbsTheChain ground f2f C ordinalLimit := by
  intro _ h
  rw [hn]
  exact h n

/-- **An unreached limit is never simulated finitely.** `simIntoCong` and
`congIntoSim` turn a simulation into a similarity, and a similarity from a chain
point is exactly what `Reach` asks for. So `LimitNotSimulatedFinitely` is free
wherever the limit is out of reach, and a model refuting it must bring the limit
within reach --- which by `congruentDiagonalIsReach` also makes it congruent to
itself. The condition is not about the limit being infinite. It is about the
limit not being *arrived at*. -/
theorem unreached_limits_are_not_simulated_finitely {ground : Form}
    {f2f : Form → Form} {S C E : Form → Form → Prop}
    (h : Conditions ground f2f S C E) {ordinalLimit : Form}
    (hr : ¬ Reach ground f2f S ordinalLimit) :
    LimitNotSimulatedFinitely ground f2f E ordinalLimit :=
  fun n he => hr ⟨n, h.congIntoSim _ _ (h.simIntoCong _ _ he)⟩

/-- **A total congruence and a moving successor escape by themselves.** The
first conjunct asks only that something in the forward orbit be congruent to the
successor, which a total `C` gives at once; the second asks only that the
successor not simulate its argument, which a simulation inside equality gives as
soon as the successor has no fixed point. Refuting `SuccEscapes` therefore needs
either a thin congruence or a successor that stands still, and the model below
takes the second --- the congruence is already pinned by
`congruentDiagonalIsReach` and the successor by nothing at all. -/
theorem a_moving_successor_escapes {f2f : Form → Form}
    {C E : Form → Form → Prop} {ordinalSucc : Form → Form}
    (total : ∀ x y, C x y) (thin : ∀ x y, E x y → x = y)
    (moves : ∀ x, ¬ (ordinalSucc x = x)) :
    SuccEscapes f2f C E ordinalSucc :=
  fun x => ⟨⟨0, total _ _⟩, fun he => moves x (thin _ _ he)⟩

/-- The five with the two that are already proved removed. What is left does
not mention similarity and does not mention a path: `someStartAtGround` was the
only transfinite condition naming `S`, and it was the half of `axLimitDerives`
that the prefix had already proved. -/
structure SharpTransfiniteConditions (ground : Form) (f2f : Form → Form)
    (C E : Form → Form → Prop) (ordinalLimit : Form)
    (ordinalSucc : Form → Form) : Prop where
  limitAbsorbsTheChain : ∀ y : Form,
    (∀ n : Nat, Derives f2f C (Nat.repeat f2f n ground) y) → Derives f2f C ordinalLimit y
  limitNotSimulatedFinitely : ∀ n : Nat, ¬ E (Nat.repeat f2f n ground) ordinalLimit
  succEscapes : ∀ x : Form, Derives f2f C x (ordinalSucc x) ∧ ¬ E (ordinalSucc x) x

/-- **Irredundant is not minimal, at the other end of the list.**
`conditions_iff_six_and_two_implications` sharpened the eight from inside: each
half that came back was a consequence of other fields of the same structure.
This sharpens from outside. The two conditions that go are proved by the prefix
and by the operations, so the biconditional cannot be stated inside
`TransfiniteConditions` at all --- it has to be stated at the joint, where the
proofs of the two dropped conditions live. Seventeen conditions say what
nineteen said. -/
theorem nineteen_iff_seventeen (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) (ordinalLimit : Form)
    (ordinalSucc : Form → Form) {Path : Type} (cp : Path → Path → Prop)
    (comp : Path → Path → Path) (e : Path) :
    (Conditions ground f2f S C E ∧ OperationConditions S C ∧
        ComposeConditions cp comp e ∧
        TransfiniteConditions ground f2f S C E ordinalLimit ordinalSucc) ↔
      (Conditions ground f2f S C E ∧ OperationConditions S C ∧
        ComposeConditions cp comp e ∧
        SharpTransfiniteConditions ground f2f C E ordinalLimit ordinalSucc) := by
  constructor
  · rintro ⟨eight, ops, compose, five⟩
    exact ⟨eight, ops, compose,
      { limitAbsorbsTheChain := five.limitAbsorbsTheChain
        limitNotSimulatedFinitely := five.limitNotSimulatedFinitely
        succEscapes := five.succEscapes }⟩
  · rintro ⟨eight, ops, compose, three⟩
    exact ⟨eight, ops, compose,
      { someStartAtGround := someStartAtGround_is_implied_by_the_eight eight
        someEndAtLimit :=
          someEndAtLimit_is_implied_by_the_operations ops ordinalLimit
        limitAbsorbsTheChain := three.limitAbsorbsTheChain
        limitNotSimulatedFinitely := three.limitNotSimulatedFinitely
        succEscapes := three.succEscapes }⟩

/-- The transfinite clauses with `axLimitDerives` removed. Its two halves are
the two conditions the prefix and the operations already prove, and it was the
only transfinite clause mentioning `S` or a path, so both disappear with it. -/
structure ContentfulTransfiniteAxioms (ground : Form) (f2f : Form → Form)
    (C E : Form → Form → Prop) (deriver ordinalLimit : Form)
    (ordinalSucc : Form → Form) : Prop where
  axDeriverAtLimit : deriver = ordinalLimit
  axLimitIsLimit : ∀ y : Form,
    (∀ n : Nat, Derives f2f C (Nat.repeat f2f n ground) y) → Derives f2f C ordinalLimit y
  axLimitNotFinite : ∀ n : Nat, ¬ E (Nat.repeat f2f n ground) ordinalLimit
  axSuccExtends : ∀ x : Form, Derives f2f C x (ordinalSucc x) ∧ ¬ E (ordinalSucc x) x

/-- **Twenty-eight, not twenty-nine.** `twenty_nine_clauses_carry_the_content`
removed the ten clauses that are definitional. This removes one more that is
not: `axLimitDerives` is a clause about the carrier, and it is still implied by
the clauses of the two layers beneath it.

The mechanism is visible in the docstring of `TransfiniteConditions`, which had
already noticed the first half of it. The clause ties two halves together with a
single path index; pinning the index separates them; and only once they are
separate can each be matched against a clause elsewhere that quantifies where
this one names. `axSim` is `axLimitDerives`'s first half with the binder run
over every point, and `axSeqIdentityR` is its second half with the binder run
over every point --- as are `axSeqIdentityL` and `axCoopIdentity`, which are the
same statement written a second and a third time. A clause whose halves are each
an instance of some other clause carries nothing, and nothing in an incidence
table over symbols can say so, because instantiation leaves the symbols exactly
where they were. -/
theorem twenty_eight_clauses_carry_the_content (x ground ordinalLimit : Form)
    (f2f ordinalSucc : Form → Form) (S C E : Form → Form → Prop)
    {CPath : Type} (cp : CPath → CPath → Prop) (comp : CPath → CPath → CPath)
    (e : CPath) :
    (ContentfulPrefixAxioms ground f2f S C E ∧ OperationAxioms S C ∧
        ComposeAxioms (Form := Form) cp comp e ∧
        ∃ deriver : Form,
          ContentfulTransfiniteAxioms ground f2f C E deriver ordinalLimit
            ordinalSucc)
      ↔ (Conditions ground f2f S C E ∧ OperationConditions S C ∧
          ComposeConditions cp comp e ∧
          TransfiniteConditions ground f2f S C E ordinalLimit ordinalSucc) := by
  have whole := twenty_nine_clauses_carry_the_content x ground ordinalLimit f2f
    ordinalSucc S C E cp comp e
  constructor
  · rintro ⟨prefixClauses, ops, compose, deriver, transfinite⟩
    obtain ⟨b, hb⟩ := someEndAtLimit_is_implied_by_the_operations
      (operationConditions_of_operationAxioms ops) ordinalLimit
    exact whole.mp ⟨prefixClauses, ops, compose,
      ⟨fun _ => f2f ground, fun _ => b, deriver,
       { axDeriverAtLimit := transfinite.axDeriverAtLimit
         axLimitDerives := ⟨(), prefixClauses.axSim ground, hb⟩
         axLimitIsLimit := transfinite.axLimitIsLimit
         axLimitNotFinite := transfinite.axLimitNotFinite
         axSuccExtends := transfinite.axSuccExtends }⟩⟩
  · intro h
    obtain ⟨prefixClauses, ops, compose, _, _, deriver, transfinite⟩ := whole.mpr h
    exact ⟨prefixClauses, ops, compose, deriver,
      { axDeriverAtLimit := transfinite.axDeriverAtLimit
        axLimitIsLimit := transfinite.axLimitIsLimit
        axLimitNotFinite := transfinite.axLimitNotFinite
        axSuccExtends := transfinite.axSuccExtends }⟩

/-- **The reduction, at its sharpest: twenty-eight clauses say seventeen
conditions.** Both halves are already proved, and the composite is what the two
of them were for. It is worth stating on its own line because every number in it
had to be argued down separately: thirty-nine clauses to twenty-nine by removing
the ones that hold of nothing, twenty-nine to twenty-eight by removing the one
whose halves are instances of clauses beneath it, nineteen conditions to
seventeen by removing the two the prefix and the operations already prove.

Nothing here is a definition unfolding. Each step is a theorem with a proof, and
the file keeps the unsharpened forms so that both ends of every step can still be
read. -/
theorem twenty_eight_clauses_are_seventeen_conditions (x ground ordinalLimit : Form)
    (f2f ordinalSucc : Form → Form) (S C E : Form → Form → Prop)
    {CPath : Type} (cp : CPath → CPath → Prop) (comp : CPath → CPath → CPath)
    (e : CPath) :
    (ContentfulPrefixAxioms ground f2f S C E ∧ OperationAxioms S C ∧
        ComposeAxioms (Form := Form) cp comp e ∧
        ∃ deriver : Form,
          ContentfulTransfiniteAxioms ground f2f C E deriver ordinalLimit
            ordinalSucc)
      ↔ (Conditions ground f2f S C E ∧ OperationConditions S C ∧
          ComposeConditions cp comp e ∧
          SharpTransfiniteConditions ground f2f C E ordinalLimit ordinalSucc) :=
  (twenty_eight_clauses_carry_the_content x ground ordinalLimit f2f ordinalSucc
      S C E cp comp e).trans
    (nineteen_iff_seventeen ground f2f S C E ordinalLimit ordinalSucc cp comp e)

/-- **The transfinite layer has an inert binder too.** `axDeriverAtLimit` pins
`deriver` to `ordinalLimit`, and no other clause of the layer mentions `deriver`,
so under the existential that binds it the clause can always be satisfied by
choosing the limit. It is the same phenomenon as
`compose_nonempty_binders_are_inert` one layer up: a binder that no other clause
reads is not a hypothesis, it is a name. What is left is three clauses, and they
are `SharpTransfiniteConditions` character for character. -/
theorem the_deriver_binder_is_inert (ground : Form) (f2f : Form → Form)
    (C E : Form → Form → Prop) (ordinalLimit : Form) (ordinalSucc : Form → Form) :
    (∃ deriver : Form,
        ContentfulTransfiniteAxioms ground f2f C E deriver ordinalLimit ordinalSucc)
      ↔ SharpTransfiniteConditions ground f2f C E ordinalLimit ordinalSucc :=
  ⟨fun ⟨_, h⟩ => ⟨h.axLimitIsLimit, h.axLimitNotFinite, h.axSuccExtends⟩,
   fun h => ⟨ordinalLimit,
     ⟨rfl, h.limitAbsorbsTheChain, h.limitNotSimulatedFinitely, h.succEscapes⟩⟩⟩

/-- The fourteen contentful prefix clauses with the three that
`three_of_the_fourteen_are_derivable` derives removed. The four clauses its proof
consumes --- `filtrationCongSim`, `filtrationSimCong`, `axGroundSubstanceAx` and
`axSim` --- are all still here, which is what makes the removal safe. -/
structure NeededPrefixAxioms (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) : Prop where
  axDiff : ∀ x, ¬ E (f2f x) ground
  axSim : ∀ x, S (f2f x) ground
  axBox : ∀ x, S (f2f (f2f x)) x
  axSyntaxRequiresSubstance : ∀ x, Reach ground f2f S x → C x x
  axSubstanceRequiresSemantics : ∀ x, C x x → E x x
  axSemanticsRequiresSyntax : ∀ x, E x x → Reach ground f2f S x
  axGroundSubstanceAx : C ground ground
  axGroundSemanticsAx : E ground ground
  filtrationSimCong : ∀ x y, E x y → C x y
  filtrationCongSim : ∀ x y, C x y → S x y
  traceLevels : ∀ x, S (f2f x) x ∧ (C (f2f x) x → S (f2f x) x) ∧
    (E (f2f x) x → C (f2f x) x)

/-- **The open question this file left, answered: eleven, not fourteen.**
`three_of_the_fourteen_are_derivable` proved the three derivations and stopped
there, and the docstring of `ContentfulPrefixAxioms` recorded that the list had
never been measured clause by clause. Measuring it is this theorem, and the proof
is the earlier one used in the direction it was always pointing. -/
theorem eleven_prefix_clauses_carry_the_content (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) :
    ContentfulPrefixAxioms ground f2f S C E ↔ NeededPrefixAxioms ground f2f S C E := by
  constructor
  · intro h
    exact { axDiff := h.axDiff
            axSim := h.axSim
            axBox := h.axBox
            axSyntaxRequiresSubstance := h.axSyntaxRequiresSubstance
            axSubstanceRequiresSemantics := h.axSubstanceRequiresSemantics
            axSemanticsRequiresSyntax := h.axSemanticsRequiresSyntax
            axGroundSubstanceAx := h.axGroundSubstanceAx
            axGroundSemanticsAx := h.axGroundSemanticsAx
            filtrationSimCong := h.filtrationSimCong
            filtrationCongSim := h.filtrationCongSim
            traceLevels := h.traceLevels }
  · intro h
    obtain ⟨groundSelf, reachesGround, closesLoop⟩ :=
      three_of_the_fourteen_are_derivable h.filtrationCongSim h.filtrationSimCong
        h.axGroundSubstanceAx h.axSim
    exact { axDiff := h.axDiff
            axSim := h.axSim
            axBox := h.axBox
            axGroundSelf := groundSelf
            axSyntaxRequiresSubstance := h.axSyntaxRequiresSubstance
            axSubstanceRequiresSemantics := h.axSubstanceRequiresSemantics
            axSemanticsRequiresSyntax := h.axSemanticsRequiresSyntax
            axFormClosesLoop := closesLoop
            axGroundSyntaxAx := reachesGround
            axGroundSubstanceAx := h.axGroundSubstanceAx
            axGroundSemanticsAx := h.axGroundSemanticsAx
            filtrationSimCong := h.filtrationSimCong
            filtrationCongSim := h.filtrationCongSim
            traceLevels := h.traceLevels }

/-- Eleven clauses, eight conditions. This is the whole of the remaining distance
between the clause set and the conditions: the other three layers have already
closed it. -/
theorem eleven_prefix_clauses_are_eight_conditions (ground : Form)
    (f2f : Form → Form) (S C E : Form → Form → Prop) :
    NeededPrefixAxioms ground f2f S C E ↔ Conditions ground f2f S C E :=
  ((eleven_prefix_clauses_carry_the_content ground f2f S C E).symm.trans
    (prefix_is_its_fourteen_contentful_clauses ground f2f S C E).symm).trans
      ⟨conditions_of_prefixAxioms, prefixAxioms_of_conditions⟩

/-- The eleven with the two the diagonal cycle proves removed, and `traceLevels`
cut to the one conjunct of its three that is not a filtration clause read at an
image. Six of these nine are fields of `Conditions` character for character. -/
structure SharpPrefixAxioms (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) : Prop where
  axDiff : ∀ x, ¬ E (f2f x) ground
  axSim : ∀ x, S (f2f x) ground
  axBox : ∀ x, S (f2f (f2f x)) x
  axImageSimilar : ∀ x, S (f2f x) x
  axSyntaxRequiresSubstance : ∀ x, Reach ground f2f S x → C x x
  axSubstanceRequiresSemantics : ∀ x, C x x → E x x
  axSemanticsRequiresSyntax : ∀ x, E x x → Reach ground f2f S x
  filtrationSimCong : ∀ x y, E x y → C x y
  filtrationCongSim : ∀ x y, C x y → S x y

/-- **Eleven was not minimal either: nine.** Two of the eleven are the ground at
the diagonal, and the diagonal cycle already reaches it --- `axSim` puts the
ground within reach at one step, `axSyntaxRequiresSubstance` turns that into
`axGroundSubstanceAx`, and `axSubstanceRequiresSemantics` turns that into
`axGroundSemanticsAx`. The third removal is not a clause but two thirds of one:
`traceLevels` states three things, and the second and third are
`filtrationCongSim` and `filtrationSimCong` read at an image. A clause list can
hide a redundancy inside a conjunction as easily as between two clauses. -/
theorem nine_prefix_clauses_carry_the_content (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) :
    NeededPrefixAxioms ground f2f S C E ↔ SharpPrefixAxioms ground f2f S C E := by
  constructor
  · intro h
    exact { axDiff := h.axDiff
            axSim := h.axSim
            axBox := h.axBox
            axImageSimilar := fun x => (h.traceLevels x).1
            axSyntaxRequiresSubstance := h.axSyntaxRequiresSubstance
            axSubstanceRequiresSemantics := h.axSubstanceRequiresSemantics
            axSemanticsRequiresSyntax := h.axSemanticsRequiresSyntax
            filtrationSimCong := h.filtrationSimCong
            filtrationCongSim := h.filtrationCongSim }
  · intro h
    have groundSubstance : C ground ground :=
      h.axSyntaxRequiresSubstance ground ⟨1, h.axSim ground⟩
    exact { axDiff := h.axDiff
            axSim := h.axSim
            axBox := h.axBox
            axSyntaxRequiresSubstance := h.axSyntaxRequiresSubstance
            axSubstanceRequiresSemantics := h.axSubstanceRequiresSemantics
            axSemanticsRequiresSyntax := h.axSemanticsRequiresSyntax
            axGroundSubstanceAx := groundSubstance
            axGroundSemanticsAx :=
              h.axSubstanceRequiresSemantics ground groundSubstance
            filtrationSimCong := h.filtrationSimCong
            filtrationCongSim := h.filtrationCongSim
            traceLevels := fun x =>
              ⟨h.axImageSimilar x, fun hc => h.filtrationCongSim _ _ hc,
               fun he => h.filtrationSimCong _ _ he⟩ }

/-- **The whole gap between the clause set and the conditions, isolated.** Six of
the nine clauses are six of the eight conditions written out identically. What is
left on each side is the diagonal: three implications around a cycle against two
equivalences to the same point. They say the same thing, and this says so with
nothing else in scope --- no ground, no image, no filtration, only the cycle.

That is the entire residue of a reduction that began at thirty-nine clauses. -/
theorem three_implications_are_two_equivalences (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) :
    ((∀ x, Reach ground f2f S x → C x x) ∧ (∀ x, C x x → E x x) ∧
        (∀ x, E x x → Reach ground f2f S x))
      ↔ ((∀ x, C x x ↔ Reach ground f2f S x) ∧
          (∀ x, E x x ↔ Reach ground f2f S x)) := by
  constructor
  · rintro ⟨reachCong, congSim, simReach⟩
    exact ⟨fun x => ⟨fun hc => simReach x (congSim x hc), reachCong x⟩,
      fun x => ⟨simReach x, fun hr => congSim x (reachCong x hr)⟩⟩
  · rintro ⟨congIff, simIff⟩
    exact ⟨fun x => (congIff x).mpr, fun x hc => (simIff x).mpr ((congIff x).mp hc),
      fun x => (simIff x).mp⟩

/-- Nine clauses, eight conditions. -/
theorem nine_prefix_clauses_are_eight_conditions (ground : Form)
    (f2f : Form → Form) (S C E : Form → Form → Prop) :
    SharpPrefixAxioms ground f2f S C E ↔ Conditions ground f2f S C E :=
  (nine_prefix_clauses_carry_the_content ground f2f S C E).symm.trans
    (eleven_prefix_clauses_are_eight_conditions ground f2f S C E)

/-- The six prefix clauses that are fields of `Conditions` written out
identically. Split off so that the three that are not can be handled on their
own. -/
structure SixSharedClauses (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) : Prop where
  axDiff : ∀ x, ¬ E (f2f x) ground
  axSim : ∀ x, S (f2f x) ground
  axBox : ∀ x, S (f2f (f2f x)) x
  axImageSimilar : ∀ x, S (f2f x) x
  filtrationSimCong : ∀ x y, E x y → C x y
  filtrationCongSim : ∀ x y, C x y → S x y

/-- **Nine is six and a cycle.** The prose claim, as a theorem. -/
theorem nine_is_six_and_a_cycle (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) :
    SharpPrefixAxioms ground f2f S C E ↔
      (SixSharedClauses ground f2f S C E ∧
        (∀ x, Reach ground f2f S x → C x x) ∧ (∀ x, C x x → E x x) ∧
        (∀ x, E x x → Reach ground f2f S x)) := by
  constructor
  · intro h
    exact ⟨{ axDiff := h.axDiff
             axSim := h.axSim
             axBox := h.axBox
             axImageSimilar := h.axImageSimilar
             filtrationSimCong := h.filtrationSimCong
             filtrationCongSim := h.filtrationCongSim },
      h.axSyntaxRequiresSubstance, h.axSubstanceRequiresSemantics,
      h.axSemanticsRequiresSyntax⟩
  · rintro ⟨six, reachCong, congSim, simReach⟩
    exact { axDiff := six.axDiff
            axSim := six.axSim
            axBox := six.axBox
            axImageSimilar := six.axImageSimilar
            axSyntaxRequiresSubstance := reachCong
            axSubstanceRequiresSemantics := congSim
            axSemanticsRequiresSyntax := simReach
            filtrationSimCong := six.filtrationSimCong
            filtrationCongSim := six.filtrationCongSim }

/-! Three models follow, one per arrow of the diagonal cycle. Each satisfies the
six shared clauses and the two arrows that are not its own. The first two need no
carrier at all: read every relation as a constant and the cycle breaks wherever
the constants disagree. Only the third has to be built, because breaking the
arrow back to reach means having somewhere reach does not go. -/

namespace DropsReachIntoCongruent

/-- Everything is similar, nothing is congruent, nothing is equal. -/
abbrev S : Form → Form → Prop := fun _ _ => True
abbrev C : Form → Form → Prop := fun _ _ => False

theorem six_hold_and_reach_does_not_reach_congruence (ground : Form)
    (f2f : Form → Form) :
    SixSharedClauses ground f2f S C C ∧
      (∀ x : Form, C x x → C x x) ∧
      (∀ x : Form, C x x → Reach ground f2f S x) ∧
      ¬ (∀ x : Form, Reach ground f2f S x → C x x) :=
  ⟨{ axDiff := fun _ h => h
     axSim := fun _ => trivial
     axBox := fun _ => trivial
     axImageSimilar := fun _ => trivial
     filtrationSimCong := fun _ _ h => h
     filtrationCongSim := fun _ _ _ => trivial },
   fun _ h => h, fun _ h => h.elim, fun h => h ground ⟨0, trivial⟩⟩

end DropsReachIntoCongruent

namespace DropsCongruentIntoSimulation

/-- Everything is similar and congruent, nothing is equal. -/
abbrev S : Form → Form → Prop := fun _ _ => True
abbrev E : Form → Form → Prop := fun _ _ => False

theorem six_hold_and_congruence_does_not_reach_equality (ground : Form)
    (f2f : Form → Form) :
    SixSharedClauses ground f2f S S E ∧
      (∀ x : Form, Reach ground f2f S x → S x x) ∧
      (∀ x : Form, E x x → Reach ground f2f S x) ∧
      ¬ (∀ x : Form, S x x → E x x) :=
  ⟨{ axDiff := fun _ h => h
     axSim := fun _ => trivial
     axBox := fun _ => trivial
     axImageSimilar := fun _ => trivial
     filtrationSimCong := fun _ _ _ => trivial
     filtrationCongSim := fun _ _ _ => trivial },
   fun _ _ => trivial, fun _ h => h.elim, fun h => h ground trivial⟩

end DropsCongruentIntoSimulation

namespace DropsSimulationIntoReach

/-- Similarity holds between any two chain points, and the adjoined point is
similar only to itself and to the ground. So the adjoined point is equal to
itself and congruent to itself, and reach never arrives there. -/
def S : Extended → Extended → Prop
  | none, y => y = none ∨ y = extGround
  | some _, y => y ≠ none

theorem self_similar (x : Extended) : S x x := by
  cases x <;> simp [S]

theorem reach_is_someness (y : Extended) :
    Reach extGround extStep S y ↔ y ≠ none := by
  constructor
  · rintro ⟨n, hn⟩
    rw [ext_repeat] at hn
    simpa [S] using hn
  · intro h
    exact ⟨0, by rw [ext_repeat]; simpa [S] using h⟩

theorem six_hold_and_equality_does_not_reach_back :
    SixSharedClauses extGround extStep S S Eq ∧
      (∀ x, Reach extGround extStep S x → S x x) ∧
      (∀ x, S x x → x = x) ∧
      ¬ (∀ x, x = x → Reach extGround extStep S x) :=
  ⟨{ axDiff := by intro x; cases x <;> simp [extStep, extGround]
     axSim := by intro x; cases x <;> simp [S, extStep, extGround]
     axBox := by intro x; cases x <;> simp [S, extStep]
     axImageSimilar := by intro x; cases x <;> simp [S, extStep]
     filtrationSimCong := by rintro x _ rfl; exact self_similar x
     filtrationCongSim := fun _ _ h => h },
   fun x _ => self_similar x, fun _ _ => rfl,
   fun h => (reach_is_someness none).mp (h none rfl) rfl⟩

end DropsSimulationIntoReach

/-- **Twenty clauses, seventeen conditions --- and the whole reduction is the
prefix layer.** Three of the four conjuncts are the same list on both sides,
because each of those layers turned out to *be* its conditions once its
non-content was removed: the operations were four copies over three statements
(`operationAxioms_iff_conditions`), the composition was three statements with two
inert binders (`composeAxioms_iff_conditions`), and the transfinite layer was
three statements with one inert binder and one clause implied from beneath
(`the_deriver_binder_is_inert`, `twenty_eight_clauses_carry_the_content`).

That the composite reduces to `eleven_prefix_clauses_are_eight_conditions` is not
a defect of the statement, it is the result. Thirty-nine clauses became seventeen
conditions, and after the bookkeeping is done the only layer where a clause still
says something a condition does not is the first one. -/
theorem twenty_clauses_are_seventeen_conditions (ground ordinalLimit : Form)
    (f2f ordinalSucc : Form → Form) (S C E : Form → Form → Prop)
    {CPath : Type} (cp : CPath → CPath → Prop) (comp : CPath → CPath → CPath)
    (e : CPath) :
    (NeededPrefixAxioms ground f2f S C E ∧ OperationConditions S C ∧
        ComposeAxioms (Form := Form) cp comp e ∧
        SharpTransfiniteConditions ground f2f C E ordinalLimit ordinalSucc)
      ↔ (Conditions ground f2f S C E ∧ OperationConditions S C ∧
          ComposeConditions cp comp e ∧
          SharpTransfiniteConditions ground f2f C E ordinalLimit ordinalSucc) := by
  constructor
  · rintro ⟨eleven, ops, compose, three⟩
    exact ⟨(eleven_prefix_clauses_are_eight_conditions ground f2f S C E).mp eleven,
      ops, (composeAxioms_iff_conditions ground cp comp e).mp compose, three⟩
  · rintro ⟨eight, ops, compose, three⟩
    exact ⟨(eleven_prefix_clauses_are_eight_conditions ground f2f S C E).mpr eight,
      ops, (composeAxioms_iff_conditions ground cp comp e).mpr compose, three⟩

/-- **Eighteen clauses, seventeen conditions.** The end of this line of work.
Thirty-nine clauses became twenty-nine by removing what the reading defines,
twenty by removing what other clauses prove, and eighteen by removing what the
diagonal cycle proves. What separates eighteen from seventeen is
`three_implications_are_two_equivalences` and nothing else. -/
theorem eighteen_clauses_are_seventeen_conditions (ground ordinalLimit : Form)
    (f2f ordinalSucc : Form → Form) (S C E : Form → Form → Prop)
    {CPath : Type} (cp : CPath → CPath → Prop) (comp : CPath → CPath → CPath)
    (e : CPath) :
    (SharpPrefixAxioms ground f2f S C E ∧ OperationConditions S C ∧
        ComposeAxioms (Form := Form) cp comp e ∧
        SharpTransfiniteConditions ground f2f C E ordinalLimit ordinalSucc)
      ↔ (Conditions ground f2f S C E ∧ OperationConditions S C ∧
          ComposeConditions cp comp e ∧
          SharpTransfiniteConditions ground f2f C E ordinalLimit ordinalSucc) := by
  constructor
  · rintro ⟨nine, ops, compose, three⟩
    exact ⟨(nine_prefix_clauses_are_eight_conditions ground f2f S C E).mp nine,
      ops, (composeAxioms_iff_conditions ground cp comp e).mp compose, three⟩
  · rintro ⟨eight, ops, compose, three⟩
    exact ⟨(nine_prefix_clauses_are_eight_conditions ground f2f S C E).mpr eight,
      ops, (composeAxioms_iff_conditions ground cp comp e).mpr compose, three⟩

/-! Three models follow, one per transfinite condition that has one. Each
satisfies the eight, the three operations, the three composition conditions and
the other four transfinite conditions, and refutes its own --- eighteen against
one, which no earlier model in this file manages. -/

namespace NeedsLimitAbsorbsTheChain

/-- Similarity is total and simulation is equality, as in `LimitAdjoined`.
Congruence is what changes: every chain point is congruent to everything, and
the limit is congruent only to itself and to the successor it is given. That is
the least the other conditions leave room for --- `succEscapes` needs the limit
to derive its own successor --- and it is already too little to absorb the
chain. -/
def C : Extended → Extended → Prop
  | none, y => y = none ∨ y = some 1
  | some _, _ => True

/-- The successor cannot send the limit to the ground here, because the ground
is what the limit has to fail to derive. It sends it one place further on. -/
def succ : Extended → Extended
  | some n => some (n + 1)
  | none => some 1

theorem succ_moves (x : Extended) : ¬ (succ x = x) := by
  cases x <;> simp [succ]

theorem creflexive (x : Extended) : C x x := by
  cases x <;> simp [C]

theorem repeat_none (m : Nat) : Nat.repeat extStep m none = none := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [Nat.repeat, ih, extStep]

theorem limit_does_not_derive_the_ground :
    ¬ Derives extStep C none extGround := by
  rintro ⟨m, hm⟩
  rw [repeat_none] at hm
  simp [C, extGround] at hm

theorem conditions :
    Conditions extGround extStep LimitAdjoined.S C Eq where
  simIntoCong x _ h := by cases h; exact creflexive x
  congIntoSim _ _ _ := trivial
  imageSimilar _ := trivial
  imageSimilarToGround _ := trivial
  doubleImageSimilar _ := trivial
  imageNotSimulatingGround x := LimitAdjoined.step_never_ground x
  congruentDiagonalIsReach x := ⟨fun _ => ⟨0, trivial⟩, fun _ => creflexive x⟩
  simulationDiagonalIsReach _ := ⟨fun _ => ⟨0, trivial⟩, fun _ => rfl⟩

theorem operation_conditions : OperationConditions LimitAdjoined.S C where
  pairedWitnesses _ _ :=
    ⟨extGround, extGround, trivial, trivial, trivial, trivial, trivial⟩
  identityWitness _ := ⟨extGround, trivial, trivial⟩
  apartWitnesses _ _ _ :=
    ⟨none, extGround, trivial, trivial, trivial, trivial, by
      simp [C, extGround]⟩

theorem eighteen_hold_and_the_limit_does_not_absorb_the_chain :
    Conditions extGround extStep LimitAdjoined.S C Eq ∧
      OperationConditions LimitAdjoined.S C ∧
      ComposeConditions (Path := Nat) Eq (· + ·) 0 ∧
      SomeStartAtGround LimitAdjoined.S extGround ∧
      SomeEndAtLimit C none ∧
      LimitNotSimulatedFinitely extGround extStep Eq none ∧
      SuccEscapes extStep C Eq succ ∧
      ¬ LimitAbsorbsTheChain extGround extStep C none :=
  ⟨conditions, operation_conditions, compose_conditions_are_always_available,
   ⟨extGround, trivial⟩, ⟨extGround, trivial⟩,
   fun n => by rw [ext_repeat]; exact fun h => Option.noConfusion h,
   fun x => ⟨⟨0, by cases x <;> simp [Nat.repeat, C, succ]⟩, succ_moves x⟩,
   fun h => limit_does_not_derive_the_ground
     (h extGround (fun n => ⟨0, by simp [Nat.repeat, ext_repeat, C]⟩))⟩

end NeedsLimitAbsorbsTheChain

namespace NeedsLimitNotSimulatedFinitely

/-- Similarity and congruence are total, as in `LimitAdjoined`. Simulation is
equality with one pair added: the ground simulates the limit. One pair at one
point is the smallest refutation there is, and it costs exactly one thing ---
the successor can no longer send the limit back to the ground, because
`imageNotSimulatingGround` denies simulation of the ground by any image. -/
def E (x y : Extended) : Prop := x = y ∨ (x = extGround ∧ y = none)

def succ : Extended → Extended
  | some n => some (n + 1)
  | none => some 1

theorem succ_moves (x : Extended) : ¬ (succ x = x) := by
  cases x <;> simp [succ]

theorem succ_never_ground (x : Extended) : ¬ (succ x = extGround) := by
  cases x <;> simp [succ, extGround]

theorem conditions :
    Conditions extGround extStep LimitAdjoined.S LimitAdjoined.C E where
  simIntoCong _ _ _ := trivial
  congIntoSim _ _ _ := trivial
  imageSimilar _ := trivial
  imageSimilarToGround _ := trivial
  doubleImageSimilar _ := trivial
  imageNotSimulatingGround x := by
    rintro (h | ⟨h, -⟩) <;> exact LimitAdjoined.step_never_ground x h
  congruentDiagonalIsReach _ := ⟨fun _ => ⟨0, trivial⟩, fun _ => trivial⟩
  simulationDiagonalIsReach _ := ⟨fun _ => ⟨0, trivial⟩, fun _ => Or.inl rfl⟩

theorem eighteen_hold_and_a_chain_point_simulates_the_limit :
    Conditions extGround extStep LimitAdjoined.S LimitAdjoined.C E ∧
      OperationConditions LimitAdjoined.S LimitAdjoined.C ∧
      ComposeConditions (Path := Nat) Eq (· + ·) 0 ∧
      SomeStartAtGround LimitAdjoined.S extGround ∧
      SomeEndAtLimit LimitAdjoined.C none ∧
      LimitAbsorbsTheChain extGround extStep LimitAdjoined.C none ∧
      SuccEscapes extStep LimitAdjoined.C E succ ∧
      ¬ LimitNotSimulatedFinitely extGround extStep E none :=
  ⟨conditions, LimitAdjoined.operation_conditions_hold,
   compose_conditions_are_always_available,
   ⟨extGround, trivial⟩, ⟨extGround, trivial⟩, fun _ _ => ⟨0, trivial⟩,
   fun x => ⟨⟨0, trivial⟩, by
     rintro (h | ⟨h, -⟩)
     · exact succ_moves x h
     · exact succ_never_ground x h⟩,
   fun h => h 0 (Or.inr ⟨rfl, rfl⟩)⟩

end NeedsLimitNotSimulatedFinitely

namespace NeedsSuccEscapes

/-- `LimitAdjoined` exactly, with the successor asked to stand still. Nothing
else has to change and nothing else can: no other transfinite condition mentions
the successor, and the eight and the operations do not know it exists. So this
model is the eighteen others with `id` written in one slot, and it is the
cheapest refutation in the file for the same reason the composition models were
cheap --- the symbol it breaks is incident to one clause. -/
theorem eighteen_hold_and_the_successor_stands_still :
    Conditions extGround extStep LimitAdjoined.S LimitAdjoined.C Eq ∧
      OperationConditions LimitAdjoined.S LimitAdjoined.C ∧
      ComposeConditions (Path := Nat) Eq (· + ·) 0 ∧
      SomeStartAtGround LimitAdjoined.S extGround ∧
      SomeEndAtLimit LimitAdjoined.C none ∧
      LimitAbsorbsTheChain extGround extStep LimitAdjoined.C none ∧
      LimitNotSimulatedFinitely extGround extStep Eq none ∧
      ¬ SuccEscapes extStep LimitAdjoined.C Eq id :=
  ⟨LimitAdjoined.conditions_hold, LimitAdjoined.operation_conditions_hold,
   compose_conditions_are_always_available,
   LimitAdjoined.transfinite_conditions_hold.someStartAtGround,
   LimitAdjoined.transfinite_conditions_hold.someEndAtLimit,
   LimitAdjoined.transfinite_conditions_hold.limitAbsorbsTheChain,
   LimitAdjoined.transfinite_conditions_hold.limitNotSimulatedFinitely,
   fun h => (h extGround).2 rfl⟩

end NeedsSuccEscapes

/-! ### What the count is relative to

Every count in this file has been a count of fields, and a field is a unit of
writing rather than a unit of content. Two of the eighteen clauses and two of
the seventeen conditions are conjunctions, so the two sides have been compared
in a form that is not normal --- and the note's own rule says to split a
conjunctive clause before counting it.

The rule cannot be *always split*, because it is not always possible. A
conjunction under a `∀` comes apart and a conjunction under an `∃` does not, and
both halves are stated here: the first as two biconditionals, the second as a
model. `TransfiniteConditions` already found the second from the other side ---
`axLimitDerives` separated into two conditions only once its witness was pinned
--- so what is added is the converse, that while the witness stands the halves
cannot be read apart.

Splitting what splits gives twenty clauses and nineteen conditions. The counts
move and their difference does not: the triangle against the hub is still the
whole residue. -/

/-- **A conjunction under a `∀` comes apart.** The composition unit is two
clauses. -/
theorem the_unit_clause_is_two {Path : Type} (cp : Path → Path → Prop)
    (comp : Path → Path → Path) (e : Path) :
    (∀ p : Path, cp (comp p e) p ∧ cp (comp e p) p) ↔
      ((∀ p : Path, cp (comp p e) p) ∧ (∀ p : Path, cp (comp e p) p)) :=
  ⟨fun h => ⟨fun p => (h p).1, fun p => (h p).2⟩, fun h p => ⟨h.1 p, h.2 p⟩⟩

/-- The successor clause is two: the successor is derived, and the successor is
not equal to what it succeeds. Nothing ties the halves together. -/
theorem the_successor_clause_is_two (f2f : Form → Form)
    (C E : Form → Form → Prop) (ordinalSucc : Form → Form) :
    (∀ x : Form, Derives f2f C x (ordinalSucc x) ∧ ¬ E (ordinalSucc x) x) ↔
      ((∀ x : Form, Derives f2f C x (ordinalSucc x)) ∧
        (∀ x : Form, ¬ E (ordinalSucc x) x)) :=
  ⟨fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩, fun h x => ⟨h.1 x, h.2 x⟩⟩

namespace WitnessConjunctionDoesNotSplit

/-- **A conjunction under an `∃` does not come apart.** Read similarity as
holding only of one point and congruence only of the other. Then everything has
something similar to it and something congruent to it, and nothing at all is
both --- which is the shape of `identityWitness`, and of the other two operation
conditions. Their conjunctions are not two clauses and no convention can make
them two. -/
abbrev S : Bool → Bool → Prop := fun c _ => c = true
abbrev C : Bool → Bool → Prop := fun c _ => c = false

theorem the_halves_hold_and_the_clause_fails :
    ((∀ a : Bool, ∃ c, S c a) ∧ (∀ a : Bool, ∃ c, C c a)) ∧
      ¬ (∀ a : Bool, ∃ c, S c a ∧ C c a) :=
  ⟨⟨fun _ => ⟨true, rfl⟩, fun _ => ⟨false, rfl⟩⟩,
   fun h =>
     match h true with
     | ⟨_, hs, hc⟩ => Bool.noConfusion (hc.symm.trans hs)⟩

end WitnessConjunctionDoesNotSplit

/-- `ComposeAxioms` with its one splittable conjunction split. -/
structure SplitComposeAxioms {Path : Type} (cp : Path → Path → Prop)
    (comp : Path → Path → Path) (e : Path) : Prop where
  axComposeAssoc : ∀ p q r : Path, cp (comp p (comp q r)) (comp (comp p q) r)
  axComposeIdentityR : ∀ p : Path, cp (comp p e) p
  axComposeIdentityL : ∀ p : Path, cp (comp e p) p
  axComposeNonempty : Form → Form → ∃ p : Path, ¬ cp p e

/-- `ComposeConditions` with the same conjunction split. -/
structure SplitComposeConditions {Path : Type} (cp : Path → Path → Prop)
    (comp : Path → Path → Path) (e : Path) : Prop where
  associativeUpToCp : ∀ p q r : Path, cp (comp p (comp q r)) (comp (comp p q) r)
  unitalOnTheRight : ∀ p : Path, cp (comp p e) p
  unitalOnTheLeft : ∀ p : Path, cp (comp e p) p
  someNonUnit : ∃ p : Path, ¬ cp p e

/-- Four clauses, four conditions, and the two inert binders still inert. -/
theorem splitComposeAxioms_iff_conditions (ground : Form) {Path : Type}
    (cp : Path → Path → Prop) (comp : Path → Path → Path) (e : Path) :
    SplitComposeAxioms (Form := Form) cp comp e ↔ SplitComposeConditions cp comp e :=
  ⟨fun h => ⟨h.axComposeAssoc, h.axComposeIdentityR, h.axComposeIdentityL,
      h.axComposeNonempty ground ground⟩,
   fun h => ⟨h.associativeUpToCp, h.unitalOnTheRight, h.unitalOnTheLeft,
      fun _ _ => h.someNonUnit⟩⟩

/-- The composition layer is four in normal form, not three. -/
theorem compose_is_four_split_conditions {Path : Type} (cp : Path → Path → Prop)
    (comp : Path → Path → Path) (e : Path) :
    ComposeConditions cp comp e ↔ SplitComposeConditions cp comp e :=
  ⟨fun h => ⟨h.associativeUpToCp, fun p => (h.unitalUpToCp p).1,
      fun p => (h.unitalUpToCp p).2, h.someNonUnit⟩,
   fun h => ⟨h.associativeUpToCp,
      fun p => ⟨h.unitalOnTheRight p, h.unitalOnTheLeft p⟩, h.someNonUnit⟩⟩

/-- `SharpTransfiniteConditions` with its one conjunction split. -/
structure SplitTransfiniteConditions (ground : Form) (f2f : Form → Form)
    (C E : Form → Form → Prop) (ordinalLimit : Form)
    (ordinalSucc : Form → Form) : Prop where
  limitAbsorbsTheChain : ∀ y : Form,
    (∀ n : Nat, Derives f2f C (Nat.repeat f2f n ground) y) → Derives f2f C ordinalLimit y
  limitNotSimulatedFinitely : ∀ n : Nat, ¬ E (Nat.repeat f2f n ground) ordinalLimit
  succIsDerived : ∀ x : Form, Derives f2f C x (ordinalSucc x)
  succIsNotSimulated : ∀ x : Form, ¬ E (ordinalSucc x) x

/-- The transfinite layer is four in normal form, not three. -/
theorem sharp_transfinite_is_four_split_conditions (ground : Form)
    (f2f : Form → Form) (C E : Form → Form → Prop) (ordinalLimit : Form)
    (ordinalSucc : Form → Form) :
    SharpTransfiniteConditions ground f2f C E ordinalLimit ordinalSucc ↔
      SplitTransfiniteConditions ground f2f C E ordinalLimit ordinalSucc :=
  ⟨fun h => ⟨h.limitAbsorbsTheChain, h.limitNotSimulatedFinitely,
      fun x => (h.succEscapes x).1, fun x => (h.succEscapes x).2⟩,
   fun h => ⟨h.limitAbsorbsTheChain, h.limitNotSimulatedFinitely,
      fun x => ⟨h.succIsDerived x, h.succIsNotSimulated x⟩⟩⟩

/-- **Twenty clauses, nineteen conditions --- the same statement as
`eighteen_clauses_are_seventeen_conditions`, counted in normal form.** Both
sides gain two, the prefix layer gains none because none of its nine is a
conjunction, and the operations gain none because theirs cannot be split at all.
The difference stays at one, and it is still the diagonal written as a triangle
on the left and as a hub on the right. -/
theorem twenty_split_clauses_are_nineteen_split_conditions (ground ordinalLimit : Form)
    (f2f ordinalSucc : Form → Form) (S C E : Form → Form → Prop)
    {CPath : Type} (cp : CPath → CPath → Prop) (comp : CPath → CPath → CPath)
    (e : CPath) :
    (SharpPrefixAxioms ground f2f S C E ∧ OperationConditions S C ∧
        SplitComposeAxioms (Form := Form) cp comp e ∧
        SplitTransfiniteConditions ground f2f C E ordinalLimit ordinalSucc)
      ↔ (Conditions ground f2f S C E ∧ OperationConditions S C ∧
          SplitComposeConditions cp comp e ∧
          SplitTransfiniteConditions ground f2f C E ordinalLimit ordinalSucc) := by
  constructor
  · rintro ⟨nine, ops, compose, four⟩
    exact ⟨(nine_prefix_clauses_are_eight_conditions ground f2f S C E).mp nine,
      ops, (splitComposeAxioms_iff_conditions ground cp comp e).mp compose, four⟩
  · rintro ⟨eight, ops, compose, four⟩
    exact ⟨(nine_prefix_clauses_are_eight_conditions ground f2f S C E).mpr eight,
      ops, (splitComposeAxioms_iff_conditions ground cp comp e).mpr compose, four⟩

/-! ### Splitting a conjunction claims a condition, and two of the splits never said so

`compose_is_four_split_conditions` and `sharp_transfinite_is_four_split_conditions`
each state a count --- four in normal form rather than three --- and a count is a
measurement only once every member has a model that drops it. The member a split
introduces is the one most at risk of not being a member at all:
`WitnessConjunctionDoesNotSplit` is this file's own proof that a conjunction can
fail to be two clauses, so a conjunction *is* two only when neither half implies
the other.

Two of the four splits in this file already answer that.
`NeedsSimulationDiagonalIsReach.the_rising_half_is_not_derivable` and
`NeedsCongruentDiagonalIsReach.the_descending_half_is_not_derivable` answer it for
the sharp split, and `no_two_of_the_triangle_suffice` answers it for the prefix
arrows. The composition split and the transfinite split had the count and not the
models: `NeedsUnitalUpToCp` drops the conjunction, and `NeedsSuccEscapes` drops
the conjunction, and neither says anything about the halves.

The two theorems below are stated over the conditions of their own layer that the
split does not touch. They do not claim the halves are independent over the eight
prefix conditions as well --- nothing here shows that, and the two models below
are not models of the eight. -/

def UnitalOnTheRight {Path : Type} (cp : Path → Path → Prop)
    (comp : Path → Path → Path) (e : Path) : Prop :=
  ∀ p : Path, cp (comp p e) p
def UnitalOnTheLeft {Path : Type} (cp : Path → Path → Prop)
    (comp : Path → Path → Path) (e : Path) : Prop :=
  ∀ p : Path, cp (comp e p) p

/-- The two names are the two fields of the split, in order and with nothing
added. -/
theorem unitalUpToCp_iff_the_two_halves {Path : Type} (cp : Path → Path → Prop)
    (comp : Path → Path → Path) (e : Path) :
    UnitalUpToCp cp comp e ↔ (UnitalOnTheRight cp comp e ∧ UnitalOnTheLeft cp comp e) :=
  ⟨fun h => ⟨fun p => (h p).1, fun p => (h p).2⟩,
   fun h p => ⟨h.1 p, h.2 p⟩⟩

namespace TheUnitalHalvesAreTwo

/-- Composition that keeps its left argument. It is strictly associative, `false`
is a unit on the right of everything, and it is a unit on the left of nothing but
itself. -/
def keepLeft (p _ : Bool) : Bool := p

/-- The mirror: composition that keeps its right argument. -/
def keepRight (_ q : Bool) : Bool := q

theorem keepLeft_associative : AssociativeUpToCp (Path := Bool) Eq keepLeft :=
  fun _ _ _ => rfl

theorem keepRight_associative : AssociativeUpToCp (Path := Bool) Eq keepRight :=
  fun _ _ _ => rfl

theorem some_non_unit : SomeNonUnit (Path := Bool) Eq false :=
  ⟨true, fun h => Bool.noConfusion h⟩

theorem keepLeft_is_unital_on_the_right :
    UnitalOnTheRight (Path := Bool) Eq keepLeft false := fun _ => rfl

theorem keepLeft_is_not_unital_on_the_left :
    ¬ UnitalOnTheLeft (Path := Bool) Eq keepLeft false :=
  fun h => Bool.noConfusion (h true)

theorem keepRight_is_unital_on_the_left :
    UnitalOnTheLeft (Path := Bool) Eq keepRight false := fun _ => rfl

theorem keepRight_is_not_unital_on_the_right :
    ¬ UnitalOnTheRight (Path := Bool) Eq keepRight false :=
  fun h => Bool.noConfusion (h true)

/-- **Neither unital half implies the other.** Both models are strictly
associative and both have a non-unit, so the two conditions the split leaves
alone are held fixed and the only thing that moves is which side the unit is a
unit on. `compose_is_four_split_conditions` is therefore a count: the composition
layer is four in normal form, and the fourth is not the third. -/
theorem neither_unital_half_implies_the_other :
    (AssociativeUpToCp (Path := Bool) Eq keepLeft ∧ SomeNonUnit (Path := Bool) Eq false
        ∧ UnitalOnTheRight (Path := Bool) Eq keepLeft false
        ∧ ¬ UnitalOnTheLeft (Path := Bool) Eq keepLeft false)
      ∧ (AssociativeUpToCp (Path := Bool) Eq keepRight
        ∧ SomeNonUnit (Path := Bool) Eq false
        ∧ UnitalOnTheLeft (Path := Bool) Eq keepRight false
        ∧ ¬ UnitalOnTheRight (Path := Bool) Eq keepRight false) :=
  ⟨⟨keepLeft_associative, some_non_unit, keepLeft_is_unital_on_the_right,
    keepLeft_is_not_unital_on_the_left⟩,
   ⟨keepRight_associative, some_non_unit, keepRight_is_unital_on_the_left,
    keepRight_is_not_unital_on_the_right⟩⟩

end TheUnitalHalvesAreTwo

def SuccIsDerived (f2f : Form → Form) (C : Form → Form → Prop)
    (ordinalSucc : Form → Form) : Prop :=
  ∀ x : Form, Derives f2f C x (ordinalSucc x)
def SuccIsNotSimulated (E : Form → Form → Prop)
    (ordinalSucc : Form → Form) : Prop :=
  ∀ x : Form, ¬ E (ordinalSucc x) x

/-- The two names are the two fields of the split, in order and with nothing
added. -/
theorem succEscapes_iff_the_two_halves (f2f : Form → Form)
    (C E : Form → Form → Prop) (ordinalSucc : Form → Form) :
    SuccEscapes f2f C E ordinalSucc ↔
      (SuccIsDerived f2f C ordinalSucc ∧ SuccIsNotSimulated E ordinalSucc) :=
  ⟨fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩,
   fun h x => ⟨h.1 x, h.2 x⟩⟩

namespace TheSuccHalvesAreTwo

/-- Congruence total, and simulation holding at exactly one pair: the ground's
own successor simulates the ground. One pair is all it takes, and it is the pair
the second half forbids. -/
def C (_ _ : Nat) : Prop := True
def E (a b : Nat) : Prop := a = 1 ∧ b = 0

/-- Congruence and simulation both empty. Nothing derives anything, so the first
half fails everywhere while the second holds for the same reason. -/
def empty (_ _ : Nat) : Prop := False

theorem total_absorbs : LimitAbsorbsTheChain (Form := Nat) 0 Nat.succ C 1 :=
  fun _ _ => ⟨0, trivial⟩

theorem one_pair_is_not_finite :
    LimitNotSimulatedFinitely (Form := Nat) 0 Nat.succ E 1 :=
  fun _ h => Nat.noConfusion h.2

theorem total_derives_the_successor :
    SuccIsDerived (Form := Nat) Nat.succ C Nat.succ := fun _ => ⟨0, trivial⟩

theorem one_pair_simulates_the_successor :
    ¬ SuccIsNotSimulated (Form := Nat) E Nat.succ := by
  intro h
  exact h 0 ⟨rfl, rfl⟩

theorem empty_absorbs : LimitAbsorbsTheChain (Form := Nat) 0 Nat.succ empty 1 := by
  intro y chain
  obtain ⟨_, held⟩ := chain 0
  exact held.elim

theorem empty_is_not_finite :
    LimitNotSimulatedFinitely (Form := Nat) 0 Nat.succ empty 1 := fun _ h => h

theorem empty_does_not_simulate_the_successor :
    SuccIsNotSimulated (Form := Nat) empty Nat.succ := fun _ h => h

theorem empty_does_not_derive_the_successor :
    ¬ SuccIsDerived (Form := Nat) Nat.succ empty Nat.succ := by
  intro h
  obtain ⟨_, held⟩ := h 0
  exact held.elim

/-- **Neither successor half implies the other.** Both models absorb the chain
and keep the limit out of finite reach, so the two transfinite conditions the
split leaves alone are held fixed while the halves separate.
`sharp_transfinite_is_four_split_conditions` is therefore a count: the
transfinite layer is four in normal form, and the fourth is not the third. -/
theorem neither_succ_half_implies_the_other :
    (LimitAbsorbsTheChain (Form := Nat) 0 Nat.succ C 1
        ∧ LimitNotSimulatedFinitely (Form := Nat) 0 Nat.succ E 1
        ∧ SuccIsDerived (Form := Nat) Nat.succ C Nat.succ
        ∧ ¬ SuccIsNotSimulated (Form := Nat) E Nat.succ)
      ∧ (LimitAbsorbsTheChain (Form := Nat) 0 Nat.succ empty 1
        ∧ LimitNotSimulatedFinitely (Form := Nat) 0 Nat.succ empty 1
        ∧ SuccIsNotSimulated (Form := Nat) empty Nat.succ
        ∧ ¬ SuccIsDerived (Form := Nat) Nat.succ empty Nat.succ) :=
  ⟨⟨total_absorbs, one_pair_is_not_finite, total_derives_the_successor,
    one_pair_simulates_the_successor⟩,
   ⟨empty_absorbs, empty_is_not_finite, empty_does_not_simulate_the_successor,
    empty_does_not_derive_the_successor⟩⟩

end TheSuccHalvesAreTwo

end FreeFiltration

namespace WeakPositionPrice

/-! ### What it would cost to state the deriver's position at `≡`

`ax-deriver-at-limit` is written `deriver == limit` in `L3_ordinatics.hm` and
mechanized as `deriver = limit` in `Ordinatics.Transfinite`.
`Ordinatics.WeakPosition.position_readings_are_incomparable` settles the
relation between the two readings in the interface: neither implies the other,
because `Simulation` there is a parameter carrying no laws.

That leaves the question this layer can actually answer. `Transfinite` draws two
consequences from the position, and both are proved by rewriting along the
equation. Replace the equation with `Simulation deriver limit` and each becomes
a chain instead, with hypotheses. The two lemmas below are those chains, stated
over an arbitrary carrier so that nothing is available beyond what is written.
What they need is three properties of the two relations, and all three are
already refuted in this file. -/

/-- The route to `deriverNotFinite` under the weak reading: one transitivity
    step, and no other hypothesis. Compare `Transfinite.deriverNotFinite`, which
    needs none because it rewrites. -/
theorem notFiniteByTransitivity {Form : Type} {ground : Form} {f2f : Form → Form}
    {Simulation : Form → Form → Prop} {limit deriver : Form}
    (weak : Simulation deriver limit)
    (trans : ∀ x y z : Form, Simulation x y → Simulation y z → Simulation x z)
    (limitNotFinite : ∀ n : Nat, ¬ Simulation (Nat.repeat f2f n ground) limit) :
    ∀ n : Nat, ¬ Simulation (Nat.repeat f2f n ground) deriver :=
  fun n step => limitNotFinite n (trans _ _ _ step weak)

/-- The route to `deriverDerivedByPath` under the weak reading. The path law
    delivers `Congruent e limit`, and the goal is `Congruent e deriver`, so the
    weak hypothesis has to cross from one relation to the other and then turn
    around: bridge, symmetry, transitivity, in that order. Compare
    `Transfinite.deriverDerivedByPath`, which is one rewrite. -/
theorem derivedByPathByBridge {Form : Type}
    {Simulation Congruent : Form → Form → Prop} {limit deriver e : Form}
    (weak : Simulation deriver limit)
    (bridge : ∀ x y : Form, Simulation x y → Congruent x y)
    (symm : ∀ x y : Form, Congruent x y → Congruent y x)
    (trans : ∀ x y z : Form, Congruent x y → Congruent y z → Congruent x z)
    (atLimit : Congruent e limit) :
    Congruent e deriver :=
  trans _ _ _ atLimit (symm _ _ (bridge _ _ weak))

/-- **The bridge is the only one of the three this layer has, and it is a
    clause rather than a theorem.** `filtrationSimCong` is one of the 24, so it
    holds in every model of them; that is the whole of what the filtration
    gives. Transitivity of `≡`, and symmetry and transitivity of `=~`, are each
    refuted by a model satisfying all 24 clauses --- the three that follow are
    `FreeSimulation.simulation_transitivity_claim_fails`,
    `AsymmetricCongruent.congruent_symmetry_claim_fails` and
    `AsymmetricCongruent.congruent_transitivity_claim_fails`, paired with the
    instances that witness them.

    So the weak reading is not merely a different clause here, as it is in the
    interface: it is a *strictly poorer* one, and the poverty is not repairable
    by this layer's own clauses. Neither consequence survives the substitution.
    Nothing below is new; the three refutations predate the question. That is
    worth recording on its own, because the note in `L3_ordinatics.hm` asserted
    the opposite --- that both costs were already paid here --- and the material
    to check it was three theorems away. -/
theorem the_weak_position_is_unaffordable_here :
    (∀ (E : FreeSimulation.Form → FreeSimulation.Form → Prop),
        FreeSimulation.PrefixAxioms E →
          ∀ x y : FreeSimulation.Form,
            FreeSimulation.Simulation E x y → FreeSimulation.Congruent E x y)
    ∧ (FreeSimulation.PrefixAxioms FreeSimulation.skipUp ∧
        ¬ ∀ x y z : FreeSimulation.Form,
            FreeSimulation.Simulation FreeSimulation.skipUp x y →
            FreeSimulation.Simulation FreeSimulation.skipUp y z →
            FreeSimulation.Simulation FreeSimulation.skipUp x z)
    ∧ (AsymmetricCongruent.PrefixAxioms AsymmetricCongruent.asym ∧
        ¬ ∀ x y : AsymmetricCongruent.Form,
            AsymmetricCongruent.Congruent AsymmetricCongruent.asym x y →
            AsymmetricCongruent.Congruent AsymmetricCongruent.asym y x)
    ∧ (AsymmetricCongruent.PrefixAxioms AsymmetricCongruent.skip ∧
        ¬ ∀ x y z : AsymmetricCongruent.Form,
            AsymmetricCongruent.Congruent AsymmetricCongruent.skip x y →
            AsymmetricCongruent.Congruent AsymmetricCongruent.skip y z →
            AsymmetricCongruent.Congruent AsymmetricCongruent.skip x z) :=
  ⟨fun _ ax => ax.filtrationSimCong,
   ⟨FreeSimulation.prefixAxioms_hold _ FreeSimulation.skipUp_avoids_ground,
    FreeSimulation.simulation_transitivity_claim_fails⟩,
   ⟨AsymmetricCongruent.prefixAxioms_hold _,
    AsymmetricCongruent.congruent_symmetry_claim_fails⟩,
   ⟨AsymmetricCongruent.prefixAxioms_hold _,
    AsymmetricCongruent.congruent_transitivity_claim_fails⟩⟩

end WeakPositionPrice

namespace FreeFiltration

/-! ### The last connective: a biconditional is two implications, and one is free

`three_implications_are_two_equivalences` compared the triangle against the hub
and found one fact written two ways. It was comparing different connectives: an
implication on the left and a biconditional on the right, so the right-hand side
was four implications counted as two fields. Two of the four are free, and they
are free for the reason the note has already named twice --- the proof lives in
another group. `E x x` gives `C x x` by the filtration, which is nowhere near
the diagonal conditions, so neither `E x x → Reach` nor `Reach → C x x` ever has
to be stated. -/

/-- **The hub is two implications.** Both biconditionals survive from a single
implication each, given one filtration clause from another group. -/
theorem the_hub_is_two_implications (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) (simIntoCong : ∀ x y, E x y → C x y) :
    ((∀ x, C x x ↔ Reach ground f2f S x) ∧ (∀ x, E x x ↔ Reach ground f2f S x))
      ↔ ((∀ x, C x x → Reach ground f2f S x) ∧
          (∀ x, Reach ground f2f S x → E x x)) := by
  constructor
  · rintro ⟨congIff, simIff⟩
    exact ⟨fun x => (congIff x).mp, fun x => (simIff x).mpr⟩
  · rintro ⟨congReach, reachSim⟩
    exact ⟨fun x => ⟨congReach x, fun h => simIntoCong x x (reachSim x h)⟩,
      fun x => ⟨fun h => congReach x (simIntoCong x x h), reachSim x⟩⟩

/-- `Conditions` with its two biconditionals spent. Eight fields still, because
two equivalences left and two implications arrived --- and now every field of
both lists is a bare implication, so the two sides can be compared in one
vocabulary for the first time. -/
structure SplitPrefixConditions (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) : Prop where
  simIntoCong : ∀ x y, E x y → C x y
  congIntoSim : ∀ x y, C x y → S x y
  imageSimilar : ∀ x, S (f2f x) x
  imageSimilarToGround : ∀ x, S (f2f x) ground
  doubleImageSimilar : ∀ x, S (f2f (f2f x)) x
  imageNotSimulatingGround : ∀ x, ¬ E (f2f x) ground
  congruentIntoReach : ∀ x, C x x → Reach ground f2f S x
  reachIntoSimulation : ∀ x, Reach ground f2f S x → E x x

theorem conditions_are_eight_split_conditions (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) :
    Conditions ground f2f S C E ↔ SplitPrefixConditions ground f2f S C E := by
  constructor
  · intro h
    have two := (the_hub_is_two_implications ground f2f S C E h.simIntoCong).mp
      ⟨h.congruentDiagonalIsReach, h.simulationDiagonalIsReach⟩
    exact { simIntoCong := h.simIntoCong
            congIntoSim := h.congIntoSim
            imageSimilar := h.imageSimilar
            imageSimilarToGround := h.imageSimilarToGround
            doubleImageSimilar := h.doubleImageSimilar
            imageNotSimulatingGround := h.imageNotSimulatingGround
            congruentIntoReach := two.1
            reachIntoSimulation := two.2 }
  · intro h
    have two := (the_hub_is_two_implications ground f2f S C E h.simIntoCong).mpr
      ⟨h.congruentIntoReach, h.reachIntoSimulation⟩
    exact { simIntoCong := h.simIntoCong
            congIntoSim := h.congIntoSim
            imageSimilar := h.imageSimilar
            imageSimilarToGround := h.imageSimilarToGround
            doubleImageSimilar := h.doubleImageSimilar
            imageNotSimulatingGround := h.imageNotSimulatingGround
            congruentDiagonalIsReach := two.1
            simulationDiagonalIsReach := two.2 }

/-- **Nine implications against eight, with nothing left hiding in a
connective.** Six fields are shared verbatim; the clause list says the diagonal
in three arrows around a triangle and the condition list says it in two, and
both lists are free of conjunctions and of biconditionals. The difference of one
is not a presentation artifact after all: it survives every splitting the note
knows how to do. -/
theorem nine_clauses_are_eight_split_conditions (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) :
    SharpPrefixAxioms ground f2f S C E ↔ SplitPrefixConditions ground f2f S C E :=
  (nine_prefix_clauses_are_eight_conditions ground f2f S C E).trans
    (conditions_are_eight_split_conditions ground f2f S C E)

/-- The residue with nothing else in scope, in one connective: three arrows
around a triangle against two arrows through reach, the filtration supplying
what neither list states. -/
theorem three_arrows_are_two_arrows (ground : Form) (f2f : Form → Form)
    (S C E : Form → Form → Prop) (simIntoCong : ∀ x y, E x y → C x y) :
    ((∀ x, Reach ground f2f S x → C x x) ∧ (∀ x, C x x → E x x) ∧
        (∀ x, E x x → Reach ground f2f S x))
      ↔ ((∀ x, C x x → Reach ground f2f S x) ∧
          (∀ x, Reach ground f2f S x → E x x)) := by
  constructor
  · rintro ⟨reachCong, congSim, simReach⟩
    exact ⟨fun x hc => simReach x (congSim x hc), fun x hr => congSim x (reachCong x hr)⟩
  · rintro ⟨congReach, reachSim⟩
    exact ⟨fun x hr => simIntoCong x x (reachSim x hr),
      fun x hc => reachSim x (congReach x hc),
      fun x he => congReach x (simIntoCong x x he)⟩

/-! ### Irredundance does not pin a count

Everything needed for this was already in the file and none of it was in one
place. Three arrow models say the triangle has no removable member; two diagonal
models say the same of the hub, and were written for a sharpening that had not
happened when they were written. Read together they look like the claim below,
but reading is not proving: irredundance of two lists over *different*
backgrounds would be two unrelated facts, and nothing had checked that the
backgrounds are the same. They are the same --- `SixSharedClauses`, and in each
case the other members of the list the member belongs to --- and the two
diagonal models happen to carry the other arrow in its stronger, biconditional
form, so they give the weaker background for free. -/

/-- The two lists carry the same content over the six, at every carrier. -/
theorem the_two_lists_agree_over_the_six :
    ∀ (α : Type) (g : α) (f : α → α) (S C E : α → α → Prop),
      SixSharedClauses g f S C E →
        (((∀ x, Reach g f S x → C x x) ∧ (∀ x, C x x → E x x) ∧
            (∀ x, E x x → Reach g f S x))
          ↔ ((∀ x, C x x → Reach g f S x) ∧ (∀ x, Reach g f S x → E x x))) :=
  fun _ g f S C E six => three_arrows_are_two_arrows g f S C E six.filtrationSimCong

/-- **Neither list has a removable member.** Each conjunct denies a uniform
derivation: a proof of one member from the six and the rest would have to hold at
every carrier, and each conjunct names a carrier where the six and the rest hold
and the member fails. The first three come from the arrow models, the last two
from the diagonal models. -/
theorem neither_list_has_a_removable_member :
    ((¬ ∀ (α : Type) (g : α) (f : α → α) (S C E : α → α → Prop),
        SixSharedClauses g f S C E → (∀ x, C x x → E x x) →
          (∀ x, E x x → Reach g f S x) → (∀ x, Reach g f S x → C x x)) ∧
      (¬ ∀ (α : Type) (g : α) (f : α → α) (S C E : α → α → Prop),
        SixSharedClauses g f S C E → (∀ x, Reach g f S x → C x x) →
          (∀ x, E x x → Reach g f S x) → (∀ x, C x x → E x x)) ∧
      (¬ ∀ (α : Type) (g : α) (f : α → α) (S C E : α → α → Prop),
        SixSharedClauses g f S C E → (∀ x, Reach g f S x → C x x) →
          (∀ x, C x x → E x x) → (∀ x, E x x → Reach g f S x)))
    ∧ ((¬ ∀ (α : Type) (g : α) (f : α → α) (S C E : α → α → Prop),
        SixSharedClauses g f S C E → (∀ x, Reach g f S x → E x x) →
          (∀ x, C x x → Reach g f S x)) ∧
      (¬ ∀ (α : Type) (g : α) (f : α → α) (S C E : α → α → Prop),
        SixSharedClauses g f S C E → (∀ x, C x x → Reach g f S x) →
          (∀ x, Reach g f S x → E x x))) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro h
    obtain ⟨six, congSim, simReach, no⟩ :=
      DropsReachIntoCongruent.six_hold_and_reach_does_not_reach_congruence
        (Form := Nat) 0 Nat.succ
    exact no (h Nat 0 Nat.succ _ _ _ six congSim simReach)
  · intro h
    obtain ⟨six, reachCong, simReach, no⟩ :=
      DropsCongruentIntoSimulation.six_hold_and_congruence_does_not_reach_equality
        (Form := Nat) 0 Nat.succ
    exact no (h Nat 0 Nat.succ _ _ _ six reachCong simReach)
  · intro h
    obtain ⟨six, reachCong, congSim, no⟩ :=
      DropsSimulationIntoReach.six_hold_and_equality_does_not_reach_back
    exact no (h Extended extGround extStep _ _ _ six reachCong congSim)
  · intro h
    obtain ⟨simCong, congSim, imgSim, imgGround, dblImg, notSim, simDiag, _⟩ :=
      NeedsCongruentDiagonalIsReach.seven_hold_and_the_congruent_diagonal_fails
    exact NeedsCongruentDiagonalIsReach.the_descending_half_is_not_derivable
      (h Extended extGround extStep _ _ _
        { axDiff := notSim
          axSim := imgGround
          axBox := dblImg
          axImageSimilar := imgSim
          filtrationSimCong := simCong
          filtrationCongSim := congSim }
        (fun x => (simDiag x).mpr))
  · intro h
    obtain ⟨simCong, congSim, imgSim, imgGround, dblImg, notSim, congDiag, _⟩ :=
      NeedsSimulationDiagonalIsReach.seven_hold_and_the_simulation_diagonal_fails
    exact NeedsSimulationDiagonalIsReach.the_rising_half_is_not_derivable
      (h Nat 0 Nat.succ _ _ _
        { axDiff := notSim
          axSim := imgGround
          axBox := dblImg
          axImageSimilar := imgSim
          filtrationSimCong := simCong
          filtrationCongSim := congSim }
        (fun x => (congDiag x).mp))

/-- **Two irredundant lists, of three members and of two, saying the same thing
over the same background about the same three predicates.** Irredundance does
not pin a count. It never did, and the whole distance from thirty-nine clauses to
here is the distance between a list with consequences in it and a list without,
not the distance between a list and its shortest form. -/
theorem two_irredundant_lists_of_different_lengths :
    (∀ (α : Type) (g : α) (f : α → α) (S C E : α → α → Prop),
      SixSharedClauses g f S C E →
        (((∀ x, Reach g f S x → C x x) ∧ (∀ x, C x x → E x x) ∧
            (∀ x, E x x → Reach g f S x))
          ↔ ((∀ x, C x x → Reach g f S x) ∧ (∀ x, Reach g f S x → E x x))))
      ∧ ((¬ ∀ (α : Type) (g : α) (f : α → α) (S C E : α → α → Prop),
            SixSharedClauses g f S C E → (∀ x, C x x → E x x) →
              (∀ x, E x x → Reach g f S x) → (∀ x, Reach g f S x → C x x)) ∧
          (¬ ∀ (α : Type) (g : α) (f : α → α) (S C E : α → α → Prop),
            SixSharedClauses g f S C E → (∀ x, Reach g f S x → C x x) →
              (∀ x, E x x → Reach g f S x) → (∀ x, C x x → E x x)) ∧
          (¬ ∀ (α : Type) (g : α) (f : α → α) (S C E : α → α → Prop),
            SixSharedClauses g f S C E → (∀ x, Reach g f S x → C x x) →
              (∀ x, C x x → E x x) → (∀ x, E x x → Reach g f S x)))
      ∧ ((¬ ∀ (α : Type) (g : α) (f : α → α) (S C E : α → α → Prop),
            SixSharedClauses g f S C E → (∀ x, Reach g f S x → E x x) →
              (∀ x, C x x → Reach g f S x)) ∧
          (¬ ∀ (α : Type) (g : α) (f : α → α) (S C E : α → α → Prop),
            SixSharedClauses g f S C E → (∀ x, C x x → Reach g f S x) →
              (∀ x, Reach g f S x → E x x))) :=
  ⟨the_two_lists_agree_over_the_six, neither_list_has_a_removable_member.1,
    neither_list_has_a_removable_member.2⟩

/-! ### Minimality: two is the smallest, and the hub is the only two

`two_irredundant_lists_of_different_lengths` says neither list has a removable
member. That is weaker than it sounds. Irredundance is a property of one list,
and two irredundant lists can have different lengths --- which is exactly what
that theorem exhibits. What pins a count is *minimality*, and minimality is a
claim about every list, not about one.

Between the three diagonal predicates there are six arrows. The six shared
clauses already give one of them: `filtrationSimCong` at `y := x` is
`E x x → C x x`, free at every setting. Five are left to say. The clause list
picks three of the five and the condition list picks two. Minimality asks
whether any other choice of two, or any one, says the diagonal over the six. -/

/-- A carrier together with the five data a filtration clause list quantifies
over. Bundling them is what lets a statement quantify over *settings* instead of
over carriers-and-relations one binder at a time, which is what saying "no pair
other than this one" requires. -/
structure Setting : Type 1 where
  carrier : Type
  ground : carrier
  step : carrier → carrier
  S : carrier → carrier → Prop
  C : carrier → carrier → Prop
  E : carrier → carrier → Prop

/-- The five arrows between the three diagonals that the six shared clauses do
not already supply. The sixth, `E x x → C x x`, is `filtrationSimCong`. -/
inductive Arrow where
  | reachCong
  | congReach
  | reachSim
  | simReach
  | congSim

def Six (m : Setting) : Prop := SixSharedClauses m.ground m.step m.S m.C m.E

def holds (m : Setting) : Arrow → Prop
  | .reachCong => ∀ x, Reach m.ground m.step m.S x → m.C x x
  | .congReach => ∀ x, m.C x x → Reach m.ground m.step m.S x
  | .reachSim => ∀ x, Reach m.ground m.step m.S x → m.E x x
  | .simReach => ∀ x, m.E x x → Reach m.ground m.step m.S x
  | .congSim => ∀ x, m.C x x → m.E x x

/-- What the condition list says, in the arrow vocabulary. -/
def Hub (m : Setting) : Prop := holds m .congReach ∧ holds m .reachSim

/-- `DropsReachIntoCongruent` as a setting: everything simulates everything and
nothing is congruent to anything. It has the three arrows out of congruence and
equality, because both are empty, and neither arrow into them. -/
def chainTrue : Setting :=
  ⟨Nat, 0, Nat.succ, DropsReachIntoCongruent.S, DropsReachIntoCongruent.C,
    DropsReachIntoCongruent.C⟩

theorem chainTrue_six : Six chainTrue :=
  (DropsReachIntoCongruent.six_hold_and_reach_does_not_reach_congruence
    (Form := Nat) 0 Nat.succ).1

theorem chainTrue_congReach : holds chainTrue .congReach := fun _ h => False.elim h
theorem chainTrue_simReach : holds chainTrue .simReach := fun _ h => False.elim h
theorem chainTrue_congSim : holds chainTrue .congSim := fun _ h => False.elim h
theorem chainTrue_no_hub : ¬ Hub chainTrue :=
  fun h => h.2 chainTrue.ground ⟨0, trivial⟩

/-- `DropsCongruentIntoSimulation` as a setting: congruence is total and
equality is empty. -/
def chainBoth : Setting :=
  ⟨Nat, 0, Nat.succ, DropsCongruentIntoSimulation.S,
    DropsCongruentIntoSimulation.S, DropsCongruentIntoSimulation.E⟩

theorem chainBoth_six : Six chainBoth :=
  (DropsCongruentIntoSimulation.six_hold_and_congruence_does_not_reach_equality
    (Form := Nat) 0 Nat.succ).1

theorem chainBoth_reachCong : holds chainBoth .reachCong := fun _ _ => trivial
theorem chainBoth_congReach : holds chainBoth .congReach := fun _ _ => ⟨0, trivial⟩
theorem chainBoth_simReach : holds chainBoth .simReach := fun _ h => False.elim h
theorem chainBoth_no_hub : ¬ Hub chainBoth :=
  fun h => h.2 chainBoth.ground ⟨0, trivial⟩

/-- `DropsSimulationIntoReach` as a setting: the adjoined point is congruent and
equal to itself and the chain never reaches it. -/
def limitFree : Setting :=
  ⟨Extended, extGround, extStep, DropsSimulationIntoReach.S,
    DropsSimulationIntoReach.S, Eq⟩

theorem limitFree_six : Six limitFree :=
  DropsSimulationIntoReach.six_hold_and_equality_does_not_reach_back.1

theorem limitFree_reachCong : holds limitFree .reachCong :=
  fun x _ => DropsSimulationIntoReach.self_similar x
theorem limitFree_reachSim : holds limitFree .reachSim := fun _ _ => rfl
theorem limitFree_congSim : holds limitFree .congSim := fun _ _ => rfl
theorem limitFree_no_hub : ¬ Hub limitFree :=
  fun h => (DropsSimulationIntoReach.reach_is_someness none).mp
    (h.1 none (DropsSimulationIntoReach.self_similar none)) rfl

/-- `NeedsCongruentDiagonalIsReach` as a setting: the only one of the four where
equality is thin enough to track `Reach` exactly, which is what makes the pair
`reachSim, simReach` available without the hub. -/
def limitEq : Setting :=
  ⟨Extended, extGround, extStep, extSimilar, NeedsCongruentDiagonalIsReach.C,
    extDiagonal⟩

theorem limitEq_six : Six limitEq := by
  obtain ⟨simCong, congSim, imgSim, imgGround, dblImg, notSim, _, _⟩ :=
    NeedsCongruentDiagonalIsReach.seven_hold_and_the_congruent_diagonal_fails
  exact { axDiff := notSim, axSim := imgGround, axBox := dblImg,
          axImageSimilar := imgSim, filtrationSimCong := simCong,
          filtrationCongSim := congSim }

theorem limitEq_reachCong : holds limitEq .reachCong := fun _ _ => rfl
theorem limitEq_reachSim : holds limitEq .reachSim :=
  fun x => (ext_conditions.simulationDiagonalIsReach x).mpr
theorem limitEq_simReach : holds limitEq .simReach :=
  fun x => (ext_conditions.simulationDiagonalIsReach x).mp
theorem limitEq_no_hub : ¬ Hub limitEq :=
  fun h => NeedsCongruentDiagonalIsReach.the_descending_half_is_not_derivable h.1

/-- **A setting is a refutation of a uniform derivation.** If some setting
satisfies the six shared clauses and two arrows but not the hub, then no
derivation of the hub from those two arrows holds at every setting. -/
theorem no_uniform_derivation {i j : Arrow} (m : Setting) (six : Six m)
    (hi : holds m i) (hj : holds m j) (noHub : ¬ Hub m) :
    ¬ ∀ n : Setting, Six n → holds n i → holds n j → Hub n :=
  fun h => noHub (h m six hi hj)

/-- **No pair of arrows other than the hub's own pair is the hub.** A pair may
repeat an arrow, so the five diagonal cases also say that no single arrow is the
hub: two is the minimum. Fifteen unordered pairs, one of them the hub itself,
and four settings covering the other fourteen. -/
theorem no_other_pair_of_arrows_is_the_hub (i j : Arrow)
    (h1 : ¬ (i = Arrow.congReach ∧ j = Arrow.reachSim))
    (h2 : ¬ (i = Arrow.reachSim ∧ j = Arrow.congReach)) :
    ¬ ∀ m : Setting, Six m → holds m i → holds m j → Hub m := by
  cases i <;> cases j
  · exact no_uniform_derivation chainBoth chainBoth_six chainBoth_reachCong
      chainBoth_reachCong chainBoth_no_hub
  · exact no_uniform_derivation chainBoth chainBoth_six chainBoth_reachCong
      chainBoth_congReach chainBoth_no_hub
  · exact no_uniform_derivation limitFree limitFree_six limitFree_reachCong
      limitFree_reachSim limitFree_no_hub
  · exact no_uniform_derivation chainBoth chainBoth_six chainBoth_reachCong
      chainBoth_simReach chainBoth_no_hub
  · exact no_uniform_derivation limitFree limitFree_six limitFree_reachCong
      limitFree_congSim limitFree_no_hub
  · exact no_uniform_derivation chainBoth chainBoth_six chainBoth_congReach
      chainBoth_reachCong chainBoth_no_hub
  · exact no_uniform_derivation chainTrue chainTrue_six chainTrue_congReach
      chainTrue_congReach chainTrue_no_hub
  · exact absurd ⟨rfl, rfl⟩ h1
  · exact no_uniform_derivation chainTrue chainTrue_six chainTrue_congReach
      chainTrue_simReach chainTrue_no_hub
  · exact no_uniform_derivation chainTrue chainTrue_six chainTrue_congReach
      chainTrue_congSim chainTrue_no_hub
  · exact no_uniform_derivation limitFree limitFree_six limitFree_reachSim
      limitFree_reachCong limitFree_no_hub
  · exact absurd ⟨rfl, rfl⟩ h2
  · exact no_uniform_derivation limitFree limitFree_six limitFree_reachSim
      limitFree_reachSim limitFree_no_hub
  · exact no_uniform_derivation limitEq limitEq_six limitEq_reachSim
      limitEq_simReach limitEq_no_hub
  · exact no_uniform_derivation limitFree limitFree_six limitFree_reachSim
      limitFree_congSim limitFree_no_hub
  · exact no_uniform_derivation chainBoth chainBoth_six chainBoth_simReach
      chainBoth_reachCong chainBoth_no_hub
  · exact no_uniform_derivation chainTrue chainTrue_six chainTrue_simReach
      chainTrue_congReach chainTrue_no_hub
  · exact no_uniform_derivation limitEq limitEq_six limitEq_simReach
      limitEq_reachSim limitEq_no_hub
  · exact no_uniform_derivation chainTrue chainTrue_six chainTrue_simReach
      chainTrue_simReach chainTrue_no_hub
  · exact no_uniform_derivation chainTrue chainTrue_six chainTrue_simReach
      chainTrue_congSim chainTrue_no_hub
  · exact no_uniform_derivation limitFree limitFree_six limitFree_congSim
      limitFree_reachCong limitFree_no_hub
  · exact no_uniform_derivation chainTrue chainTrue_six chainTrue_congSim
      chainTrue_congReach chainTrue_no_hub
  · exact no_uniform_derivation limitFree limitFree_six limitFree_congSim
      limitFree_reachSim limitFree_no_hub
  · exact no_uniform_derivation chainTrue chainTrue_six chainTrue_congSim
      chainTrue_simReach chainTrue_no_hub
  · exact no_uniform_derivation chainTrue chainTrue_six chainTrue_congSim
      chainTrue_congSim chainTrue_no_hub

/-- The hub's own pair does say it, trivially: it *is* the hub. Stated so that
minimality is two-sided and not only a list of refutations. -/
theorem the_hub_pair_does_say_it :
    ∀ m : Setting, Six m → holds m .congReach → holds m .reachSim → Hub m :=
  fun _ _ hc hr => ⟨hc, hr⟩

/-- **No two of the clause list's three arrows say the diagonal.** The corollary
that separates the two lists: the clause list is irredundant, but each of the
three pairs drawn from it has a countermodel, so it is not minimum. -/
theorem no_two_of_the_triangle_suffice :
    (¬ ∀ m : Setting, Six m → holds m .reachCong → holds m .congSim → Hub m)
      ∧ (¬ ∀ m : Setting, Six m → holds m .congSim → holds m .simReach → Hub m)
      ∧ (¬ ∀ m : Setting, Six m → holds m .reachCong → holds m .simReach → Hub m) :=
  ⟨no_uniform_derivation limitFree limitFree_six limitFree_reachCong
      limitFree_congSim limitFree_no_hub,
    no_uniform_derivation chainTrue chainTrue_six chainTrue_congSim
      chainTrue_simReach chainTrue_no_hub,
    no_uniform_derivation chainBoth chainBoth_six chainBoth_reachCong
      chainBoth_simReach chainBoth_no_hub⟩

/-- **Irredundance does not pin a count; minimality does.** The clause list and
the condition list are both irredundant, and only the condition list is minimum.
Taken with `two_irredundant_lists_of_different_lengths` the residue is settled:
the condition list is the shortest list of arrows saying the diagonal over the
six shared clauses, the clause list is not, and neither has a removable member.

The claim is minimality **in the arrow vocabulary** --- among sets drawn from
the five statements `holds` names. It does not say that no single cleverly
worded statement is equivalent to the hub. A conjunction is a statement, and
nothing here rules out finding a name for one. -/
theorem the_hub_is_the_unique_minimum :
    (∀ m : Setting, Six m → holds m .congReach → holds m .reachSim → Hub m)
      ∧ (∀ i j : Arrow, ¬ (i = Arrow.congReach ∧ j = Arrow.reachSim) →
          ¬ (i = Arrow.reachSim ∧ j = Arrow.congReach) →
          ¬ ∀ m : Setting, Six m → holds m i → holds m j → Hub m) :=
  ⟨the_hub_pair_does_say_it, no_other_pair_of_arrows_is_the_hub⟩

end FreeFiltration

namespace AxiomsMeasureVocabulary

/-! **What an axiom report is a report of.** The composition group left a rule:
a model depends on no axioms exactly when it never had to look at a carrier. It
has been cited three times as a prediction that came true, and it is false. The
counterexample is in this file --- `WitnessConjunctionDoesNotSplit` reads a
carrier and depends on nothing --- and the pair below says why.

Both theorems state the same fact about the same model. One names a lemma from
core; the other does the lemma's work by constructor injectivity. Their reports
differ, and nothing between them is mathematical. -/

theorem the_image_misses_the_ground_by_library : ∀ x : Nat, ¬ (Nat.succ x = 0) :=
  fun x => Nat.succ_ne_zero x

theorem the_image_misses_the_ground_by_hand : ∀ x : Nat, ¬ (Nat.succ x = 0) :=
  fun _ h => Nat.noConfusion h

end AxiomsMeasureVocabulary

#print axioms FreeFiltration.the_hub_is_two_implications
#print axioms FreeFiltration.conditions_are_eight_split_conditions
#print axioms FreeFiltration.nine_clauses_are_eight_split_conditions
#print axioms FreeFiltration.three_arrows_are_two_arrows
#print axioms FreeFiltration.the_two_lists_agree_over_the_six
#print axioms FreeFiltration.neither_list_has_a_removable_member
#print axioms FreeFiltration.two_irredundant_lists_of_different_lengths
#print axioms FreeFiltration.no_uniform_derivation
#print axioms FreeFiltration.no_other_pair_of_arrows_is_the_hub
#print axioms FreeFiltration.the_hub_pair_does_say_it
#print axioms FreeFiltration.no_two_of_the_triangle_suffice
#print axioms FreeFiltration.the_hub_is_the_unique_minimum
#print axioms AxiomsMeasureVocabulary.the_image_misses_the_ground_by_library
#print axioms AxiomsMeasureVocabulary.the_image_misses_the_ground_by_hand
#print axioms AsymmetricCongruent.prefixAxioms_hold
#print axioms AsymmetricCongruent.congruent_symmetry_claim_fails
#print axioms AsymmetricCongruent.congruent_transitivity_claim_fails
#print axioms AsymmetricCongruent.congruent_symmetry_independent
#print axioms AsymmetricCongruent.congruent_transitivity_independent
#print axioms AsymmetricCongruent.congruent_is_free_above_equality
#print axioms AsymmetricCongruent.componentwise_symmetry_is_exactly_congruent_symmetry
#print axioms FreeSimulation.prefixAxioms_hold
#print axioms FreeSimulation.simulation_symmetry_claim_fails
#print axioms FreeSimulation.simulation_transitivity_claim_fails
#print axioms FreeSimulation.simulation_is_free_above_equality_apart_from_axDiff
#print axioms FreeFiltration.prefixAxioms_of_conditions
#print axioms FreeFiltration.conditions_of_prefixAxioms
#print axioms FreeFiltration.prefixAxioms_iff_conditions
#print axioms FreeFiltration.reach_is_total_on_the_chain
#print axioms FreeFiltration.ext_conditions
#print axioms FreeFiltration.congruent_reflexivity_needs_an_unreached_point
#print axioms FreeFiltration.minimal_upper_relations_leave_five_conditions_on_similar
#print axioms FreeFiltration.five_hold_without_chainIsCofinal
#print axioms FreeFiltration.five_hold_without_similarReflexive
#print axioms FreeFiltration.five_hold_without_imageSimilar
#print axioms FreeFiltration.five_hold_without_imageSimilarToGround
#print axioms FreeFiltration.five_hold_without_doubleImageSimilar
#print axioms FreeFiltration.five_hold_without_formingAvoidsGround
#print axioms FreeFiltration.formedAtLeast_conditions
#print axioms FreeFiltration.similar_can_be_a_partial_order
#print axioms FreeFiltration.total_similar_leaves_exactly_three_conditions
#print axioms FreeFiltration.congruent_reflexivity_is_not_a_fourth_condition
#print axioms FreeFiltration.total_similar_makes_reach_total
#print axioms FreeFiltration.ground_is_not_an_image
#print axioms FreeFiltration.ground_is_not_a_fixed_point
#print axioms FreeFiltration.no_model_on_one_point
#print axioms FreeFiltration.two_points_are_enough
#print axioms FreeFiltration.two_is_the_smallest_carrier
#print axioms FreeFiltration.simulation_is_never_total
#print axioms FreeFiltration.total_congruent_forces_total_similar
#print axioms FreeFiltration.the_extremes_of_the_three_relations
#print axioms FreeFiltration.bool_ne_is_not
#print axioms FreeFiltration.forming_is_forced_at_two_points
#print axioms FreeFiltration.reach_is_total_at_two_points
#print axioms FreeFiltration.both_diagonals_are_forced_at_two_points
#print axioms FreeFiltration.similar_is_forced_off_one_cell_at_two_points
#print axioms FreeFiltration.two_points_are_enough_with_total_similar
#print axioms FreeFiltration.two_points_are_enough_with_maximal_simulation
#print axioms FreeFiltration.the_free_cells_are_free
#print axioms FreeFiltration.not_self_ne
#print axioms FreeFiltration.self_ne_not
#print axioms FreeFiltration.eight_cells_are_forced_at_two_points
#print axioms FreeFiltration.two_points_are_enough_with_total_congruent
#print axioms FreeFiltration.congruent_has_two_free_cells_at_two_points
#print axioms FreeFiltration.the_eight_decide_forming_and_eight_of_twelve_cells
#print axioms FreeFiltration.ThreeFormChoice.one_holds
#print axioms FreeFiltration.ThreeFormChoice.two_holds
#print axioms FreeFiltration.forming_is_not_forced_at_three_points
#print axioms FreeFiltration.two_points_determine_forming_and_three_do_not
#print axioms FreeFiltration.similar_is_never_equality
#print axioms FreeFiltration.similarity_is_not_contained_in_simulation
#print axioms FreeFiltration.the_three_relations_are_never_all_one
#print axioms FreeFiltration.congruent_may_equal_similar
#print axioms FreeFiltration.neither_inclusion_is_forced_to_be_strict
#print axioms FreeFiltration.two_hold_without_simulationIntoCongruent
#print axioms FreeFiltration.two_hold_without_simulationReflexive
#print axioms FreeFiltration.two_hold_without_imageNotSimulatingGround
#print axioms FreeFiltration.operationAxioms_iff_conditions
#print axioms FreeFiltration.prefixWithOperations_iff_conditions
#print axioms FreeFiltration.compose_nonempty_binders_are_inert
#print axioms FreeFiltration.transfinite_clauses_are_five_conditions
#print axioms FreeFiltration.all_thirty_nine_iff_nineteen_conditions
#print axioms FreeFiltration.all_forty_four_iff_twenty_four_conditions
#print axioms FreeFiltration.closingAxioms_iff_conditions
#print axioms FreeFiltration.chain_points_are_reached
#print axioms FreeFiltration.the_limit_is_off_the_chain
#print axioms FreeFiltration.no_three_distinct_booleans
#print axioms FreeFiltration.no_limit_on_two_points
#print axioms FreeFiltration.operation_conditions_hold_on_one_point
#print axioms FreeFiltration.transfinite_conditions_hold_on_one_point
#print axioms FreeFiltration.only_the_prefix_demands_a_second_form
#print axioms FreeFiltration.the_third_form_is_a_joint_demand
#print axioms FreeFiltration.no_compose_on_one_path
#print axioms FreeFiltration.two_paths_are_enough
#print axioms FreeFiltration.two_is_the_smallest_path_carrier
#print axioms FreeFiltration.ThreePointLimit.conditions_hold
#print axioms FreeFiltration.ThreePointLimit.transfinite_conditions_hold
#print axioms FreeFiltration.ThreePointLimit.all_nineteen_conditions_hold
#print axioms FreeFiltration.three_is_the_smallest_carrier_with_a_limit
#print axioms FreeFiltration.spanned_carriers_admit_no_limit
#print axioms FreeFiltration.LimitAdjoined.all_nineteen_conditions_hold
#print axioms FreeFiltration.nineteen_is_not_fourteen_plus_five
#print axioms FreeFiltration.the_closes_are_definitional
#print axioms FreeFiltration.three_of_the_fourteen_are_derivable
#print axioms FreeFiltration.prefix_is_its_fourteen_contentful_clauses
#print axioms FreeFiltration.twenty_nine_clauses_carry_the_content
#print axioms FreeFiltration.the_canonical_clauses_are_the_free_ones
#print axioms FreeFiltration.conditions_iff_the_eight
#print axioms FreeFiltration.reached_points_are_self_congruent
#print axioms FreeFiltration.self_simulating_points_are_reached
#print axioms FreeFiltration.conditions_iff_six_and_two_implications
#print axioms FreeFiltration.NeedsCongruentDiagonalIsReach.the_descending_half_is_not_derivable
#print axioms FreeFiltration.NeedsSimulationDiagonalIsReach.the_rising_half_is_not_derivable
#print axioms FreeFiltration.NeedsSimIntoCong.seven_hold_and_the_inclusion_fails
#print axioms FreeFiltration.NeedsCongIntoSim.seven_hold_and_the_descent_fails
#print axioms FreeFiltration.NeedsImageSimilar.seven_hold_and_the_image_is_not_similar
#print axioms FreeFiltration.NeedsImageSimilarToGround.seven_hold_and_the_image_misses_the_ground
#print axioms FreeFiltration.NeedsDoubleImageSimilar.seven_hold_and_the_double_image_is_not_similar
#print axioms FreeFiltration.NeedsImageNotSimulatingGround.seven_hold_and_the_denial_fails
#print axioms FreeFiltration.NeedsCongruentDiagonalIsReach.seven_hold_and_the_congruent_diagonal_fails
#print axioms FreeFiltration.NeedsSimulationDiagonalIsReach.seven_hold_and_the_simulation_diagonal_fails
#print axioms FreeFiltration.operationConditions_iff_the_three
#print axioms FreeFiltration.reached_points_are_their_own_identity_witness
#print axioms FreeFiltration.a_reached_common_predecessor_pairs_them
#print axioms FreeFiltration.mutual_predecessors_are_apart_witnesses
#print axioms FreeFiltration.NeedsApartWitnesses.ten_hold_and_nothing_is_apart
#print axioms FreeFiltration.NeedsIdentityWitness.ten_hold_and_one_point_has_no_identity_witness
#print axioms FreeFiltration.NeedsPairedWitnesses.ten_hold_and_one_pair_is_unpaired
#print axioms FreeFiltration.composeAxioms_iff_conditions
#print axioms FreeFiltration.prefixOperationsCompose_iff_conditions
#print axioms FreeFiltration.compose_conditions_are_always_available
#print axioms FreeFiltration.composeConditions_iff_the_three
#print axioms FreeFiltration.strictly_associative_is_associative_up_to_cp
#print axioms FreeFiltration.strict_unit_is_unital_up_to_cp
#print axioms FreeFiltration.no_non_unit_collapses_cp
#print axioms FreeFiltration.NeedsAssociativeUpToCp.two_hold_and_composition_is_not_associative
#print axioms FreeFiltration.NeedsUnitalUpToCp.two_hold_and_the_unit_is_not_a_unit
#print axioms FreeFiltration.NeedsSomeNonUnit.two_hold_and_everything_is_the_unit
#print axioms FreeFiltration.transfiniteConditions_iff_the_five
#print axioms FreeFiltration.someStartAtGround_is_implied_by_the_eight
#print axioms FreeFiltration.someEndAtLimit_is_implied_by_the_operations
#print axioms FreeFiltration.two_of_the_nineteen_are_theorems_of_the_others
#print axioms FreeFiltration.nineteen_iff_seventeen
#print axioms FreeFiltration.twenty_eight_clauses_carry_the_content
#print axioms FreeFiltration.twenty_eight_clauses_are_seventeen_conditions
#print axioms FreeFiltration.twenty_clauses_are_seventeen_conditions
#print axioms FreeFiltration.nine_prefix_clauses_carry_the_content
#print axioms FreeFiltration.three_implications_are_two_equivalences
#print axioms FreeFiltration.nine_prefix_clauses_are_eight_conditions
#print axioms FreeFiltration.eighteen_clauses_are_seventeen_conditions
#print axioms FreeFiltration.nine_is_six_and_a_cycle
#print axioms FreeFiltration.DropsReachIntoCongruent.six_hold_and_reach_does_not_reach_congruence
#print axioms FreeFiltration.DropsCongruentIntoSimulation.six_hold_and_congruence_does_not_reach_equality
#print axioms FreeFiltration.DropsSimulationIntoReach.six_hold_and_equality_does_not_reach_back
#print axioms FreeFiltration.the_unit_clause_is_two
#print axioms FreeFiltration.the_successor_clause_is_two
#print axioms FreeFiltration.WitnessConjunctionDoesNotSplit.the_halves_hold_and_the_clause_fails
#print axioms FreeFiltration.splitComposeAxioms_iff_conditions
#print axioms FreeFiltration.compose_is_four_split_conditions
#print axioms FreeFiltration.sharp_transfinite_is_four_split_conditions
#print axioms FreeFiltration.twenty_split_clauses_are_nineteen_split_conditions
#print axioms FreeFiltration.unitalUpToCp_iff_the_two_halves
#print axioms FreeFiltration.TheUnitalHalvesAreTwo.neither_unital_half_implies_the_other
#print axioms FreeFiltration.succEscapes_iff_the_two_halves
#print axioms FreeFiltration.TheSuccHalvesAreTwo.neither_succ_half_implies_the_other
#print axioms FreeFiltration.eleven_prefix_clauses_are_eight_conditions
#print axioms FreeFiltration.eleven_prefix_clauses_carry_the_content
#print axioms FreeFiltration.the_deriver_binder_is_inert
#print axioms FreeFiltration.a_limit_on_the_chain_absorbs_it
#print axioms FreeFiltration.unreached_limits_are_not_simulated_finitely
#print axioms FreeFiltration.a_moving_successor_escapes
#print axioms FreeFiltration.NeedsLimitAbsorbsTheChain.eighteen_hold_and_the_limit_does_not_absorb_the_chain
#print axioms FreeFiltration.NeedsLimitNotSimulatedFinitely.eighteen_hold_and_a_chain_point_simulates_the_limit
#print axioms FreeFiltration.NeedsSuccEscapes.eighteen_hold_and_the_successor_stands_still
#print axioms FreeFiltration.lists_join_freely_exactly_on_disjoint_symbols
#print axioms WeakPositionPrice.notFiniteByTransitivity
#print axioms WeakPositionPrice.derivedByPathByBridge
#print axioms WeakPositionPrice.the_weak_position_is_unaffordable_here
#print axioms FreeFiltration.operations_exclude_the_unreached_point
#print axioms FreeFiltration.endpoints_free_off_one_path
#print axioms FreeFiltration.determined_by_its_closing_clause
#print axioms FreeFiltration.incidence_one_is_two_cases
#print axioms FreeFiltration.carried_symbols_are_free
#print axioms FreeFiltration.carrying_iff_prefix
#print axioms FreeFiltration.the_unmentioned_are_unconstrained
#print axioms FreeFiltration.carrying_iff_the_whole_clause_set
#print axioms FreeFiltration.carried_symbols_are_free_at_forty_four
#print axioms FreeFiltration.the_unmentioned_are_unconstrained_at_forty_four

#print axioms FreeFiltration.ComposeNeedsTransitivity.fourFold_of_transitive
#print axioms FreeFiltration.ComposeNeedsTransitivity.related_satisfies_the_clauses
#print axioms FreeFiltration.ComposeNeedsTransitivity.related_denies_the_four_fold
#print axioms FreeFiltration.ComposeNeedsTransitivity.related_is_reflexive
#print axioms FreeFiltration.ComposeNeedsTransitivity.four_fold_without_transitivity
#print axioms FreeFiltration.ComposeNeedsTransitivity.transitivity_is_exactly_the_missing_step
#print axioms FreeFiltration.FormClosureIsOneDirection.the_ground_closure_needs_only_the_loop
#print axioms FreeFiltration.FormClosureIsOneDirection.the_close_clause_is_exactly_its_converse
#print axioms FreeFiltration.FormClosureIsOneDirection.the_other_clauses_do_not_give_the_close

#print axioms prefixAxioms_hold
#print axioms IrreflexiveSimilar.prefixAxioms_hold
#print axioms IrreflexiveSimilar.similar_reflexive_claim_fails
#print axioms IrreflexiveSimilar.similar_symmetric_claim_fails
#print axioms IrreflexiveSimilar.column_quotient_claim_fails
#print axioms IrreflexiveSimilar.prefix_without_reflexive_or_symmetric_similar
#print axioms IrreflexiveSimilar.similar_reflexivity_independent
#print axioms IrreflexiveSimilar.similar_symmetry_independent
#print axioms IrreflexiveSimilar.similar_transitive_claim_fails
#print axioms IrreflexiveSimilar.congruent_reflexive_claim_fails
#print axioms IrreflexiveSimilar.simulation_reflexive_claim_fails
#print axioms IrreflexiveSimilar.congruent_reflexivity_fails_with_unreached_form
#print axioms similar_transitivity_independent
#print axioms congruent_reflexivity_independent
#print axioms simulation_reflexivity_independent
#print axioms simulation_symmetry_independent
#print axioms simulation_transitivity_independent
#print axioms reverse_filtration_fails
#print axioms directionality_claim_fails
#print axioms driver_cycle_claim_fails
#print axioms preserving_prefix_axioms_hold
#print axioms d_spans_ground_claim_fails
#print axioms driver_endpoint_cycle_without_positive_trace
#print axioms FreeFiltration.NeedsFormingIsNotCongruentToGround.four_hold_and_the_denial_fails
#print axioms FreeFiltration.NeedsSimilarIsReflexive.four_hold_and_similarity_is_not_reflexive
#print axioms FreeFiltration.NeedsSimilarIsSymmetric.four_hold_and_similarity_is_not_symmetric
#print axioms FreeFiltration.NeedsCongruentIsTransitive.four_hold_and_congruence_is_not_transitive
#print axioms FreeFiltration.NeedsCongruentPathIsSymmetric.four_hold_and_path_congruence_is_not_symmetric

end HypermathCountermodel
