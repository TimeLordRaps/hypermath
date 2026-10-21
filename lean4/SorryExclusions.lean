import Lean
import Hypermath

set_option autoImplicit false

namespace HypermathSorryExclusions

structure Sig : Type 1 where
  Form : Type
  ground : Form
  f2f : Form → Form
  structContinues : Form → Form → Prop
  structDistinct : Form → Form → Prop
  structOrbits : Form → Form → Prop
  Similar : Form → Form → Prop
  Congruent : Form → Form → Prop
  Simulation : Form → Form → Prop
  HMSyntax : Form → Prop
  Substance : Form → Prop
  Semantics : Form → Prop
  Derives : Form → Form → Prop
  Discharge : Form → Form → Prop
  Definition : Form → Form → Prop
  FormClosure : Form → Prop
  deriver : Form
  DerivationPath : Type
  pathStep : Form → Form → DerivationPath
  pathGround : DerivationPath
  pathStart : DerivationPath → Form
  pathEnd : DerivationPath → Form
  pathLength : DerivationPath → Form
  pathTrace : DerivationPath → Form
  compose : DerivationPath → DerivationPath → DerivationPath
  congruentPath : DerivationPath → DerivationPath → Prop
  ordinalLimit : Form
  ordinalSucc : Form → Form
  ordinalApply : Form → Form → Form

structure Clauses (s : Sig) : Prop where
  axDiff : ∀ x, s.structDistinct (s.f2f x) s.ground
  axSim : ∀ x, s.structContinues (s.f2f x) s.ground
  axBox : ∀ x, s.structOrbits (s.f2f (s.f2f x)) x
  axGroundSelf : s.structContinues s.ground s.ground
  closeStructContinues : ∀ x, s.structContinues x s.ground ↔ s.Similar x s.ground
  closeStructDistinct : ∀ x y, s.structDistinct x y ↔ ¬ s.Simulation x y
  closeStructOrbits : ∀ x, s.structOrbits (s.f2f (s.f2f x)) x ↔ s.Similar (s.f2f (s.f2f x)) x
  axSyntaxRequiresSubstance : ∀ x, s.HMSyntax x → s.Substance x
  axSubstanceRequiresSemantics : ∀ x, s.Substance x → s.Semantics x
  axSemanticsRequiresSyntax : ∀ x, s.Semantics x → s.HMSyntax x
  axFormClosesLoop : ∀ x, s.HMSyntax x → s.Semantics x → s.FormClosure x
  axGroundSyntaxAx : s.HMSyntax s.ground
  axGroundSubstanceAx : s.Substance s.ground
  axGroundSemanticsAx : s.Semantics s.ground
  filtrationSimCong : ∀ x y, s.Simulation x y → s.Congruent x y
  filtrationCongSim : ∀ x y, s.Congruent x y → s.Similar x y
  closeSyntaxOpaque : ∀ x, s.HMSyntax x ↔ ∃ n : Nat, s.Similar (Nat.repeat s.f2f n s.ground) x
  closeSubstanceOpaque : ∀ x, s.Substance x ↔ s.Congruent x x
  closeSemanticsOpaque : ∀ x, s.Semantics x ↔ s.Simulation x x
  closeDerivesOpaque : ∀ x y, s.Derives x y ↔ ∃ n : Nat, s.Congruent (Nat.repeat s.f2f n x) y
  closeDischargeOpaque : ∀ c e, s.Discharge c e ↔ s.Derives e c
  closeDefinitionOpaque : ∀ n x, s.Definition n x ↔ s.Derives n x
  closeFormClosureOpaque : ∀ x, s.FormClosure x ↔ (s.HMSyntax x ∧ s.Substance x ∧ s.Semantics x)
  axDiffCongruent : ∀ x, ¬ s.Congruent (s.f2f x) s.ground
  axSimilarRefl : ∀ x, s.Similar x x
  axSimilarSymm : ∀ x y, s.Similar x y → s.Similar y x
  axCongruentTrans : ∀ x y z, s.Congruent x y → s.Congruent y z → s.Congruent x z
  traceLevels : ∀ x, s.Similar (s.f2f x) x ∧
    (s.Congruent (s.f2f x) x → s.Similar (s.f2f x) x) ∧
    (s.Simulation (s.f2f x) x → s.Congruent (s.f2f x) x)
  axSeq : ∀ a b, ∃ c, s.Similar c a ∧ s.Similar c b
  axSeqAsymm : ∀ a b, ¬ s.Congruent a b → ∃ c d,
    s.Similar c a ∧ s.Similar c b ∧ s.Similar d b ∧ s.Similar d a ∧ ¬ s.Congruent c d
  axSeqIdentityR : ∀ a, ∃ c, s.Similar c a ∧ s.Congruent c a
  axSeqIdentityL : ∀ a, ∃ c, s.Similar c a ∧ s.Congruent c a
  axCoop : ∀ a b, ∃ c, s.Similar c a ∧ s.Similar c b
  axCoopComm : ∀ a b, ∃ ca cab,
    s.Similar ca a ∧ s.Similar ca b ∧ s.Similar cab b ∧ s.Similar cab a ∧ s.Congruent ca cab
  axCoopIdentity : ∀ a, ∃ c, s.Similar c a ∧ s.Congruent c a
  axComposeAssoc : ∀ p q r,
    s.congruentPath (s.compose p (s.compose q r)) (s.compose (s.compose p q) r)
  axComposeIdentity : ∀ p,
    s.congruentPath (s.compose p s.pathGround) p ∧ s.congruentPath (s.compose s.pathGround p) p
  axComposeNonempty : ∀ _x _y : s.Form, ∃ p, ¬ s.congruentPath p s.pathGround
  axCongruentPathSymm : ∀ p q, s.congruentPath p q → s.congruentPath q p
  axLimitNotFinite : ∀ n : Nat, ¬ s.Simulation (Nat.repeat s.f2f n s.ground) s.ordinalLimit
  axLimitDerives : ∃ limitPath,
    s.Similar (s.pathStart limitPath) s.ground ∧ s.Congruent (s.pathEnd limitPath) s.ordinalLimit
  axSuccExtends : ∀ x, s.Derives x (s.ordinalSucc x) ∧ ¬ s.Simulation (s.ordinalSucc x) x
  axLimitIsLimit : ∀ y,
    (∀ n : Nat, s.Derives (Nat.repeat s.f2f n s.ground) y) → s.Derives s.ordinalLimit y
  axDeriverAtLimit : s.deriver = s.ordinalLimit

noncomputable def production : Sig where
  Form := Hypermath.Form
  ground := Hypermath.ground
  f2f := Hypermath.f2f
  structContinues := Hypermath.structContinues
  structDistinct := Hypermath.structDistinct
  structOrbits := Hypermath.structOrbits
  Similar := Hypermath.Similar
  Congruent := Hypermath.Congruent
  Simulation := Hypermath.Simulation
  HMSyntax := Hypermath.HMSyntax
  Substance := Hypermath.Substance
  Semantics := Hypermath.Semantics
  Derives := Hypermath.Derives
  Discharge := Hypermath.Discharge
  Definition := Hypermath.Definition
  FormClosure := Hypermath.FormClosure
  deriver := Hypermath.deriver
  DerivationPath := Hypermath.DerivationPath
  pathStep := Hypermath.pathStep
  pathGround := Hypermath.pathGround
  pathStart := Hypermath.pathStart
  pathEnd := Hypermath.pathEnd
  pathLength := Hypermath.pathLength
  pathTrace := Hypermath.pathTrace
  compose := Hypermath.compose
  congruentPath := Hypermath.congruentPath
  ordinalLimit := Hypermath.ordinalLimit
  ordinalSucc := Hypermath.ordinalSucc
  ordinalApply := Hypermath.ordinalApply

theorem production_clauses : Clauses production where
  axDiff := Hypermath.axDiff
  axSim := Hypermath.axSim
  axBox := Hypermath.axBox
  axGroundSelf := Hypermath.axGroundSelf
  closeStructContinues := Hypermath.closeStructContinues
  closeStructDistinct := Hypermath.closeStructDistinct
  closeStructOrbits := Hypermath.closeStructOrbits
  axSyntaxRequiresSubstance := Hypermath.axSyntaxRequiresSubstance
  axSubstanceRequiresSemantics := Hypermath.axSubstanceRequiresSemantics
  axSemanticsRequiresSyntax := Hypermath.axSemanticsRequiresSyntax
  axFormClosesLoop := Hypermath.axFormClosesLoop
  axGroundSyntaxAx := Hypermath.axGroundSyntaxAx
  axGroundSubstanceAx := Hypermath.axGroundSubstanceAx
  axGroundSemanticsAx := Hypermath.axGroundSemanticsAx
  filtrationSimCong := Hypermath.filtrationSimCong
  filtrationCongSim := Hypermath.filtrationCongSim
  closeSyntaxOpaque := Hypermath.closeSyntaxOpaque
  closeSubstanceOpaque := Hypermath.closeSubstanceOpaque
  closeSemanticsOpaque := Hypermath.closeSemanticsOpaque
  closeDerivesOpaque := Hypermath.closeDerivesOpaque
  closeDischargeOpaque := Hypermath.closeDischargeOpaque
  closeDefinitionOpaque := Hypermath.closeDefinitionOpaque
  closeFormClosureOpaque := Hypermath.closeFormClosureOpaque
  axDiffCongruent := Hypermath.axDiffCongruent
  axSimilarRefl := Hypermath.axSimilarRefl
  axSimilarSymm := Hypermath.axSimilarSymm
  axCongruentTrans := Hypermath.axCongruentTrans
  traceLevels := Hypermath.traceLevels
  axSeq := Hypermath.axSeq
  axSeqAsymm := Hypermath.axSeqAsymm
  axSeqIdentityR := Hypermath.axSeqIdentityR
  axSeqIdentityL := Hypermath.axSeqIdentityL
  axCoop := Hypermath.axCoop
  axCoopComm := Hypermath.axCoopComm
  axCoopIdentity := Hypermath.axCoopIdentity
  axComposeAssoc := Hypermath.axComposeAssoc
  axComposeIdentity := Hypermath.axComposeIdentity
  axComposeNonempty := Hypermath.axComposeNonempty
  axCongruentPathSymm := Hypermath.axCongruentPathSymm
  axLimitNotFinite := Hypermath.axLimitNotFinite
  axLimitDerives := Hypermath.axLimitDerives
  axSuccExtends := Hypermath.axSuccExtends
  axLimitIsLimit := Hypermath.axLimitIsLimit
  axDeriverAtLimit := Hypermath.ordinatics.deriverAtLimit

open Lean

def excludedDeclarations : List (Name × Name) := []

def witnesses : List Name := []

def layerModules : List Name :=
  [`Hypermath.L0Ground, `Hypermath.L1Relations, `Hypermath.L2Operations,
   `Hypermath.L3Ordinatics]

partial def reachesSorry (env : Environment) (memo : IO.Ref (Std.HashMap Name Bool))
    (n : Name) : IO Bool := do
  if let some known := (← memo.get)[n]? then return known
  memo.modify (·.insert n false)
  let some info := env.find? n | return false
  let mut found := n == ``sorryAx
  unless found do
    let used := info.type.getUsedConstants ++
      (match info.value? with | some v => v.getUsedConstants | none => #[])
    for m in used do
      if ← reachesSorry env memo m then
        found := true
        break
  memo.modify (·.insert n found)
  return found

end HypermathSorryExclusions

open Lean Elab Command HypermathSorryExclusions in
run_cmd do
  let env ← getEnv
  let mut problems : Array String := #[]
  let moduleOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
  let memo ← IO.mkRef ({} : Std.HashMap Name Bool)
  let mut scanned := 0
  let mut found : Array Name := #[]
  for (n, _) in env.constants.toList do
    let some m := moduleOf n | continue
    unless (`Hypermath).isPrefixOf m do continue
    scanned := scanned + 1
    if ← reachesSorry env memo n then found := found.push n
  let listed := excludedDeclarations.map (·.1)
  for n in found do
    unless listed.contains n do
      problems := problems.push s!"{n} depends on sorryAx and is not on the exclusion list"
  for (n, m) in excludedDeclarations do
    unless found.contains n do
      problems := problems.push s!"{n} is on the exclusion list but does not depend on sorryAx"
    if moduleOf n != some m then
      problems := problems.push s!"{n} is recorded in {m} but is declared in {moduleOf n}"
  let foundation := [``propext, ``Classical.choice, ``Quot.sound]
  for w in witnesses do
    for a in ← collectAxioms w do
      unless foundation.contains a do
        problems := problems.push s!"witness {w} uses {a}"
  let used ← collectAxioms ``production_clauses
  let mut declared : Array Name := #[]
  for (n, info) in env.constants.toList do
    if let .axiomInfo _ := info then
      if let some m := moduleOf n then
        if layerModules.contains m then declared := declared.push n
  for a in declared do
    unless used.contains a do
      problems := problems.push s!"production_clauses omits the production axiom {a}"
  for a in used do
    unless declared.contains a do
      problems := problems.push s!"production_clauses uses {a}, which no layer module declares"
  if (env.find? ``Hypermath.definitionOfGround).isNone then
    throwError "Hypermath.definitionOfGround is missing"
  if moduleOf ``Hypermath.definitionOfGround != some `Hypermath.L0Ground then
    problems := problems.push "definitionOfGround is not declared in L0Ground"
  if ← reachesSorry env memo ``Hypermath.definitionOfGround then
    problems := problems.push "definitionOfGround depends on sorryAx"
  unless problems.isEmpty do
    throwError m!"SORRY_EXCLUSIONS FAIL\n{String.intercalate "\n" problems.toList}"
  IO.println s!"SORRY_EXCLUSIONS PASS scanned={scanned} sorry_dependents={found.size} excluded={excludedDeclarations.length} witnesses={witnesses.length} production_axioms={declared.size}"
  let sorted := found.qsort (fun a b => a.toString < b.toString)
  for n in sorted do
    IO.println s!"EXCLUDED {n}"
