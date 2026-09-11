import Hypermath.RecordMachine

/-!
# Explicit substitution for the finite source rules

The retained source kernel describes an application by its rule, substitution,
and substituted premises. This module makes those inputs explicit for every
instruction of the existing ground-record machine. Variable positions are
finite natural-number indices, with separate term and formula sorts.

This is a finite operational refinement of that source description. Pattern
recursion and equality checking remain Lean infrastructure. In particular this
does not identify substitution with `ordinal_wrap`, this operation with `f2f`,
or successful execution with source-native ranked acceptance.
-/

namespace Hypermath.RuleSubstitution

open GroundSyntax GroundDerivation

inductive TermPattern where
  | variable (index : Nat)
  | ground
  | apply (argument : TermPattern)
  deriving DecidableEq, Repr

inductive FormulaPattern where
  | variable (index : Nat)
  | distinct (left right : TermPattern)
  | continues (left right : TermPattern)
  | orbits (left right : TermPattern)
  | similar (left right : TermPattern)
  | notSimulation (left right : TermPattern)
  | both (left right : FormulaPattern)
  deriving DecidableEq, Repr

structure Environment where
  terms : List Term
  formulas : List Formula
  deriving DecidableEq, Repr

def TermPattern.instantiate (env : Environment) : TermPattern → Option Term
  | .variable index => env.terms[index]?
  | .ground => some .ground
  | .apply argument => (argument.instantiate env).map Term.apply

def FormulaPattern.instantiate (env : Environment) : FormulaPattern → Option Formula
  | .variable index => env.formulas[index]?
  | .distinct left right => do
      return .structural (.distinct (← left.instantiate env) (← right.instantiate env))
  | .continues left right => do
      return .structural (.continues (← left.instantiate env) (← right.instantiate env))
  | .orbits left right => do
      return .structural (.orbits (← left.instantiate env) (← right.instantiate env))
  | .similar left right => do
      return .similar (← left.instantiate env) (← right.instantiate env)
  | .notSimulation left right => do
      return .notSimulation (← left.instantiate env) (← right.instantiate env)
  | .both left right => do
      return .both (← left.instantiate env) (← right.instantiate env)

def instantiateAll (env : Environment) : List FormulaPattern → Option (List Formula)
  | [] => some []
  | first :: rest => do return (← first.instantiate env) :: (← instantiateAll env rest)

/-- Only the four ground axioms, three closes, and three conjunction rules. -/
inductive RuleName where
  | groundSelf | diff | sim | box
  | closeContinues | closeDistinct | closeOrbits
  | join | projectLeft | projectRight
  deriving DecidableEq, Repr

structure Schema where
  termArity : Nat
  formulaArity : Nat
  premises : List FormulaPattern
  conclusion : FormulaPattern

/-- Premises are in stack order; the most recently proved premise comes first. -/
def schema : RuleName → Schema
  | .groundSelf => ⟨0, 0, [], .continues .ground .ground⟩
  | .diff => ⟨1, 0, [], .distinct (.apply (.variable 0)) .ground⟩
  | .sim => ⟨1, 0, [], .continues (.apply (.variable 0)) .ground⟩
  | .box => ⟨1, 0, [], .orbits (.apply (.apply (.variable 0))) (.variable 0)⟩
  | .closeContinues => ⟨1, 0, [.continues (.variable 0) .ground],
      .similar (.variable 0) .ground⟩
  | .closeDistinct => ⟨2, 0, [.distinct (.variable 0) (.variable 1)],
      .notSimulation (.variable 0) (.variable 1)⟩
  | .closeOrbits => ⟨1, 0, [.orbits (.apply (.apply (.variable 0))) (.variable 0)],
      .similar (.apply (.apply (.variable 0))) (.variable 0)⟩
  | .join => ⟨0, 2, [.variable 1, .variable 0], .both (.variable 0) (.variable 1)⟩
  | .projectLeft => ⟨0, 2, [.both (.variable 0) (.variable 1)], .variable 0⟩
  | .projectRight => ⟨0, 2, [.both (.variable 0) (.variable 1)], .variable 1⟩

structure Application where
  rule : RuleName
  environment : Environment
  deriving DecidableEq, Repr

/-- Reject missing, surplus, and incorrectly sorted substitution arguments. -/
def Application.instantiate (application : Application) : Option (List Formula × Formula) := do
  let rule := schema application.rule
  let env := application.environment
  if env.terms.length = rule.termArity ∧ env.formulas.length = rule.formulaArity then
    return (← instantiateAll env rule.premises, ← rule.conclusion.instantiate env)
  else none

/-- Inspect every substituted premise, retaining the untouched stack context. -/
def consume : List Formula → List Formula → Option (List Formula)
  | [], stack => some stack
  | expected :: premises, actual :: stack =>
      if actual = expected then consume premises stack else none
  | _ :: _, [] => none

def Application.run (application : Application) : RecordMachine.State → RecordMachine.State
  | none => none
  | some stack => do
      let (premises, result) ← application.instantiate
      let rest ← consume premises stack
      return result :: rest

/-- Construct the retained substitution for an existing instruction.
Join infers its two formula arguments from the actual premise stack. -/
def compile : RecordMachine.Instruction → RecordMachine.State → Option Application
  | .primitive .groundSelf, _ => some ⟨.groundSelf, ⟨[], []⟩⟩
  | .primitive (.diff term), _ => some ⟨.diff, ⟨[term], []⟩⟩
  | .primitive (.sim term), _ => some ⟨.sim, ⟨[term], []⟩⟩
  | .primitive (.box term), _ => some ⟨.box, ⟨[term], []⟩⟩
  | .closeContinues term, _ => some ⟨.closeContinues, ⟨[term], []⟩⟩
  | .closeDistinct left right, _ => some ⟨.closeDistinct, ⟨[left, right], []⟩⟩
  | .closeOrbits term, _ => some ⟨.closeOrbits, ⟨[term], []⟩⟩
  | .join, some (right :: left :: _) => some ⟨.join, ⟨[], [left, right]⟩⟩
  | .join, _ => none
  | .projectLeft left right, _ => some ⟨.projectLeft, ⟨[], [left, right]⟩⟩
  | .projectRight left right, _ => some ⟨.projectRight, ⟨[], [left, right]⟩⟩

/-- Executes the schema and substitution; it does not call the old machine step. -/
def step (instruction : RecordMachine.Instruction) (state : RecordMachine.State) :
    RecordMachine.State := do
  let application ← compile instruction state
  application.run state

theorem step_agrees (instruction : RecordMachine.Instruction) (state : RecordMachine.State) :
    step instruction state = RecordMachine.step instruction state := by
  cases instruction with
  | primitive rule =>
      cases rule <;> cases state <;>
        simp [step, compile, Application.run, Application.instantiate, schema,
          instantiateAll, FormulaPattern.instantiate, TermPattern.instantiate,
          consume, RecordMachine.step, AxiomInstance.conclusion]
  | join =>
      cases state with
      | none => rfl
      | some stack =>
          cases stack with
          | nil => rfl
          | cons right rest =>
              cases rest with
              | nil => rfl
              | cons left rest =>
                  simp [step, compile, Application.run, Application.instantiate, schema,
                    instantiateAll, FormulaPattern.instantiate, consume, RecordMachine.step]
  | closeContinues term | closeDistinct left right | closeOrbits term
      | projectLeft left right | projectRight left right =>
      cases state with
      | none => rfl
      | some stack =>
          cases stack <;>
            simp [step, compile, Application.run, Application.instantiate, schema,
              instantiateAll, FormulaPattern.instantiate, TermPattern.instantiate,
              consume, RecordMachine.step, RecordMachine.replace] <;> split <;> rfl

def execute : List RecordMachine.Instruction → RecordMachine.State → RecordMachine.State
  | [], state => state
  | instruction :: rest, state => execute rest (step instruction state)

theorem execute_agrees (instructions : List RecordMachine.Instruction)
    (state : RecordMachine.State) :
    execute instructions state = RecordMachine.execute instructions state := by
  induction instructions generalizing state with
  | nil => rfl
  | cons instruction rest ih => simp only [execute, RecordMachine.execute, step_agrees, ih]

theorem execute_program (record : Record) (stack : List Formula) :
    execute (RecordMachine.program record) (some stack) =
      if record.valid then some (record.conclusion :: stack) else none :=
  (execute_agrees _ _).trans (RecordMachine.execute_program record stack)

def check (record : Record) (claimed : Formula) : Bool :=
  decide (execute (RecordMachine.program record) (some []) = some [claimed])

theorem check_agrees (record : Record) (claimed : Formula) :
    check record claimed = GroundDerivation.check record claimed := by
  simpa only [check, execute_agrees, RecordMachine.check] using
    RecordMachine.check_agrees record claimed

theorem check_sound (model : GroundDerivation.Model) (record : Record) (claimed : Formula)
    (accepted : check record claimed = true) : claimed.holds model :=
  GroundDerivation.check_sound model record claimed ((check_agrees _ _) ▸ accepted)

theorem check_quote {claimed : Formula} (proof : Derivation claimed) :
    check (quote proof) claimed = true := by
  rw [check_agrees]
  exact GroundDerivation.check_quote proof

open GroundCode (Tree)

def listTree {α : Type} (encode : α → Tree) : List α → Tree
  | [] => .leaf
  | first :: rest => .fork (encode first) (listTree encode rest)

def readList {α : Type} (decode : Tree → Option α) : Tree → Option (List α)
  | .leaf => some []
  | .fork first rest => do return (← decode first) :: (← readList decode rest)

theorem readList_listTree {α : Type} (encode : α → Tree) (decode : Tree → Option α)
    (correct : ∀ value, decode (encode value) = some value) (values : List α) :
    readList decode (listTree encode values) = some values := by
  induction values <;> simp_all [listTree, readList]

def RuleName.index : RuleName → Nat
  | .groundSelf => 0 | .diff => 1 | .sim => 2 | .box => 3
  | .closeContinues => 4 | .closeDistinct => 5 | .closeOrbits => 6
  | .join => 7 | .projectLeft => 8 | .projectRight => 9

def readRule : Nat → Option RuleName
  | 0 => some .groundSelf | 1 => some .diff | 2 => some .sim | 3 => some .box
  | 4 => some .closeContinues | 5 => some .closeDistinct | 6 => some .closeOrbits
  | 7 => some .join | 8 => some .projectLeft | 9 => some .projectRight
  | _ => none

theorem readRule_index (rule : RuleName) : readRule rule.index = some rule := by
  cases rule <;> rfl

/-- Outer tag 10 separates applications from existing record and formula codes.
Both substitution lists are retained, even if the application will be rejected. -/
def Application.tree (application : Application) : Tree :=
  RecordEncoding.tag 10 (RecordEncoding.tag application.rule.index
    (.fork (listTree RecordEncoding.termTree application.environment.terms)
      (listTree RecordEncoding.formulaTree application.environment.formulas)))

def readApplication (tree : Tree) : Option Application := do
  let payload ← RecordEncoding.unwrap 10 tree
  match payload with
  | .fork rule (.fork terms formulas) =>
      return ⟨← readRule (← RecordEncoding.readTag rule),
        ⟨← readList RecordEncoding.readTerm terms, ← readList RecordEncoding.readFormula formulas⟩⟩
  | _ => none

theorem readApplication_tree (application : Application) :
    readApplication application.tree = some application := by
  cases application with
  | mk rule env =>
      cases env
      simp [Application.tree, readApplication, RecordEncoding.unwrap, RecordEncoding.tag,
        RecordEncoding.readTag_number, readRule_index,
        readList_listTree _ _ RecordEncoding.readTerm_termTree,
        readList_listTree _ _ RecordEncoding.readFormula_formulaTree]

def Application.code (application : Application) : Nat := application.tree.code

def decodeNumber (code : Nat) : Option Application := do
  readApplication (← GroundCode.decodeNumber code)

theorem decode_code (application : Application) : decodeNumber application.code = some application := by
  simp [decodeNumber, Application.code, GroundCode.decode_code, readApplication_tree]

def Application.toTerm (application : Application) : Term := Term.ofDepth application.code

def decodeTerm (term : Term) : Option Application := decodeNumber term.depth

theorem decode_toTerm (application : Application) :
    decodeTerm application.toTerm = some application := by
  simp [decodeTerm, Application.toTerm, Term.depth_ofDepth, decode_code]

theorem toTerm_injective {first second : Application} (same : first.toTerm = second.toTerm) :
    first = second :=
  Option.some.inj ((decode_toTerm first).symm.trans
    ((congrArg decodeTerm same).trans (decode_toTerm second)))

/-- Packed input avoids materializing the exponentially larger unary term. -/
def runNumber (code : Nat) (state : RecordMachine.State) : RecordMachine.State := do
  let application ← decodeNumber code
  application.run state

theorem runNumber_code (application : Application) (state : RecordMachine.State) :
    runNumber application.code state = application.run state := by
  simp [runNumber, decode_code]

def runTerm (term : Term) (state : RecordMachine.State) : RecordMachine.State :=
  runNumber term.depth state

theorem runTerm_toTerm (application : Application) (state : RecordMachine.State) :
    runTerm application.toTerm state = application.run state := by
  simp [runTerm, Application.toTerm, Term.depth_ofDepth, runNumber_code]

/-- Decoding an application from a formula representation fails at the outer sort tag. -/
theorem formula_code_rejected (formula : Formula) :
    decodeNumber (RecordEncoding.formulaCode formula) = none := by
  simp [decodeNumber, RecordEncoding.formulaCode, GroundCode.decode_code, readApplication,
    RecordEncoding.unwrap, RecordEncoding.tag, RecordEncoding.readTag_number]

theorem record_code_rejected (record : Record) :
    decodeNumber (RecordEncoding.recordCode record) = none := by
  simp [decodeNumber, RecordEncoding.recordCode, GroundCode.decode_code, readApplication,
    RecordEncoding.unwrap, RecordEncoding.tag, RecordEncoding.readTag_number]

/-- A rule identifier alone does not determine its substituted result. -/
theorem no_rule_only_instantiation :
    ¬ ∃ instantiate : RuleName → Option (List Formula × Formula),
      ∀ application : Application, instantiate application.rule = application.instantiate := by
  rintro ⟨instantiate, agrees⟩
  have first := agrees ⟨.diff, ⟨[.ground], []⟩⟩
  have second := agrees ⟨.diff, ⟨[.apply .ground], []⟩⟩
  have impossible := first.symm.trans second
  cases impossible

/-- A complete checking invocation retains the input stack as well as the application.
No additional proof or unrecorded premise stack is supplied to its decoder. -/
structure Call where
  application : Application
  state : RecordMachine.State
  deriving DecidableEq, Repr

def stateTree : RecordMachine.State → Tree
  | none => .leaf
  | some stack => .fork .leaf (listTree RecordEncoding.formulaTree stack)

def readState : Tree → Option RecordMachine.State
  | .leaf => some none
  | .fork .leaf stack => (readList RecordEncoding.readFormula stack).map some
  | _ => none

theorem readState_stateTree (state : RecordMachine.State) :
    readState (stateTree state) = some state := by
  cases state <;> simp [stateTree, readState,
    readList_listTree _ _ RecordEncoding.readFormula_formulaTree]

def Call.tree (call : Call) : Tree :=
  RecordEncoding.tag 11 (.fork call.application.tree (stateTree call.state))

def readCall (tree : Tree) : Option Call := do
  let payload ← RecordEncoding.unwrap 11 tree
  match payload with
  | .fork application state => return ⟨← readApplication application, ← readState state⟩
  | _ => none

theorem readCall_tree (call : Call) : readCall call.tree = some call := by
  cases call
  simp [Call.tree, readCall, RecordEncoding.unwrap_tag,
    readApplication_tree, readState_stateTree]

def Call.code (call : Call) : Nat := call.tree.code

def decodeCall (code : Nat) : Option Call := do readCall (← GroundCode.decodeNumber code)

theorem decodeCall_code (call : Call) : decodeCall call.code = some call := by
  simp [decodeCall, Call.code, GroundCode.decode_code, readCall_tree]

def Call.toTerm (call : Call) : Term := Term.ofDepth call.code

theorem decodeCall_toTerm (call : Call) : decodeCall call.toTerm.depth = some call := by
  simp [Call.toTerm, Term.depth_ofDepth, decodeCall_code]

theorem call_toTerm_injective {first second : Call} (same : first.toTerm = second.toTerm) :
    first = second :=
  Option.some.inj ((decodeCall_toTerm first).symm.trans
    ((congrArg (fun term : Term => decodeCall term.depth) same).trans (decodeCall_toTerm second)))

/-- The encoded call alone supplies the rule, substitution, and exact input state. -/
def runCallNumber (code : Nat) : RecordMachine.State := do
  let call ← decodeCall code
  call.application.run call.state

theorem runCallNumber_code (call : Call) :
    runCallNumber call.code = call.application.run call.state := by
  simp [runCallNumber, decodeCall_code]

def runCallTerm (term : Term) : RecordMachine.State := runCallNumber term.depth

theorem runCallTerm_toTerm (call : Call) :
    runCallTerm call.toTerm = call.application.run call.state := by
  simp [runCallTerm, Call.toTerm, Term.depth_ofDepth, runCallNumber_code]

/-- Every executed schema invocation is serialized with its input state first. -/
def encodedStep (instruction : RecordMachine.Instruction) (state : RecordMachine.State) :
    RecordMachine.State := do
  let application ← compile instruction state
  runCallNumber (Call.mk application state).code

theorem encodedStep_agrees (instruction : RecordMachine.Instruction) (state : RecordMachine.State) :
    encodedStep instruction state = RecordMachine.step instruction state := by
  rw [← step_agrees]
  simp [encodedStep, step, runCallNumber_code]

def encodedExecute : List RecordMachine.Instruction → RecordMachine.State → RecordMachine.State
  | [], state => state
  | instruction :: rest, state => encodedExecute rest (encodedStep instruction state)

theorem encodedExecute_agrees (instructions : List RecordMachine.Instruction)
    (state : RecordMachine.State) :
    encodedExecute instructions state = RecordMachine.execute instructions state := by
  induction instructions generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [encodedExecute, RecordMachine.execute, encodedStep_agrees, ih]

theorem encodedExecute_program (record : Record) (stack : List Formula) :
    encodedExecute (RecordMachine.program record) (some stack) =
      if record.valid then some (record.conclusion :: stack) else none :=
  (encodedExecute_agrees _ _).trans (RecordMachine.execute_program record stack)

def encodedCheck (record : Record) (claimed : Formula) : Bool :=
  decide (encodedExecute (RecordMachine.program record) (some []) = some [claimed])

theorem encodedCheck_agrees (record : Record) (claimed : Formula) :
    encodedCheck record claimed = GroundDerivation.check record claimed := by
  simpa only [encodedCheck, encodedExecute_agrees, RecordMachine.check] using
    RecordMachine.check_agrees record claimed

theorem encodedCheck_sound (model : GroundDerivation.Model) (record : Record) (claimed : Formula)
    (accepted : encodedCheck record claimed = true) : claimed.holds model :=
  GroundDerivation.check_sound model record claimed ((encodedCheck_agrees _ _) ▸ accepted)

theorem encodedCheck_quote {claimed : Formula} (proof : Derivation claimed) :
    encodedCheck (quote proof) claimed = true := by
  rw [encodedCheck_agrees]
  exact GroundDerivation.check_quote proof

end Hypermath.RuleSubstitution
