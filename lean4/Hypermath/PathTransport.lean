import Hypermath.PathLayers

/-!
# Witnessed reproduction across related boundaries

This is a conditional, one-step-for-one-step transport construction. The
relation is a parameter, not a new definition of native Simulation. Both
paths and their pointwise correspondence remain available. No connector
between the starting points, equality, or quotient is assumed.
-/

namespace Hypermath.PathTransport

variable {α : Type} {Step : α → α → Prop} {Related : α → α → Prop}

/-- A constructive choice of a corresponding next step, including its evidence. -/
abbrev StepTransfer (Step Related : α → α → Prop) :=
  ∀ {x y copyStart : α}, Related x copyStart → Step x y →
    { copyEnd : α // Step copyStart copyEnd ∧ Related y copyEnd }

/-- Correspondence at every vertex, including both boundaries of empty paths. -/
inductive Alignment (Related : α → α → Prop) :
    {x y copyStart copyEnd : α} → Trace Step x y → Trace Step copyStart copyEnd → Prop where
  | nil {x copyStart} (related : Related x copyStart) : Alignment Related (.nil x) (.nil copyStart)
  | cons {x y z copyStart copyNext copyEnd}
      {edge : Step x y} {copyEdge : Step copyStart copyNext}
      {tail : Trace Step y z} {copyTail : Trace Step copyNext copyEnd}
      (related : Related x copyStart) (rest : Alignment Related tail copyTail) :
      Alignment Related (.cons edge tail) (.cons copyEdge copyTail)

theorem Alignment.starts {x y copyStart copyEnd : α}
    {path : Trace Step x y} {copy : Trace Step copyStart copyEnd}
    (aligned : Alignment Related path copy) : Related x copyStart := by
  cases aligned with
  | nil related => exact related
  | cons related _ => exact related

theorem Alignment.ends {x y copyStart copyEnd : α}
    {path : Trace Step x y} {copy : Trace Step copyStart copyEnd}
    (aligned : Alignment Related path copy) : Related y copyEnd := by
  induction aligned with
  | nil related => exact related
  | cons _ _ ih => exact ih

theorem Alignment.length_eq {x y copyStart copyEnd : α}
    {path : Trace Step x y} {copy : Trace Step copyStart copyEnd}
    (aligned : Alignment Related path copy) : copy.length = path.length := by
  induction aligned with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem Alignment.compose {a b c a' b' c' : α}
    {first : Trace Step a b} {second : Trace Step b c}
    {firstCopy : Trace Step a' b'} {secondCopy : Trace Step b' c'}
    (firstAligned : Alignment Related first firstCopy)
    (secondAligned : Alignment Related second secondCopy) :
    Alignment Related (Trace.compose first second) (Trace.compose firstCopy secondCopy) := by
  induction firstAligned with
  | nil => exact secondAligned
  | cons related _ ih => exact .cons related (ih secondAligned)

structure Reproduction (Related : α → α → Prop) {x y : α}
    (original : Trace Step x y) (copyStart : α) where
  copyEnd : α
  copy : Trace Step copyStart copyEnd
  aligned : Alignment Related original copy

def Reproduction.append {a b c copyStart : α}
    {first : Trace Step a b} {second : Trace Step b c}
    (firstCopy : Reproduction Related first copyStart)
    (secondCopy : Reproduction Related second firstCopy.copyEnd) :
    Reproduction Related (Trace.compose first second) copyStart :=
  ⟨secondCopy.copyEnd, Trace.compose firstCopy.copy secondCopy.copy,
    firstCopy.aligned.compose secondCopy.aligned⟩

/-- Finite induction uses the supplied step operation, without classical choice. -/
def reproduce (transfer : StepTransfer Step Related) {x y : α}
    (original : Trace Step x y) (copyStart : α) (related : Related x copyStart) :
    Reproduction Related original copyStart :=
  match original with
  | .nil _ => ⟨copyStart, .nil copyStart, .nil related⟩
  | .cons edge tail =>
    let next := transfer related edge
    let rest := reproduce transfer tail next.val next.property.2
    ⟨rest.copyEnd, .cons next.property.1 rest.copy, .cons related rest.aligned⟩

/-- One fixed step operation reproduces concatenation coherently. Distinct
step operations need not choose the same copies. -/
theorem reproduce_compose (transfer : StepTransfer Step Related) {a b c : α}
    (first : Trace Step a b) (second : Trace Step b c) (copyStart : α)
    (related : Related a copyStart) :
    reproduce transfer (Trace.compose first second) copyStart related =
      let firstCopy := reproduce transfer first copyStart related
      firstCopy.append (reproduce transfer second firstCopy.copyEnd firstCopy.aligned.ends) := by
  induction first generalizing copyStart with
  | nil => rfl
  | cons edge tail ih =>
    exact congrArg (fun rest : Reproduction Related (Trace.compose tail second)
        (transfer related edge).val =>
      (⟨rest.copyEnd, .cons (transfer related edge).property.1 rest.copy,
        .cons related rest.aligned⟩ :
        Reproduction Related (Trace.compose (.cons edge tail) second) copyStart))
      (ih second _ _)

/-- The original suffix is stored alongside its reproduced copy, not overwritten. -/
structure Composition (Step Related : α → α → Prop) (a b c d : α) where
  first : Trace Step a b
  original : Trace Step c d
  reproduction : Reproduction Related original b

def composeAcross (transfer : StepTransfer Step Related) {a b c d : α}
    (first : Trace Step a b) (original : Trace Step c d) (boundary : Related c b) :
    Composition Step Related a b c d :=
  ⟨first, original, reproduce transfer original b boundary⟩

def Composition.path {a b c d : α} (certificate : Composition Step Related a b c d) :
    Trace Step a certificate.reproduction.copyEnd :=
  Trace.compose certificate.first certificate.reproduction.copy

theorem composed_length {a b c d : α} (certificate : Composition Step Related a b c d) :
    certificate.path.length = certificate.first.length + certificate.original.length := by
  rw [Composition.path, Trace.length_compose, certificate.reproduction.aligned.length_eq]

theorem composed_endpoint_related {a b c d : α}
    (certificate : Composition Step Related a b c d) :
    Related d certificate.reproduction.copyEnd := certificate.reproduction.aligned.ends

theorem composed_edges {a b c d : α} (certificate : Composition Step Related a b c d) :
    certificate.path.edges = certificate.first.edges ++ certificate.reproduction.copy.edges :=
  Trace.edges_compose _ _

/-- The certificate is retained in full, separately from the expanded execution path. -/
structure Layer (Step Related : α → α → Prop) (level : Nat) (a b c d : α) where
  certificate : Composition Step Related a b c d
  surface : PathLayers.Surface Step level a certificate.reproduction.copyEnd
  expands : PathLayers.expand level surface = certificate.path

def atLayer (level : Nat) {a b c d : α} (certificate : Composition Step Related a b c d) :
    Layer Step Related level a b c d :=
  ⟨certificate, PathLayers.promote level certificate.path, PathLayers.expand_promote _ _⟩

def raise (count : Nat) {level : Nat} {a b c d : α}
    (layer : Layer Step Related level a b c d) : Layer Step Related (level + count) a b c d :=
  ⟨layer.certificate, PathLayers.iterateLift count level layer.surface,
    (PathLayers.expand_iterateLift _ _ _).trans layer.expands⟩

theorem raise_retains_certificate (count : Nat) {level : Nat} {a b c d : α}
    (layer : Layer Step Related level a b c d) :
    (raise count layer).certificate = layer.certificate := rfl

theorem raise_recovers_surface (count : Nat) {level : Nat} {a b c d : α}
    (layer : Layer Step Related level a b c d) :
    PathLayers.recoverThrough count level (raise count layer).surface = some layer.surface :=
  PathLayers.recoverThrough_iterateLift _ _ _

theorem raise_preserves_path (count : Nat) {level : Nat} {a b c d : α}
    (layer : Layer Step Related level a b c d) :
    PathLayers.expand (level + count) (raise count layer).surface = layer.certificate.path :=
  (raise count layer).expands

/-- Exact missing law for one-for-one reproduction of guarded native forming steps.
It is a hypothesis, not an added axiom or a proved property of Simulation. -/
def NativeOneStepLaw : Prop :=
  ∀ {x copyStart : Form}, Simulation x copyStart → Congruent (f2f x) x →
    Congruent (f2f copyStart) copyStart ∧ Simulation (f2f x) (f2f copyStart)

noncomputable def nativeTransfer (law : NativeOneStepLaw) : StepTransfer DStep Simulation := by
  intro x y copyStart related edge
  have h := law related (edge.1 ▸ edge.2)
  refine ⟨f2f copyStart, ⟨rfl, h.1⟩, ?_⟩
  exact edge.1.symm ▸ h.2

theorem native_law_iff_transfer :
    NativeOneStepLaw ↔ Nonempty (StepTransfer DStep Simulation) := by
  constructor
  · intro law
    exact ⟨nativeTransfer law⟩
  · rintro ⟨transfer⟩ x copyStart related guard
    let next := transfer related (show DStep x (f2f x) from ⟨rfl, guard⟩)
    exact ⟨next.property.1.1 ▸ next.property.1.2,
      next.property.1.1 ▸ next.property.2⟩

namespace Checks

abbrev Point := Nat × Bool
def Next (x y : Point) : Prop := y = (x.1 + 1, x.2)
def SameHeight (x y : Point) : Prop := x.1 = y.1

def transfer : StepTransfer Next SameHeight := by
  intro x y copyStart related edge
  refine ⟨(copyStart.1 + 1, copyStart.2), rfl, ?_⟩
  subst y
  exact congrArg (fun n => n + 1) related

def first : Trace Next (0, false) (1, false) := .cons rfl (.nil _)
def original : Trace Next (1, true) (2, true) := .cons rfl (.nil _)
def certificate := composeAcross (Related := SameHeight) transfer first original rfl

theorem reproduced_copy_changes_endpoint :
    certificate.reproduction.copyEnd = (2, false) ∧
    certificate.reproduction.copy.edges = [((1, false), (2, false))] := ⟨rfl, rfl⟩

theorem original_and_copy_retained (count : Nat) :
    (raise count (atLayer 1 certificate)).certificate.original = original ∧
    PathLayers.expand (1 + count) (raise count (atLayer 1 certificate)).surface =
      certificate.path := ⟨rfl, raise_preserves_path _ _⟩

theorem path_preserves_component {x y : Point} (path : Trace Next x y) : y.2 = x.2 := by
  induction path with
  | nil => rfl
  | cons edge _ ih =>
    have tag := congrArg (fun (point : Point) => point.2) edge
    exact ih.trans tag

theorem related_without_connector :
    SameHeight (1, true) (1, false) ∧ ¬ Nonempty (Trace Next (1, true) (1, false)) := by
  refine ⟨rfl, ?_⟩
  rintro ⟨path⟩
  have impossible := path_preserves_component path
  cases impossible

/-- Even an equivalence relation need not preserve available steps. This is a
generic transition example, not a model of all native Hypermath assumptions. -/
def OneEdge (x y : Bool) : Prop := x = false ∧ y = true
def AllRelated (_ _ : Bool) : Prop := True

theorem relation_alone_insufficient : ¬ Nonempty (StepTransfer OneEdge AllRelated) := by
  rintro ⟨transport⟩
  let next := transport (x := false) (copyStart := true) True.intro
    (show OneEdge false true from ⟨rfl, rfl⟩)
  have impossible := next.property.1.1
  cases impossible

def probe : IO Unit := do
  IO.println "START path transport: distinct boundaries and witnessed reproduction"
  let layer := raise 4 (atLayer 1 certificate)
  unless layer.certificate.original.edges == [((1, true), (2, true))] do
    throw (IO.userError "original path was replaced")
  unless layer.certificate.reproduction.copy.edges == [((1, false), (2, false))] do
    throw (IO.userError "reproduced path lost its actual endpoints")
  unless (PathLayers.expand 5 layer.surface).edges ==
      [((0, false), (1, false)), ((1, false), (2, false))] do
    throw (IO.userError "composed path has a mismatched boundary")
  IO.println "PASS path transport: original, copy and exact composed path survive four lifts"

end Checks

end Hypermath.PathTransport
