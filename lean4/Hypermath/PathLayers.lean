import Hypermath.Sequential
import Hypermath.L3Ordinatics

/-!
# Finite representation layers over witnessed derivation paths

A higher atom contains an entire lower path expression, with both endpoints
in its type. This uses Lean's inductive types as representation infrastructure.
The native specialization starts from actual DEntry witnesses; it does not
postulate any new native edge or identify these constructors with f2f.
-/

namespace Hypermath.PathLayers

/-- Unlike an existence proposition, the atom carries the supplied value. -/
inductive Expression {α : Type} (Atom : α → α → Type) : α → α → Type where
  | atom {x y : α} (value : Atom x y) : Expression Atom x y
  | self (x : α) : Expression Atom x x
  | seq {x y z : α} (first : Expression Atom x y) (second : Expression Atom y z) :
      Expression Atom x z

variable {α : Type} {Step : α → α → Prop}

def Surface (Step : α → α → Prop) : Nat → α → α → Type
  | 0 => Trace Step
  | layer + 1 => Expression (Surface Step layer)

def identity (layer : Nat) (x : α) : Surface Step layer x x :=
  match layer with
  | 0 => Trace.nil x
  | _ + 1 => Expression.self x

def compose (layer : Nat) {x y z : α}
    (first : Surface Step layer x y) (second : Surface Step layer y z) : Surface Step layer x z :=
  match layer with
  | 0 => Trace.compose first second
  | _ + 1 => Expression.seq first second

def Expression.expand {Atom : α → α → Type}
    (onAtom : ∀ {x y}, Atom x y → Trace Step x y)
    {x y : α} : Expression Atom x y → Trace Step x y
  | .atom value => onAtom value
  | .self x => Trace.nil x
  | .seq first second => Trace.compose (first.expand onAtom) (second.expand onAtom)

def expand : (layer : Nat) → {x y : α} → Surface Step layer x y → Trace Step x y
  | 0, _, _, path => path
  | layer + 1, _, _, expression => expression.expand (expand layer)

theorem expand_identity (layer : Nat) (x : α) :
    expand layer (identity (Step := Step) layer x) = Trace.nil x := by
  cases layer <;> rfl

theorem expand_compose (layer : Nat) {x y z : α}
    (first : Surface Step layer x y) (second : Surface Step layer y z) :
    expand layer (compose layer first second) =
      Trace.compose (expand layer first) (expand layer second) := by
  cases layer <;> rfl

def lift (layer : Nat) {x y : α} (surface : Surface Step layer x y) :
    Surface Step (layer + 1) x y := Expression.atom surface

def lowerAtom (layer : Nat) {x y : α} :
    Surface Step (layer + 1) x y → Option (Surface Step layer x y)
  | .atom value => some value
  | .self _ => none
  | .seq _ _ => none

theorem lowerAtom_lift (layer : Nat) {x y : α} (surface : Surface Step layer x y) :
    lowerAtom layer (lift layer surface) = some surface := rfl

theorem expand_lift (layer : Nat) {x y : α} (surface : Surface Step layer x y) :
    expand (layer + 1) (lift layer surface) = expand layer surface := rfl

def iterateLift : (count layer : Nat) → {x y : α} →
    Surface Step layer x y → Surface Step (layer + count) x y
  | 0, _, _, _, surface => surface
  | count + 1, layer, _, _, surface => lift (layer + count) (iterateLift count layer surface)

def recoverThrough : (count layer : Nat) → {x y : α} →
    Surface Step (layer + count) x y → Option (Surface Step layer x y)
  | 0, _, _, _, surface => some surface
  | count + 1, layer, _, _, surface => do
      let lower ← lowerAtom (layer + count) surface
      recoverThrough count layer lower

theorem recoverThrough_iterateLift (count layer : Nat) {x y : α}
    (surface : Surface Step layer x y) :
    recoverThrough count layer (iterateLift count layer surface) = some surface := by
  induction count with
  | zero => rfl
  | succ count ih => simp [iterateLift, recoverThrough, lowerAtom_lift, ih]

theorem expand_iterateLift (count layer : Nat) {x y : α}
    (surface : Surface Step layer x y) :
    expand (layer + count) (iterateLift count layer surface) = expand layer surface := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

/-- Both the grouped representation and its exact evidenced base path survive. -/
theorem composition_lift_preserves (count layer : Nat) {x y z : α}
    (first : Surface Step layer x y) (second : Surface Step layer y z) :
    recoverThrough count layer (iterateLift count layer (compose layer first second)) =
        some (compose layer first second) ∧
    expand (layer + count) (iterateLift count layer (compose layer first second)) =
      Trace.compose (expand layer first) (expand layer second) :=
  ⟨recoverThrough_iterateLift _ _ _, (expand_iterateLift _ _ _).trans (expand_compose _ _ _)⟩

theorem composed_edges_preserved (count layer : Nat) {x y z : α}
    (first : Surface Step layer x y) (second : Surface Step layer y z) :
    (expand (layer + count) (iterateLift count layer (compose layer first second))).edges =
      (expand layer first).edges ++ (expand layer second).edges := by
  rw [(composition_lift_preserves count layer first second).2, Trace.edges_compose]

theorem composed_length_preserved (count layer : Nat) {x y z : α}
    (first : Surface Step layer x y) (second : Surface Step layer y z) :
    (expand (layer + count) (iterateLift count layer (compose layer first second))).length =
      (expand layer first).length + (expand layer second).length := by
  rw [(composition_lift_preserves count layer first second).2, Trace.length_compose]

/-- All paths compose only at matching endpoints. Loops at one endpoint form
the shared monoid interface under equality of their expanded witnessed paths. -/
def loopSequencing (layer : Nat) (x : α) : Sequential.Sequencing (Surface Step layer x x)
    (fun first second => expand layer first = expand layer second) where
  equivalence := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
  operation := compose layer
  unit := identity layer x
  respects := by
    intro p p' q q' hp hq
    simp only [expand_compose, hp, hq]
  identity := fun path => by
    simp [expand_compose, expand_identity]
  associative := fun p q r => by
    simp only [expand_compose]
    exact Trace.compose_assoc _ _ _

def loopLiftMap (layer : Nat) (x : α) :
    Sequential.CompositionMap (loopSequencing (Step := Step) layer x)
      (loopSequencing (Step := Step) (layer + 1) x) where
  toFun := lift layer
  respects := fun same => same
  preserves_unit := expand_identity layer x
  preserves_operation := fun first second => expand_compose layer first second

def promote : (layer : Nat) → {x y : α} → Trace Step x y → Surface Step layer x y
  | 0, _, _, path => path
  | layer + 1, _, _, path => lift layer (promote layer path)

theorem expand_promote (layer : Nat) {x y : α} (path : Trace Step x y) :
    expand layer (promote layer path) = path := by
  induction layer with
  | zero => rfl
  | succ layer ih => exact ih

/-- Wrapping changes representation, not which base endpoints are reachable. -/
theorem nonempty_iff_base (layer : Nat) (x y : α) :
    Nonempty (Surface Step layer x y) ↔ Nonempty (Trace Step x y) :=
  ⟨fun ⟨surface⟩ => ⟨expand layer surface⟩, fun ⟨path⟩ => ⟨promote layer path⟩⟩

theorem no_steps_remains_empty (noSteps : ∀ x y : α, ¬ Step x y)
    (layer : Nat) {x y : α} (surface : Surface Step layer x y) :
    (expand layer surface).length = 0 ∧ x = y := by
  cases expand layer surface with
  | nil => exact ⟨rfl, rfl⟩
  | cons edge tail => exact False.elim (noSteps _ _ edge)

abbrev NativeSurface (layer : Nat) (x y : Form) := Surface DStep layer x y

theorem native_reachability_iff (layer : Nat) (x y : Form) :
    Nonempty (NativeSurface layer x y) ↔ D x y := nonempty_iff_base layer x y

theorem native_endpoint_preserved (layer : Nat) {x y : Form} (surface : NativeSurface layer x y) :
    Nat.repeat f2f (expand layer surface).length x = y :=
  dEntryEndpointIteration (expand layer surface)

theorem native_composition_lift_preserves (count layer : Nat) {x y z : Form}
    (first : NativeSurface layer x y) (second : NativeSurface layer y z) :
    recoverThrough count layer (iterateLift count layer (compose layer first second)) =
        some (compose layer first second) ∧
    expand (layer + count) (iterateLift count layer (compose layer first second)) =
      dEntryCompose (expand layer first) (expand layer second) :=
  composition_lift_preserves count layer first second

theorem native_without_steps (noSteps : ∀ x y : Form, ¬ DStep x y)
    (layer : Nat) {x y : Form} (surface : NativeSurface layer x y) :
    (expand layer surface).length = 0 ∧ x = y := no_steps_remains_empty noSteps layer surface

/-- A supplied stronger cycle certificate retains both actual steps at every
finite layer. This theorem supplies no inhabitant of DriverCycleWitness. -/
theorem cycle_witness_length_preserved (layer : Nat) (witness : DriverCycleWitness) :
    (expand layer (promote layer (simulationEntryToDEntry witness.path))).length = 2 := by
  rw [expand_promote, simulationEntryToDEntry_length, witness.length_two]

/-- Keep the stronger simulation path and its relational closure together.
Closure by Simulation is not an equality of the endpoint indices. -/
structure CycleSurface (layer : Nat) where
  path : Surface SimulationStep layer deriver (f2f (f2f deriver))
  length_two : (expand layer path).length = 2
  closes : driverCycleClaim

noncomputable def reifyCycle (layer : Nat) (witness : DriverCycleWitness) : CycleSurface layer :=
  ⟨promote layer witness.path, by rw [expand_promote, witness.length_two], witness.closes⟩

noncomputable def recoverCycle (layer : Nat) (surface : CycleSurface layer) : DriverCycleWitness :=
  ⟨expand layer surface.path, surface.length_two, surface.closes⟩

theorem recoverCycle_reifyCycle (layer : Nat) (witness : DriverCycleWitness) :
    recoverCycle layer (reifyCycle layer witness) = witness := by
  cases witness
  simp only [recoverCycle, reifyCycle, expand_promote]

theorem cycle_surface_iff_witness (layer : Nat) :
    Nonempty (CycleSurface layer) ↔ Nonempty DriverCycleWitness :=
  ⟨fun ⟨surface⟩ => ⟨recoverCycle layer surface⟩, fun ⟨witness⟩ => ⟨reifyCycle layer witness⟩⟩

namespace Checks

def Forward (x y : Nat) : Prop := y = x + 1
def first : Trace Forward 0 1 := .cons rfl (.nil 1)
def second : Trace Forward 1 2 := .cons rfl (.nil 2)

theorem two_steps_retained (count : Nat) :
    (expand (0 + count) (iterateLift count 0 (compose 0 first second))).edges = [(0, 1), (1, 2)] := by
  rw [composed_edges_preserved]
  rfl

theorem nested_paths_recovered (count : Nat) :
    recoverThrough count 1
      (iterateLift count 1 (compose 1 (lift 0 first) (lift 0 second))) =
      some (compose 1 (lift 0 first) (lift 0 second)) := recoverThrough_iterateLift _ _ _

theorem grouping_remains_distinct :
    lift 0 (compose 0 first second) ≠ compose 1 (lift 0 first) (lift 0 second) := by
  intro impossible
  cases impossible

theorem grouping_has_same_path :
    expand 1 (lift 0 (compose 0 first second)) =
      expand 1 (compose 1 (lift 0 first) (lift 0 second)) := rfl

def probe : IO Unit := do
  IO.println "START path layers: actual endpoints and nested witnesses"
  let raised := iterateLift 4 1 (compose 1 (lift 0 first) (lift 0 second))
  unless (expand 5 raised).edges == [(0, 1), (1, 2)] do
    throw (IO.userError "nested path lost a boundary or edge")
  unless (expand 5 raised).length == 2 do
    throw (IO.userError "wrapping changed the native-edge count")
  IO.println "PASS path layers: both boundaries and two witnessed edges retained"

end Checks

end Hypermath.PathLayers
