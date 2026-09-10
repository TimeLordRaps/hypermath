import Hypermath.Trace

/-!
Kernel-checked finite examples and boundary claims for `Hypermath.Trace`.
These exercise constructive infrastructure, not native Form adequacy or
transfinite arithmetic. Every named theorem below reports its dependencies.
-/

namespace Hypermath.TraceChecks

abbrev NatStep (x y : Nat) : Prop := y = x + 1

def twoSteps : Trace NatStep 0 2 :=
  .cons rfl (.cons rfl (.nil 2))

def thirdStep : Trace NatStep 2 3 := .cons rfl (.nil 3)

theorem twoSteps_length : twoSteps.length = 2 := rfl

theorem twoSteps_edges : twoSteps.edges = [(0, 1), (1, 2)] := rfl

theorem composed_length : (twoSteps.compose thirdStep).length = 3 := rfl

theorem composed_edges :
    (twoSteps.compose thirdStep).edges = [(0, 1), (1, 2), (2, 3)] := rfl

abbrev PairStep (a b : Nat × Nat) : Prop :=
  b.1 = a.1 + 1 ∧ b.2 = a.2 + 1

def pairTrace : Trace PairStep (0, 0) (2, 2) :=
  Trace.map (fun n => (n, n)) (fun h => ⟨h, h⟩) twoSteps

theorem mapped_length : pairTrace.length = 2 := rfl

theorem mapped_edges :
    pairTrace.edges = [((0, 0), (1, 1)), ((1, 1), (2, 2))] := rfl

def closedTrace : Trace (fun (_ _ : Nat) => True) 0 0 :=
  .cons (y := 1) True.intro (.cons (y := 0) True.intro (.nil 0))

/-- Reuse the same evidenced closed trace on either side of a self expression. -/
def reused : TraceExpr (fun (_ _ : Nat) => True) 0 0 :=
  .seq (.atom closedTrace) (.seq (.self 0) (.atom closedTrace))

theorem reused_length : reused.expand.length = 4 := rfl

theorem reused_edges :
    reused.expand.edges = [(0, 1), (1, 0), (0, 1), (1, 0)] := rfl

/-- Empty traces cannot change endpoints; a nonempty one needs edge evidence. -/
theorem absent_edge_rejected :
    ¬ Nonempty (Trace (fun (_ _ : Nat) => False) 0 1) := by
  intro ⟨trace⟩
  cases trace with
  | cons edge _ => exact edge

/-- Every successor-edge trace respects the numerical order of its endpoints. -/
theorem successor_trace_monotone {x y : Nat} (trace : Trace NatStep x y) : x ≤ y := by
  induction trace with
  | nil x => exact Nat.le_refl x
  | @cons x y z edge tail ih =>
    exact Nat.le_trans (edge.symm ▸ Nat.le_succ x) ih

/-- The end of `twoSteps` cannot be connected back to its start by successor edges.
Composition itself additionally requires matching middle endpoints by type. -/
theorem missing_return_rejected : ¬ Nonempty (Trace NatStep 2 0) := by
  intro ⟨trace⟩
  exact Nat.not_succ_le_zero 1 (successor_trace_monotone trace)

end Hypermath.TraceChecks

#print axioms Hypermath.Trace.nil_compose
#print axioms Hypermath.Trace.compose_nil
#print axioms Hypermath.Trace.compose_assoc
#print axioms Hypermath.Trace.length_nil
#print axioms Hypermath.Trace.length_cons
#print axioms Hypermath.Trace.length_compose
#print axioms Hypermath.Trace.edges_compose
#print axioms Hypermath.Trace.edges_length
#print axioms Hypermath.Trace.map_nil
#print axioms Hypermath.Trace.map_compose
#print axioms Hypermath.Trace.length_map
#print axioms Hypermath.Trace.edges_map
#print axioms Hypermath.TraceExpr.expand_atom
#print axioms Hypermath.TraceExpr.expand_self
#print axioms Hypermath.TraceExpr.expand_seq
#print axioms Hypermath.TraceExpr.length_expand
#print axioms Hypermath.TraceExpr.edges_expand_seq
#print axioms Hypermath.TraceChecks.twoSteps_length
#print axioms Hypermath.TraceChecks.twoSteps_edges
#print axioms Hypermath.TraceChecks.composed_length
#print axioms Hypermath.TraceChecks.composed_edges
#print axioms Hypermath.TraceChecks.mapped_length
#print axioms Hypermath.TraceChecks.mapped_edges
#print axioms Hypermath.TraceChecks.reused_length
#print axioms Hypermath.TraceChecks.reused_edges
#print axioms Hypermath.TraceChecks.absent_edge_rejected
#print axioms Hypermath.TraceChecks.successor_trace_monotone
#print axioms Hypermath.TraceChecks.missing_return_rejected
