import Init

/-!
# Constructive finite traces

`Trace Step x y` records a finite sequence of justified `Step` edges from `x`
to `y`. Its length is computed from that sequence, never supplied as a label.
The definitions are generic infrastructure: they do not identify traces or
their reusable expressions with native `Form` objects or transfinite paths.
-/

universe u v

namespace Hypermath

/-- A finite, endpoint-indexed sequence of edges carrying their evidence. -/
inductive Trace {α : Type u} (Step : α → α → Prop) : α → α → Type u where
  | nil (x : α) : Trace Step x x
  | cons {x y z : α} (edge : Step x y) (tail : Trace Step y z) : Trace Step x z

namespace Trace

variable {α : Type u} {β : Type v}
variable {Step : α → α → Prop} {Step' : β → β → Prop}

/-- Traverse the first trace and then the second; endpoints must match. -/
def compose {x y z : α} (first : Trace Step x y) (second : Trace Step y z) :
    Trace Step x z :=
  match first with
  | .nil _ => second
  | .cons edge tail => .cons edge (compose tail second)

@[simp] theorem nil_compose {x y : α} (trace : Trace Step x y) :
    compose (.nil x) trace = trace := rfl

@[simp] theorem compose_nil {x y : α} (trace : Trace Step x y) :
    compose trace (.nil y) = trace := by
  induction trace with
  | nil => rfl
  | cons edge tail ih => exact congrArg (Trace.cons edge) ih

theorem compose_assoc {w x y z : α}
    (first : Trace Step w x) (second : Trace Step x y) (third : Trace Step y z) :
    compose (compose first second) third = compose first (compose second third) := by
  induction first with
  | nil => rfl
  | cons edge tail ih => exact congrArg (Trace.cons edge) (ih second)

/-- The actual number of recorded edges. -/
def length {x y : α} : Trace Step x y → Nat
  | .nil _ => 0
  | .cons _ tail => length tail + 1

@[simp] theorem length_nil (x : α) : length (Trace.nil (Step := Step) x) = 0 := rfl

@[simp] theorem length_cons {x y z : α} (edge : Step x y) (tail : Trace Step y z) :
    length (.cons edge tail) = length tail + 1 := rfl

@[simp] theorem length_compose {x y z : α}
    (first : Trace Step x y) (second : Trace Step y z) :
    length (compose first second) = length first + length second := by
  induction first with
  | nil => exact (Nat.zero_add _).symm
  | cons edge tail ih =>
    exact (congrArg Nat.succ (ih second)).trans (Nat.add_right_comm _ _ 1)

/-- Recorded endpoint pairs, forgetting only the edge proofs. -/
def edges {x y : α} : Trace Step x y → List (α × α)
  | .nil _ => []
  | .cons (x := x) (y := y) _ tail => (x, y) :: edges tail

@[simp] theorem edges_compose {x y z : α}
    (first : Trace Step x y) (second : Trace Step y z) :
    edges (compose first second) = edges first ++ edges second := by
  induction first with
  | nil => rfl
  | cons edge tail ih => exact congrArg (List.cons _) (ih second)

@[simp] theorem edges_length {x y : α} (trace : Trace Step x y) :
    (edges trace).length = length trace := by
  induction trace with
  | nil => rfl
  | cons edge tail ih => exact congrArg Nat.succ ih

/-- Transport a trace by a vertex map and an explicit preservation of every edge. -/
def map (f : α → β) (onStep : ∀ {x y}, Step x y → Step' (f x) (f y))
    {x y : α} : Trace Step x y → Trace Step' (f x) (f y)
  | .nil x => .nil (f x)
  | .cons edge tail => .cons (onStep edge) (map f onStep tail)

@[simp] theorem map_nil (f : α → β)
    (onStep : ∀ {x y}, Step x y → Step' (f x) (f y)) (x : α) :
    map f onStep (.nil x) = .nil (f x) := rfl

@[simp] theorem map_compose (f : α → β)
    (onStep : ∀ {x y}, Step x y → Step' (f x) (f y))
    {x y z : α} (first : Trace Step x y) (second : Trace Step y z) :
    map f onStep (compose first second) =
      compose (map f onStep first) (map f onStep second) := by
  induction first with
  | nil => rfl
  | cons edge tail ih => exact congrArg (Trace.cons (onStep edge)) (ih second)

@[simp] theorem length_map (f : α → β)
    (onStep : ∀ {x y}, Step x y → Step' (f x) (f y))
    {x y : α} (trace : Trace Step x y) :
    length (map f onStep trace) = length trace := by
  induction trace with
  | nil => rfl
  | cons edge tail ih => exact congrArg Nat.succ ih

@[simp] theorem edges_map (f : α → β)
    (onStep : ∀ {x y}, Step x y → Step' (f x) (f y))
    {x y : α} (trace : Trace Step x y) :
    edges (map f onStep trace) = (edges trace).map (fun edge => (f edge.1, f edge.2)) := by
  induction trace with
  | nil => rfl
  | cons edge tail ih => exact congrArg (List.cons _) ih

end Trace

/-- Finite reusable trace expressions, not a reification into native `Form`.
An atom carries an existing trace; sequencing preserves the endpoint contract. -/
inductive TraceExpr {α : Type u} (Step : α → α → Prop) : α → α → Type u where
  | atom {x y : α} (trace : Trace Step x y) : TraceExpr Step x y
  | self (x : α) : TraceExpr Step x x
  | seq {x y z : α} (first : TraceExpr Step x y) (second : TraceExpr Step y z) :
      TraceExpr Step x z

namespace TraceExpr

variable {α : Type u} {Step : α → α → Prop}

/-- Expand reusable atoms and sequencing into their evidenced trace. -/
def expand {x y : α} : TraceExpr Step x y → Trace Step x y
  | .atom trace => trace
  | .self x => .nil x
  | .seq first second => Trace.compose (expand first) (expand second)

@[simp] theorem expand_atom {x y : α} (trace : Trace Step x y) :
    expand (.atom trace) = trace := rfl

@[simp] theorem expand_self (x : α) :
    expand (TraceExpr.self (Step := Step) x) = .nil x := rfl

@[simp] theorem expand_seq {x y z : α}
    (first : TraceExpr Step x y) (second : TraceExpr Step y z) :
    expand (.seq first second) = Trace.compose (expand first) (expand second) := rfl

/-- A compositional edge-count observation, extracted from the actual atoms. -/
def length {x y : α} : TraceExpr Step x y → Nat
  | .atom trace => trace.length
  | .self _ => 0
  | .seq first second => length first + length second

@[simp] theorem length_expand {x y : α} (expression : TraceExpr Step x y) :
    expression.expand.length = expression.length := by
  induction expression with
  | atom trace => rfl
  | self x => rfl
  | seq first second ihFirst ihSecond =>
    exact (Trace.length_compose first.expand second.expand).trans
      ((congrArg (fun n => n + second.expand.length) ihFirst).trans
        (congrArg (fun n => first.length + n) ihSecond))

/-- Expansion preserves the full sequence of edge endpoints across sequencing. -/
theorem edges_expand_seq {x y z : α}
    (first : TraceExpr Step x y) (second : TraceExpr Step y z) :
    (expand (.seq first second)).edges = first.expand.edges ++ second.expand.edges :=
  Trace.edges_compose first.expand second.expand

end TraceExpr

end Hypermath
