import Hypermath.Trace

/-!
# Observation boundaries for finite traces

An observation preserved by every justified edge is preserved across a trace.
Endpoint observations need not retain path-dependent data: two traces with the
same endpoints and different structural lengths rule out an endpoint-only
length decoder. These are generic results, with no native `Form` or transfinite
interpretation assumed.
-/

universe u v

namespace Hypermath.Observation

variable {α : Type u} {β : Type v} {Step : α → α → Prop}

/-- An invariant of each edge is an invariant of the full finite trace. -/
theorem endpoints_eq_of_step (observe : α → β)
    (preserves : ∀ {x y}, Step x y → observe x = observe y)
    {x y : α} (trace : Trace Step x y) : observe x = observe y := by
  induction trace with
  | nil => rfl
  | cons edge tail ih => exact (preserves edge).trans ih

/-- A function of the endpoint pair has only one output for both traces. -/
theorem endpoint_decoder_cannot_recover_distinct_lengths {x y : α}
    (first second : Trace Step x y) (different : first.length ≠ second.length) :
    ¬ ∃ decoder : α → α → Nat,
      decoder x y = first.length ∧ decoder x y = second.length := by
  intro ⟨decoder, firstValue, secondValue⟩
  exact different (firstValue.symm.trans secondValue)

/-- A single pair of equal-endpoint traces with unequal lengths obstructs a
length decoder for all traces that receives only their endpoints. -/
theorem no_endpoint_length_decoder {x y : α}
    (first second : Trace Step x y) (different : first.length ≠ second.length) :
    ¬ ∃ decoder : α → α → Nat,
      ∀ {a b : α} (trace : Trace Step a b), decoder a b = trace.length := by
  intro ⟨decoder, correct⟩
  exact endpoint_decoder_cannot_recover_distinct_lengths first second different
    ⟨decoder, correct first, correct second⟩

end Hypermath.Observation
