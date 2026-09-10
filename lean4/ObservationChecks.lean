import Hypermath.Observation

/-!
Concrete finite witnesses for observation preservation and information loss.
The observed natural-number coordinate is invariant while a Boolean coordinate
toggles. Empty and positive closed traces share exactly the same endpoints.
-/

namespace Hypermath.ObservationChecks

abbrev ToggleStep (x y : Nat × Bool) : Prop :=
  x.1 = y.1 ∧ y.2 = !x.2

def empty : Trace ToggleStep (7, false) (7, false) := .nil (7, false)

def closed : Trace ToggleStep (7, false) (7, false) :=
  .cons (y := (7, true)) ⟨rfl, rfl⟩
    (.cons (y := (7, false)) ⟨rfl, rfl⟩ (.nil (7, false)))

theorem observation_preserved {x y : Nat × Bool} (trace : Trace ToggleStep x y) :
    x.1 = y.1 :=
  Observation.endpoints_eq_of_step Prod.fst (fun edge => edge.1) trace

theorem empty_length : empty.length = 0 := rfl

theorem closed_length : closed.length = 2 := rfl

theorem closed_positive : 0 < closed.length := Nat.zero_lt_succ 1

theorem distinct_lengths : empty.length ≠ closed.length := by
  intro sameLength
  exact Nat.noConfusion sameLength

theorem pair_decoder_rejected :
    ¬ ∃ decoder : (Nat × Bool) → (Nat × Bool) → Nat,
      decoder (7, false) (7, false) = empty.length ∧
      decoder (7, false) (7, false) = closed.length :=
  Observation.endpoint_decoder_cannot_recover_distinct_lengths empty closed distinct_lengths

theorem universal_decoder_rejected :
    ¬ ∃ decoder : (Nat × Bool) → (Nat × Bool) → Nat,
      ∀ {x y : Nat × Bool} (trace : Trace ToggleStep x y),
        decoder x y = trace.length :=
  Observation.no_endpoint_length_decoder empty closed distinct_lengths

/-- Retaining the actual trace retains both computed lengths. -/
theorem whole_trace_retains_lengths : (empty.length, closed.length) = (0, 2) := rfl

def reused : TraceExpr ToggleStep (7, false) (7, false) :=
  .seq (.atom closed) (.atom closed)

theorem reused_length : reused.expand.length = 4 := rfl

theorem reused_preserves_length : reused.expand.length = reused.length :=
  TraceExpr.length_expand reused

end Hypermath.ObservationChecks

#print axioms Hypermath.Observation.endpoints_eq_of_step
#print axioms Hypermath.Observation.endpoint_decoder_cannot_recover_distinct_lengths
#print axioms Hypermath.Observation.no_endpoint_length_decoder
#print axioms Hypermath.ObservationChecks.observation_preserved
#print axioms Hypermath.ObservationChecks.empty_length
#print axioms Hypermath.ObservationChecks.closed_length
#print axioms Hypermath.ObservationChecks.closed_positive
#print axioms Hypermath.ObservationChecks.distinct_lengths
#print axioms Hypermath.ObservationChecks.pair_decoder_rejected
#print axioms Hypermath.ObservationChecks.universal_decoder_rejected
#print axioms Hypermath.ObservationChecks.whole_trace_retains_lengths
#print axioms Hypermath.ObservationChecks.reused_length
#print axioms Hypermath.ObservationChecks.reused_preserves_length
