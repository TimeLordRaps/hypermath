import Hypermath.OperationalCorrespondence

/-!
# Retained terminal states and merging concrete orbits

Under the earlier total correspondence law, a completed abstract state stays
decoded as that same state under further concrete steps. Two concrete orbits
that meet therefore cannot retain different completed states. This constrains
that specific execution protocol, not stopped or guarded native protocols.
-/

namespace Hypermath.TerminalRetention

open OperationalCorrespondence GroundDerivation RecordMachine

universe u v

theorem run_fixed {C : Type u} (step : C → C) (value : C) (fixed : step value = value)
    (count : Nat) : run step count value = value := by
  induction count with
  | zero => rfl
  | succ count ih => simpa [run, fixed] using ih

/-- The actual reached representations need not be canonical encodings. -/
theorem merged_fixed_states {C : Type u} {N : Type v} (view : Representation C N)
    (abstract : C → C) (concrete : N → N) (correct : Respects view abstract concrete)
    (first second : N) (left right : C)
    (decodedLeft : view.decode first = some left)
    (decodedRight : view.decode second = some right)
    (fixedLeft : abstract left = left) (fixedRight : abstract right = right)
    (firstCount secondCount : Nat)
    (meet : run concrete firstCount first = run concrete secondCount second) : left = right := by
  have firstResult := run_decodes view abstract concrete correct firstCount first left decodedLeft
  have secondResult := run_decodes view abstract concrete correct secondCount second right decodedRight
  rw [run_fixed abstract left fixedLeft] at firstResult
  rw [run_fixed abstract right fixedRight] at secondResult
  exact Option.some.inj (firstResult.symm.trans ((congrArg view.decode meet).trans secondResult))

/-- Finished means that execution exhausted the program; the record can still
be rejected. The original record, claim, and canonical history remain data. -/
def finished (record : Record) (claim : Formula) : Frame :=
  run Frame.advance (program record).length (Frame.initial record claim)

theorem finished_record (record : Record) (claim : Formula) :
    (finished record claim).record = record := by
  simp [finished, Frame.initial, run_frame]

theorem finished_fixed (record : Record) (claim : Formula) :
    Frame.advance (finished record claim) = finished record claim := by
  rw [finished, Frame.initial, run_frame]
  rfl

theorem finished_check (record : Record) (claim : Formula) :
    (finished record claim).accept = GroundDerivation.check record claim :=
  accept_run_initial record claim

end Hypermath.TerminalRetention
