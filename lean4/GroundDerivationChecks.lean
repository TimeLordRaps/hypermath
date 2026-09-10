import Hypermath.GroundDerivation

namespace Hypermath.GroundDerivationChecks

open GroundSyntax GroundDerivation

def exampleRecord : Record := quote (separation (.apply .ground))

theorem separation_checked (term : Term) :
    GroundDerivation.check (quote (separation term))
      (.both (.similar (.apply term) .ground) (.notSimulation (.apply term) .ground)) = true :=
  check_quote (separation term)

theorem composed_example_checked :
    GroundDerivation.check exampleRecord exampleRecord.conclusion = true := rfl

theorem wrong_claim_rejected :
    GroundDerivation.check exampleRecord (.notSimulation .ground .ground) = false := rfl

theorem wrong_predicate_premise_rejected :
    (Record.closeContinues (.apply .ground) (.primitive (.diff .ground))).valid = false := rfl

theorem wrong_argument_rejected :
    (Record.closeOrbits (.apply .ground) (.primitive (.box .ground))).valid = false := rfl

theorem nonconjunction_projection_rejected :
    (Record.projectLeft (.similar .ground .ground) (.similar .ground .ground)
      (.primitive .groundSelf)).valid = false := rfl

/-- The outer conjunction and its selected good child must not hide a bad premise. -/
def hiddenFailure : Record :=
  .join (.primitive .groundSelf)
    (.closeContinues (.apply .ground) (.primitive (.diff .ground)))

theorem projection_cannot_hide_failed_premise :
    (Record.projectLeft (.structural (.continues .ground .ground))
      (.similar (.apply .ground) .ground) hiddenFailure).valid = false := rfl

theorem invalid_record_not_reconstructed : reconstruct hiddenFailure = none := rfl

theorem wrong_projection_annotation_rejected :
    (Record.projectRight (.similar .ground .ground) (.notSimulation .ground .ground)
      exampleRecord).valid = false := rfl

theorem repeated_record_can_be_joined :
    (Record.join exampleRecord exampleRecord).valid = true := rfl

theorem good_projection_checked :
    GroundDerivation.check
      (.projectLeft (.similar (.apply (.apply .ground)) .ground)
        (.notSimulation (.apply (.apply .ground)) .ground) exampleRecord)
      (.similar (.apply (.apply .ground)) .ground) = true := rfl

end Hypermath.GroundDerivationChecks

#print axioms Hypermath.GroundDerivation.derivation_sound
#print axioms Hypermath.GroundDerivation.check_iff
#print axioms Hypermath.GroundDerivation.Record.derive
#print axioms Hypermath.GroundDerivation.check_sound
#print axioms Hypermath.GroundDerivation.conclusion_quote
#print axioms Hypermath.GroundDerivation.valid_quote
#print axioms Hypermath.GroundDerivation.check_quote
#print axioms Hypermath.GroundDerivation.quote_derive
#print axioms Hypermath.GroundDerivation.observe_derive
#print axioms Hypermath.GroundDerivation.reconstruct
#print axioms Hypermath.GroundDerivation.reconstruct_retains_record
#print axioms Hypermath.GroundDerivation.represented_iff_derivable
#print axioms Hypermath.GroundDerivation.check_join_iff
#print axioms Hypermath.GroundDerivation.separation
#print axioms Hypermath.GroundDerivation.native_check_sound
#print axioms Hypermath.GroundDerivationChecks.separation_checked
#print axioms Hypermath.GroundDerivationChecks.composed_example_checked
#print axioms Hypermath.GroundDerivationChecks.wrong_claim_rejected
#print axioms Hypermath.GroundDerivationChecks.wrong_predicate_premise_rejected
#print axioms Hypermath.GroundDerivationChecks.wrong_argument_rejected
#print axioms Hypermath.GroundDerivationChecks.nonconjunction_projection_rejected
#print axioms Hypermath.GroundDerivationChecks.projection_cannot_hide_failed_premise
#print axioms Hypermath.GroundDerivationChecks.invalid_record_not_reconstructed
#print axioms Hypermath.GroundDerivationChecks.wrong_projection_annotation_rejected
#print axioms Hypermath.GroundDerivationChecks.repeated_record_can_be_joined
#print axioms Hypermath.GroundDerivationChecks.good_projection_checked
