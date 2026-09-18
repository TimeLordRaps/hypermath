import Hypermath.GroundSyntax

namespace Hypermath.GroundSyntaxChecks

open GroundSyntax

def exampleProof : AxiomInstance := .box (.apply (.apply .ground))

theorem concrete_record_roundtrip : decode (encode exampleProof) = some exampleProof := rfl

theorem concrete_conclusion_checked : check (encode exampleProof) exampleProof.conclusion = true := rfl

theorem wrong_claim_rejected :
    check (encode (.diff .ground)) (.distinct .ground .ground) = false := rfl

theorem wrong_argument_rejected :
    check (encode (.diff (.apply .ground))) (.diff .ground : AxiomInstance).conclusion = false := rfl

theorem wrong_rule_rejected :
    check (encode (.diff .ground)) (.box .ground : AxiomInstance).conclusion = false := rfl

theorem malformed_record_rejected (claimed : Statement) :
    check (Term.ofDepth 4) claimed = false := rfl

theorem longer_malformed_record_rejected (claimed : Statement) :
    check (Term.ofDepth 12) claimed = false := rfl

theorem distinct_records_retained : encode (.diff .ground) ≠ encode (.box .ground) := by
  intro same
  exact AxiomInstance.noConfusion (encode_injective same)

theorem reused_record_checked :
    (reuseMany 3 (encode (.diff .ground))).map
      (fun record => check record (.diff (Term.ofDepth 3) : AxiomInstance).conclusion) =
      some true := rfl

theorem malformed_reuse_rejected : reuse (Term.ofDepth 4) = none := rfl

end Hypermath.GroundSyntaxChecks

#print axioms Hypermath.GroundSyntax.Term.depth_ofDepth
#print axioms Hypermath.GroundSyntax.Term.ofDepth_depth
#print axioms Hypermath.GroundSyntax.Term.interpret_ofDepth
#print axioms Hypermath.GroundSyntax.decode_encode
#print axioms Hypermath.GroundSyntax.encode_injective
#print axioms Hypermath.GroundSyntax.observe_encode
#print axioms Hypermath.GroundSyntax.check_encode
#print axioms Hypermath.GroundSyntax.reuse_encode
#print axioms Hypermath.GroundSyntax.reuse_many_encode
#print axioms Hypermath.GroundSyntax.check_iff
#print axioms Hypermath.GroundSyntax.instance_sound
#print axioms Hypermath.GroundSyntax.check_sound
#print axioms Hypermath.GroundSyntax.native_check_sound
#print axioms Hypermath.GroundSyntaxChecks.concrete_record_roundtrip
#print axioms Hypermath.GroundSyntaxChecks.concrete_conclusion_checked
#print axioms Hypermath.GroundSyntaxChecks.wrong_claim_rejected
#print axioms Hypermath.GroundSyntaxChecks.wrong_argument_rejected
#print axioms Hypermath.GroundSyntaxChecks.wrong_rule_rejected
#print axioms Hypermath.GroundSyntaxChecks.malformed_record_rejected
#print axioms Hypermath.GroundSyntaxChecks.longer_malformed_record_rejected
#print axioms Hypermath.GroundSyntaxChecks.distinct_records_retained
#print axioms Hypermath.GroundSyntaxChecks.reused_record_checked
#print axioms Hypermath.GroundSyntaxChecks.malformed_reuse_rejected
