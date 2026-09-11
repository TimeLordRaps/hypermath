import Hypermath.RecordEncoding

namespace Hypermath.RecordEncodingChecks

open GroundSyntax GroundDerivation GroundCode RecordEncoding

def exampleRecord : Record := quote (separation (.apply .ground))

theorem packed_separation_checked (term : Term) :
    checkNumbers (recordCode (quote (separation term)))
      (formulaCode (.both (.similar (.apply term) .ground)
        (.notSimulation (.apply term) .ground))) = true := by
  rw [checkNumbers_codes]
  exact check_quote (separation term)

theorem wrong_claim_rejected :
    checkNumbers (recordCode exampleRecord)
      (formulaCode (.notSimulation .ground .ground)) = false := by
  rw [checkNumbers_codes]
  rfl

def hiddenFailure : Record :=
  .projectLeft (.structural (.continues .ground .ground))
    (.similar (.apply .ground) .ground)
    (.join (.primitive .groundSelf)
      (.closeContinues (.apply .ground) (.primitive (.diff .ground))))

theorem encoded_projection_cannot_hide_failure :
    checkNumbers (recordCode hiddenFailure) (formulaCode hiddenFailure.conclusion) = false := by
  rw [checkNumbers_codes]
  rfl

theorem repeated_record_checked :
    checkNumbers (recordCode (.join exampleRecord exampleRecord))
      (formulaCode (.both exampleRecord.conclusion exampleRecord.conclusion)) = true := by
  rw [checkNumbers_codes]
  rfl

theorem empty_code_rejected : decodeNumber 0 = none := by
  simp [decodeNumber, unpack, parse]
theorem incomplete_tree_rejected : decodeNumber (pack [true, false]) = none := by
  simp [decodeNumber, unpack_pack, parse]
theorem trailing_bits_rejected : decodeNumber (pack [false, false]) = none := by
  simp [decodeNumber, unpack_pack, parse]
theorem no_parse_fuel : parse 0 [false] = none := rfl
theorem unknown_formula_tag_rejected : readFormula (tag 4 .leaf) = none := rfl
theorem unknown_record_tag_rejected : readRecord (tag 7 .leaf) = none := rfl
theorem wrong_formula_arity_rejected : readFormula (tag 3 .leaf) = none := rfl
theorem wrong_record_arity_rejected : readRecord (tag 4 .leaf) = none := rfl
theorem malformed_primitive_rejected :
    readRecord (tag 0 (termTree (Term.ofDepth 4))) = none := rfl
theorem malformed_tag_rejected : readTag (.fork (.fork .leaf .leaf) .leaf) = none := rfl
theorem invalid_inputs_rejected : checkNumbers 0 0 = false := by
  simp [checkNumbers, checkDecoded, decodeRecord, decodeFormula, empty_code_rejected]
theorem invalid_join_rejected : joinCodes 0 0 = none := by
  simp [joinCodes, decodeRecord, empty_code_rejected]

/-- This executes packed numbers; it never constructs their unary ground terms. -/
def packedSmoke : IO Unit := do
  let record := recordCode exampleRecord
  let formula := formulaCode exampleRecord.conclusion
  unless decodeRecord record == some exampleRecord do
    throw (IO.userError "packed record did not round trip")
  unless checkNumbers record formula do
    throw (IO.userError "packed separation was not accepted")
  unless !(checkNumbers (recordCode hiddenFailure) (formulaCode hiddenFailure.conclusion)) do
    throw (IO.userError "packed projection concealed a failed premise")
  unless joinCodes record record == some (recordCode (.join exampleRecord exampleRecord)) do
    throw (IO.userError "packed join changed the record")
  IO.println s!"Packed check passed; prefix bits={unpack record |>.length}; unary depth={record}"

#eval packedSmoke

end Hypermath.RecordEncodingChecks

#print axioms Hypermath.GroundCode.unpack_pack
#print axioms Hypermath.GroundCode.pack_bounds
#print axioms Hypermath.GroundCode.Tree.bits_length
#print axioms Hypermath.GroundCode.parse_bits
#print axioms Hypermath.GroundCode.decode_code
#print axioms Hypermath.GroundCode.decode_toTerm
#print axioms Hypermath.GroundCode.code_injective
#print axioms Hypermath.GroundCode.toTerm_injective
#print axioms Hypermath.RecordEncoding.readTerm_termTree
#print axioms Hypermath.RecordEncoding.readTag_number
#print axioms Hypermath.RecordEncoding.readStatement_statementTree
#print axioms Hypermath.RecordEncoding.readFormula_formulaTree
#print axioms Hypermath.RecordEncoding.readRecord_recordTree
#print axioms Hypermath.RecordEncoding.decode_recordCode
#print axioms Hypermath.RecordEncoding.decode_formulaCode
#print axioms Hypermath.RecordEncoding.decodeFormula_recordCode
#print axioms Hypermath.RecordEncoding.decodeRecord_formulaCode
#print axioms Hypermath.RecordEncoding.recordCode_injective
#print axioms Hypermath.RecordEncoding.observe_recordCode
#print axioms Hypermath.RecordEncoding.decode_recordTerm
#print axioms Hypermath.RecordEncoding.decode_formulaTerm
#print axioms Hypermath.RecordEncoding.checkNumbers_codes
#print axioms Hypermath.RecordEncoding.checkTerms_terms
#print axioms Hypermath.RecordEncoding.checkNumbers_sound
#print axioms Hypermath.RecordEncoding.checkTerms_quote
#print axioms Hypermath.RecordEncoding.recordTerm_injective
#print axioms Hypermath.RecordEncoding.observe_recordTerm
#print axioms Hypermath.RecordEncoding.joinCodes_recordCode
#print axioms Hypermath.RecordEncoding.semantic_record_recovery
#print axioms Hypermath.RecordEncodingChecks.packed_separation_checked
#print axioms Hypermath.RecordEncodingChecks.wrong_claim_rejected
#print axioms Hypermath.RecordEncodingChecks.encoded_projection_cannot_hide_failure
#print axioms Hypermath.RecordEncodingChecks.repeated_record_checked
#print axioms Hypermath.RecordEncodingChecks.empty_code_rejected
#print axioms Hypermath.RecordEncodingChecks.incomplete_tree_rejected
#print axioms Hypermath.RecordEncodingChecks.trailing_bits_rejected
#print axioms Hypermath.RecordEncodingChecks.no_parse_fuel
#print axioms Hypermath.RecordEncodingChecks.unknown_formula_tag_rejected
#print axioms Hypermath.RecordEncodingChecks.unknown_record_tag_rejected
#print axioms Hypermath.RecordEncodingChecks.wrong_formula_arity_rejected
#print axioms Hypermath.RecordEncodingChecks.wrong_record_arity_rejected
#print axioms Hypermath.RecordEncodingChecks.malformed_primitive_rejected
#print axioms Hypermath.RecordEncodingChecks.malformed_tag_rejected
#print axioms Hypermath.RecordEncodingChecks.invalid_inputs_rejected
#print axioms Hypermath.RecordEncodingChecks.invalid_join_rejected
