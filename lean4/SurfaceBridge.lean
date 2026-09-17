import Hypermath.LayeredDerivation
import Lean.Data.Json

/-!
Bounded executable bridge to the existing finite layer definitions. JSON is
host transport, not a native Hypermath formation or acceptance rule. The Python
adapter supplies canonical input and separately binds graph/evidence digests.
-/

open Lean Hypermath Hypermath.GroundCode Hypermath.GroundDerivation
open Hypermath.LayeredDerivation

private def fail {α : Type} (message : String) : Except String α := .error message

private def treeString (tree : Tree) : String :=
  String.mk (tree.bits.map fun bit => if bit then '1' else '0')

private def readTree (value : String) : Except String Tree := do
  if value.length > 8191 then fail "LIMIT: tree exceeds the 8191-bit bound"
  else if !value.toList.all (fun char => char == '0' || char == '1') then
    fail "tree contains a nonbinary character"
  else
    let bits := value.toList.map (· == '1')
    match GroundCode.parse bits.length bits with
    | some (tree, []) => return tree
    | _ => fail "tree is incomplete or contains trailing data"

private def surfaceJson (layer : Nat) (surface : Surface layer) : Json :=
  Json.mkObj [("format", "hypermath-surface-1"), ("layer", toJson layer),
    ("code", toJson (treeString (encode layer surface)))]

private def readSurface (value : Json) : Except String ((layer : Nat) × Surface layer) := do
  if (← (← value.getObjVal? "format").getStr?) != "hypermath-surface-1" then
    fail "unsupported surface format"
  else
    let layer ← (← value.getObjVal? "layer").getNat?
    if layer > 16 then fail "LIMIT: layer exceeds the bound of 16"
    else
      let tree ← readTree (← (← value.getObjVal? "code").getStr?)
      match decode layer tree with
      | none => fail "surface does not decode at its stated layer"
      | some surface =>
          if encode layer surface = tree then return ⟨layer, surface⟩
          else fail "surface tree is not canonical"

private def observe (layer : Nat) (surface : Surface layer) : Json :=
  Json.mkObj [("surface", surfaceJson layer surface),
    ("valid", toJson (valid layer surface)),
    ("claims", match unfold layer surface with
      | none => Json.null
      | some records => toJson (records.map fun pair => treeString (RecordEncoding.formulaTree pair.2)))]

private def execute (request : Json) : Except String Json := do
  let operation ← (← request.getObjVal? "operation").getStr?
  let inputs ← (← request.getObjVal? "inputs").getArr?
  match operation, inputs.toList with
  | "primitive", [] =>
      let depth ← (← request.getObjVal? "depth").getNat?
      if depth > 32 then fail "LIMIT: term depth exceeds the bound of 32"
      else
        let term := GroundSyntax.Term.ofDepth depth
        let name ← (← request.getObjVal? "rule").getStr?
        let primitive : GroundSyntax.AxiomInstance ← match name with
          | "groundSelf" =>
              if depth == 0 then pure GroundSyntax.AxiomInstance.groundSelf
              else fail "groundSelf has no term argument"
          | "diff" => pure (GroundSyntax.AxiomInstance.diff term)
          | "sim" => pure (GroundSyntax.AxiomInstance.sim term)
          | "box" => pure (GroundSyntax.AxiomInstance.box term)
          | _ => fail "unsupported primitive rule"
        let record := Record.primitive primitive
        return observe 0 (record, record.conclusion)
  | "inspect", [input] =>
      let ⟨layer, surface⟩ ← readSurface input
      return observe layer surface
  | "lift", [input] =>
      let ⟨layer, surface⟩ ← readSurface input
      if layer == 16 then fail "LIMIT: lift would exceed the layer bound"
      else return observe (layer + 1) (lift layer surface)
  | "compose", [first, second] =>
      let ⟨firstLayer, firstSurface⟩ ← readSurface first
      let ⟨secondLayer, secondSurface⟩ ← readSurface second
      match firstLayer, firstSurface, secondLayer, secondSurface with
      | n + 1, left, m + 1, right =>
          if n == m then return observe (n + 1) (.seq left right)
          else fail "composition requires equal layers"
      | _, _, _, _ => fail "composition requires successor-layer surfaces"
  | _, _ => fail "unsupported operation or operand count"

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
      let input ← IO.FS.readFile path
      if input.utf8ByteSize > 65536 then
        IO.eprintln "request exceeds the 64 KiB input bound"
        return 2
      let result := do
        let request ← Json.parse input
        execute request
      let response := match result with
        | .ok value => Json.mkObj [("status", "OK"), ("result", value)]
        | .error reason => Json.mkObj [
            ("status", if reason.startsWith "LIMIT:" then "LIMIT" else "REJECTED"),
            ("reason", toJson reason)]
      IO.println ("HYPERMATH_SURFACE_RESULT:" ++ response.compress)
      return 0
  | _ =>
      IO.eprintln "expected one request-file argument"
      return 2
