import Hypermath.GroundSyntax
import Lean.Elab.Tactic.Omega

/-!
# A finite binary-tree code in unary ground syntax

This is explicit host serialization infrastructure. A tree has a prefix code,
that bit string has a natural-number code, and the number denotes the depth of
a free ground term. The packed numerical interface avoids expanding that unary
term during execution. It does not assert semantic `Form` injectivity, native
arithmetic, internal checking, or a compression theorem.
-/

namespace Hypermath.GroundCode

open GroundSyntax

inductive Tree where
  | leaf
  | fork (left right : Tree)
  deriving DecidableEq, Repr

def pack : List Bool → Nat
  | [] => 0
  | bit :: rest => 2 * pack rest + if bit then 2 else 1

def unpack : Nat → List Bool
  | 0 => []
  | n + 1 => decide (n % 2 = 1) :: unpack (n / 2)
termination_by n => n
decreasing_by omega

theorem unpack_pack (bits : List Bool) : unpack (pack bits) = bits := by
  induction bits with
  | nil => simp [pack, unpack]
  | cons bit rest ih =>
      cases bit <;> simp [pack, unpack, Nat.mul_add_div, Nat.mul_mod, ih] <;> omega

/-- The unary term is exponentially larger than its prefix bit string. -/
theorem pack_bounds (bits : List Bool) :
    2 ^ bits.length ≤ pack bits + 1 ∧ pack bits + 2 ≤ 2 ^ (bits.length + 1) := by
  induction bits with
  | nil => simp [pack]
  | cons bit rest ih =>
      simp only [Nat.pow_succ] at ih
      cases bit <;> simp only [pack, Bool.false_eq_true, ite_false, ite_true,
        List.length_cons, Nat.pow_succ] <;> omega

def Tree.bits : Tree → List Bool
  | .leaf => [false]
  | .fork left right => true :: (left.bits ++ right.bits)

def Tree.size : Tree → Nat
  | .leaf => 1
  | .fork left right => left.size + right.size + 1

theorem Tree.bits_length (tree : Tree) : tree.bits.length = tree.size := by
  induction tree <;> simp_all [Tree.bits, Tree.size]

/-- Fuel bounds parser recursion; callers derive it from the actual input length. -/
def parse : Nat → List Bool → Option (Tree × List Bool)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: rest => some (.leaf, rest)
  | fuel + 1, true :: rest => do
      let (left, middle) ← parse fuel rest
      let (right, tail) ← parse fuel middle
      return (.fork left right, tail)

theorem parse_bits (tree : Tree) (tail : List Bool) (fuel : Nat)
    (enough : tree.size ≤ fuel) : parse fuel (tree.bits ++ tail) = some (tree, tail) := by
  induction tree generalizing fuel tail with
  | leaf =>
      cases fuel with
      | zero => simp [Tree.size] at enough
      | succ fuel => rfl
  | fork left right ihLeft ihRight =>
      cases fuel with
      | zero => simp [Tree.size] at enough
      | succ fuel =>
          have leftBound : left.size ≤ fuel := by simp [Tree.size] at enough; omega
          have rightBound : right.size ≤ fuel := by simp [Tree.size] at enough; omega
          simp [Tree.bits, parse, List.append_assoc,
            ihLeft (right.bits ++ tail) fuel leftBound, ihRight tail fuel rightBound]

def Tree.code (tree : Tree) : Nat := pack tree.bits

/-- Consume the whole code. A valid prefix with trailing data is not accepted. -/
def decodeNumber (code : Nat) : Option Tree :=
  let bits := unpack code
  match parse bits.length bits with
  | some (tree, []) => some tree
  | _ => none

theorem decode_code (tree : Tree) : decodeNumber tree.code = some tree := by
  have parsed := parse_bits tree [] tree.size (Nat.le_refl _)
  simp only [List.append_nil] at parsed
  simp [decodeNumber, Tree.code, unpack_pack, Tree.bits_length, parsed]

def Tree.toTerm (tree : Tree) : Term := Term.ofDepth tree.code

def decodeTerm (term : Term) : Option Tree := decodeNumber term.depth

theorem decode_toTerm (tree : Tree) : decodeTerm tree.toTerm = some tree := by
  simp [decodeTerm, Tree.toTerm, Term.depth_ofDepth, decode_code]

theorem code_injective {first second : Tree} (same : first.code = second.code) :
    first = second :=
  Option.some.inj ((decode_code first).symm.trans
    ((congrArg decodeNumber same).trans (decode_code second)))

theorem toTerm_injective {first second : Tree} (same : first.toTerm = second.toTerm) :
    first = second :=
  Option.some.inj ((decode_toTerm first).symm.trans
    ((congrArg decodeTerm same).trans (decode_toTerm second)))

end Hypermath.GroundCode
