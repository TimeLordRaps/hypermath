import Hypermath.Trace

/-!
# Observation boundaries for finite traces

An observation preserved by every justified edge is preserved across a trace.
Endpoint observations need not retain path-dependent data: two traces with the
same endpoints and different structural lengths rule out an endpoint-only
length decoder. These are generic results, with no native `Form` or transfinite
interpretation assumed.
-/

universe u v w z

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

namespace Hypermath.Observation

variable {D : Type u} {R : Type v} {Q : Type w} {B : Type z}

/-- Only records actually produced by this encoding. No inhabitant or default
answer is required for records outside its image. -/
def Image (encode : D → R) := {record : R // ∃ d : D, encode d = record}

def toImage (encode : D → R) (d : D) : Image encode := ⟨encode d, d, rfl⟩

/-- Equal records must give equal answers to every declared observation.
The query family must include observations made after reuse. -/
def Compatible (encode : D → R) (observe : D → Q → B) : Prop :=
  ∀ {first second : D}, encode first = encode second →
    ∀ query : Q, observe first query = observe second query

/-- Correctness on the image; neither decidability nor native definability is
part of this host-level specification. -/
def Decodes (encode : D → R) (observe : D → Q → B)
    (decoder : Image encode → Q → B) : Prop :=
  ∀ d query, decoder (toImage encode d) query = observe d query

theorem decoder_implies_compatible {encode : D → R} {observe : D → Q → B}
    {decoder : Image encode → Q → B} (correct : Decodes encode observe decoder) :
    Compatible encode observe := by
  intro first second equal query
  exact (correct first query).symm.trans
    ((congrArg (fun record => decoder record query) (Subtype.ext equal)).trans
      (correct second query))

/-- Classical existence construction from an image witness, not an executable
decoder or a derivation in the native Hypermath grammar. -/
noncomputable def chosenDecoder (encode : D → R) (observe : D → Q → B)
    (record : Image encode) (query : Q) : B :=
  observe (Classical.choose record.property) query

theorem chosenDecoder_correct {encode : D → R} {observe : D → Q → B}
    (compatible : Compatible encode observe) :
    Decodes encode observe (chosenDecoder encode observe) := by
  intro d query
  exact compatible (Classical.choose_spec (toImage encode d).property) query

/-- The paper's factorization criterion, including empty domains and query
families. Only the existence direction uses classical choice. -/
theorem compatible_iff_decoder (encode : D → R) (observe : D → Q → B) :
    Compatible encode observe ↔ ∃ decoder, Decodes encode observe decoder := by
  constructor
  · intro compatible
    exact ⟨chosenDecoder encode observe, chosenDecoder_correct compatible⟩
  · intro ⟨decoder, correct⟩
    intro first second equal query
    exact decoder_implies_compatible correct equal query

/-- Uniqueness is pointwise on the actual image and requires no choice axiom. -/
theorem decoder_unique_on_image {encode : D → R} {observe : D → Q → B}
    {first second : Image encode → Q → B}
    (firstCorrect : Decodes encode observe first)
    (secondCorrect : Decodes encode observe second) :
    ∀ record query, first record query = second record query := by
  intro record query
  obtain ⟨d, hd⟩ := record.property
  have imageEq : toImage encode d = record := Subtype.ext hd
  rw [← imageEq]
  exact (firstCorrect d query).trans (secondCorrect d query).symm

/-- Apply the listed reuse operations from left to right. This only constructs
finite contexts; it makes no claim about limit stages or infinite unfoldings. -/
def reuse {I : Type w} (operation : I → D → D) : List I → D → D
  | [], d => d
  | index :: rest, d => reuse operation rest (operation index d)

/-- A supplied operation must respect equality of represented inputs.
This condition is an explicit premise, never inferred from base observations. -/
def RespectsEncoding {I : Type w} (encode : D → R) (operation : I → D → D) : Prop :=
  ∀ index {first second}, encode first = encode second →
    encode (operation index first) = encode (operation index second)

theorem reuse_respects_encoding {I : Type w} {encode : D → R}
    {operation : I → D → D} (respects : RespectsEncoding encode operation)
    (context : List I) {first second : D} (equal : encode first = encode second) :
    encode (reuse operation context first) = encode (reuse operation context second) := by
  induction context generalizing first second with
  | nil => exact equal
  | cons index rest ih => exact ih (respects index equal)

/-- One checked substitution condition suffices for every finite reuse depth. -/
theorem reuse_preserves_observations {I : Type w} {encode : D → R}
    {observe : D → Q → B} {operation : I → D → D}
    (compatible : Compatible encode observe) (respects : RespectsEncoding encode operation)
    (context : List I) {first second : D} (equal : encode first = encode second)
    (query : Q) :
    observe (reuse operation context first) query =
      observe (reuse operation context second) query :=
  compatible (reuse_respects_encoding respects context equal) query

/-- Equality to each original input is already a separating observation family. -/
def equalityQuery [DecidableEq D] (d query : D) : Bool := decide (d = query)

/-- Preserving all equality queries requires, and is ensured by, injectivity.
Arithmetic operation preservation alone is a weaker condition. -/
theorem equality_queries_iff_injective [DecidableEq D] (encode : D → R) :
    Compatible encode equalityQuery ↔
      (∀ {first second : D}, encode first = encode second → first = second) := by
  constructor
  · intro compatible first second equal
    have self : equalityQuery first first = true := decide_eq_true rfl
    exact (of_decide_eq_true ((compatible equal first).symm.trans self)).symm
  · intro injective first second equal query
    cases injective equal
    rfl

end Hypermath.Observation
