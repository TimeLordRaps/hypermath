/-!
# Form as a transfinite least fixed point

Owner's definition (USER-STATED 2026-10-04): "a form is a reachable closed derivation chain
from the ground L0". Two readings of "reachable":

* finite:      every form is `f2f^n ground` for some `n : Nat`;
* transfinite: forms are the least collection containing `ground`, closed under `f2f`
               and under limits of ω-sequences (Brouwer ordinal trees).

Results, all kernel-checked, no `sorry`:
1. `finite_reachability_contradicts_limit`: for ANY carrier, finite reachability plus the
   source's `ax-limit-not-finite` is contradictory. So "reachable" must be transfinite.
2. In the transfinite model, `f2f` is injective and never returns to ground for free, the
   limit is not finite, minimality is the recursor, and `ordinalApply` defined by transfinite
   recursion makes the three L3 claims refuted in `FiniteActionCountermodel.lean` hold
   with *equality* (stronger than the source's `Congruent`).
Not shown here: that this model satisfies every clause of hypermath's `FullAxioms`.
-/

namespace HypermathTransfinite

/-- 1. Abstract: no carrier has both finite reachability and a non-finite limit.
Stated with the source's own relation: L3 writes `ax-limit-not-finite` with `≡` (`Sim`), so
the contradiction needs only that `≡` is reflexive at the limit. -/
theorem finite_reachability_contradicts_limit {F : Type} (ground L : F) (f : F → F)
    (Sim : F → F → Prop) (simReflAtLimit : Sim L L)
    (reach : ∀ x : F, ∃ n : Nat, Nat.repeat f n ground = x)
    (limitNotFinite : ∀ n : Nat, ¬ Sim (Nat.repeat f n ground) L) : False :=
  let ⟨n, h⟩ := reach L
  limitNotFinite n (h ▸ simReflAtLimit)

/-- 2. Forms as the least collection closed under ground, `f2f` and ω-limits. -/
inductive Form where
  | ground : Form
  | f2f : Form → Form
  | lim : (Nat → Form) → Form

open Form

/-- Minimality is the recursor: a property closed under the three formers holds of all forms. -/
theorem minimality (P : Form → Prop) (h0 : P ground) (hs : ∀ x, P x → P (f2f x))
    (hl : ∀ s : Nat → Form, (∀ n, P (s n)) → P (lim s)) : ∀ x, P x := by
  intro x
  induction x with
  | ground => exact h0
  | f2f x ih => exact hs x ih
  | lim s ih => exact hl s ih

theorem f2f_injective : ∀ x y : Form, f2f x = f2f y → x = y := fun _ _ h => Form.f2f.inj h

theorem ax_diff : ∀ x : Form, f2f x ≠ ground := fun _ h => Form.noConfusion h

def ordinalLimit : Form := lim (fun n => Nat.repeat f2f n ground)

theorem ax_limit_not_finite : ∀ n : Nat, Nat.repeat f2f n ground ≠ ordinalLimit := by
  intro n
  cases n with
  | zero => exact fun h => Form.noConfusion h
  | succ n => exact fun h => Form.noConfusion h

/-- Ordinal iteration by transfinite recursion on the first argument. -/
def ordinalApply : Form → Form → Form
  | ground, x => x
  | f2f p, x => f2f (ordinalApply p x)
  | lim s, x => lim (fun n => ordinalApply (s n) x)

def ordinalSucc : Form → Form := f2f
abbrev DerivationPath := Nat
def compose (p q : DerivationPath) : DerivationPath := p + q
def pathLength (p : DerivationPath) : Form := Nat.repeat f2f p ground

theorem ordinal_zero_identity : ∀ x : Form, ordinalApply ground x = x := fun _ => rfl

theorem ordinal_succ_applies :
    ∀ p x : Form, ordinalApply (ordinalSucc p) x = f2f (ordinalApply p x) := fun _ _ => rfl

theorem path_length_arithmetic :
    ∀ p q : DerivationPath, pathLength (compose p q) = ordinalApply (pathLength q) (pathLength p) := by
  intro p q
  induction q with
  | zero => rfl
  | succ q ih =>
    show f2f (Nat.repeat f2f (p + q) ground) = f2f (ordinalApply (Nat.repeat f2f q ground) (pathLength p))
    exact congrArg f2f ih

/-- The limit is reached transfinitely and is past every finite stage. -/
theorem limit_reached_and_beyond_finite :
    (∃ s : Nat → Form, ordinalLimit = lim s) ∧ (∀ n : Nat, Nat.repeat f2f n ground ≠ ordinalLimit) :=
  ⟨⟨_, rfl⟩, ax_limit_not_finite⟩

/-- ω + 1 is a successor of the limit: arithmetic continues past ω. -/
theorem omega_plus_one : ordinalApply (f2f ground) ordinalLimit = f2f ordinalLimit := rfl

end HypermathTransfinite

#print axioms HypermathTransfinite.path_length_arithmetic
#print axioms HypermathTransfinite.finite_reachability_contradicts_limit
#print axioms HypermathTransfinite.minimality
