/-!
# The ladder and its self-containing top: ℕ inside the conatural numbers

`ground or □ of something` has least fixed point ℕ (the `==` ladder) and greatest fixed point
the conatural numbers: ℕ plus one element `top` with `□ top = top`.

Representation (Lean core, no Mathlib): a conatural is a decreasing Bool stream;
`x.f k = true` reads "x has passed rung k". The finite rung `n` has passed exactly k < n.

Kernel-checked here:
* `succ_top`: □ top = top, the top contains itself;
* `rung` embeds the ladder injectively, commuting with □, and □ never lands on ground;
* `top_not_rung`: the top is beyond every rung;
* `extrapolated_top_unique`: anything above every rung IS the top, so the top is fully
  determined by the descriptions of all runs below (owner's "extrapolatable top");
* `finite_or_top` (classical) and `lpo_of_decide_top`: a decision procedure for
  "is x the top?" would decide whether an arbitrary Bool stream is all-false (LPO), i.e. a rung
  cannot, in general, compute whether it is finite or the top.
-/

namespace HypermathTop

structure Conat where
  f : Nat → Bool
  dec : ∀ k, f (k + 1) = true → f k = true

theorem Conat.ext {x y : Conat} (h : ∀ k, x.f k = y.f k) : x = y := by
  cases x; cases y; simp only [Conat.mk.injEq]; funext k; exact h k

def ground : Conat := ⟨fun _ => false, fun _ h => h⟩

def top : Conat := ⟨fun _ => true, fun _ _ => rfl⟩

/-- □: passing rung 0 now, and rung k+1 iff x had passed rung k. -/
def succ (x : Conat) : Conat where
  f := fun k => match k with
    | 0 => true
    | k + 1 => x.f k
  dec := by
    intro k h
    cases k with
    | zero => rfl
    | succ k => exact x.dec k h

theorem succ_top : succ top = top := Conat.ext fun k => by cases k <;> rfl

theorem succ_ne_ground : ∀ x : Conat, succ x ≠ ground := by
  intro x h
  have := congrArg (fun c => c.f 0) h
  simp [succ, ground] at this

theorem succ_injective : ∀ x y : Conat, succ x = succ y → x = y := by
  intro x y h
  exact Conat.ext fun k => congrArg (fun c => c.f (k + 1)) h

def rung (n : Nat) : Conat := ⟨fun k => decide (k < n), fun k h => by
  simp only [decide_eq_true_eq] at h ⊢; omega⟩

theorem rung_succ (n : Nat) : rung (n + 1) = succ (rung n) := by
  apply Conat.ext; intro k
  cases k with
  | zero => simp [rung, succ]
  | succ k => simp [rung, succ]

theorem rung_injective : ∀ m n : Nat, rung m = rung n → m = n := by
  intro m n h
  have hm := congrArg (fun c => c.f m) h
  have hn := congrArg (fun c => c.f n) h
  simp only [rung, decide_eq_decide] at hm hn
  omega

theorem top_not_rung : ∀ n : Nat, top ≠ rung n := by
  intro n h
  have := congrArg (fun c => c.f n) h
  simp [top, rung] at this

/-- `x` is above rung `n`: it has passed every rung that `n` has passed. -/
def above (x : Conat) (n : Nat) : Prop := ∀ k, k < n → x.f k = true

/-- The extrapolatable top: whatever lies above every rung is exactly the top. -/
theorem extrapolated_top_unique : ∀ x : Conat, (∀ n, above x n) → x = top := by
  intro x h
  exact Conat.ext fun k => h (k + 1) k (Nat.lt_succ_self k)

theorem top_above_all : ∀ n, above top n := fun _ _ _ => rfl

theorem down (x : Conat) : ∀ j, x.f j = true → ∀ i, i ≤ j → x.f i = true := by
  intro j
  induction j with
  | zero => intro h i hi; have : i = 0 := by omega
            subst this; exact h
  | succ j ih =>
    intro h i hi
    by_cases e : i = j + 1
    · subst e; exact h
    · exact ih (x.dec j h) i (by omega)

theorem up (x : Conat) (j : Nat) (h : x.f j = false) : ∀ i, j ≤ i → x.f i = false := by
  intro i hi
  cases hx : x.f i with
  | false => rfl
  | true => have := down x i hx j hi; simp_all

/-- A rung is located by its first silent step. -/
theorem rung_of_false (x : Conat) : ∀ k, x.f k = false → ∃ n, x = rung n := by
  intro k
  induction k with
  | zero =>
    intro h
    exact ⟨0, Conat.ext fun j => by simp [rung, up x 0 h j (Nat.zero_le j)]⟩
  | succ k ih =>
    intro h
    cases hk : x.f k with
    | false => exact ih hk
    | true =>
      refine ⟨k + 1, Conat.ext fun j => ?_⟩
      by_cases hj : j < k + 1
      · simp [rung, hj, down x k hk j (by omega)]
      · simp [rung, hj, up x (k + 1) h j (by omega)]

/-- Classically every conatural is a rung or the top. -/
theorem finite_or_top (x : Conat) : x = top ∨ ∃ n, x = rung n := by
  by_cases h : ∀ k, x.f k = true
  · exact Or.inl (Conat.ext h)
  · have ⟨k, hk⟩ := Classical.not_forall.1 h
    exact Or.inr (rung_of_false x k (by simpa using hk))

/-- "Has the stream `s` produced a `true` by step k?" -/
def seenUpTo (s : Nat → Bool) : Nat → Bool
  | 0 => s 0
  | k + 1 => seenUpTo s k || s (k + 1)

/-- The conatural that keeps climbing while `s` stays silent. -/
def watch (s : Nat → Bool) : Conat where
  f := fun k => !(seenUpTo s k)
  dec := by
    intro k h
    simp only [seenUpTo, Bool.not_eq_true', Bool.or_eq_false_iff] at h
    simp [h.1]

theorem seen_false_iff (s : Nat → Bool) : ∀ k, seenUpTo s k = false ↔ ∀ j, j ≤ k → s j = false := by
  intro k
  induction k with
  | zero =>
    simp only [seenUpTo]
    constructor
    · intro h j hj
      have : j = 0 := by omega
      subst this; exact h
    · intro h; exact h 0 (Nat.le_refl 0)
  | succ k ih =>
    simp only [seenUpTo, Bool.or_eq_false_iff, ih]
    constructor
    · intro ⟨h1, h2⟩ j hj
      by_cases e : j = k + 1
      · subst e; exact h2
      · exact h1 j (by omega)
    · intro h; exact ⟨fun j hj => h j (by omega), h (k + 1) (Nat.le_refl _)⟩

theorem watch_top_iff (s : Nat → Bool) : watch s = top ↔ ∀ j, s j = false := by
  constructor
  · intro h j
    have := congrArg (fun c => c.f j) h
    simp only [watch, top, Bool.not_eq_true'] at this
    exact (seen_false_iff s j).1 this j (Nat.le_refl j)
  · intro h
    apply Conat.ext; intro k
    simp only [watch, top, Bool.not_eq_true']
    exact (seen_false_iff s k).2 (fun j _ => h j) |>.symm ▸ rfl

/-- LPO from a top-detector: deciding "x is the top" decides whether any stream is all-false. -/
def lpo_of_decide_top (d : ∀ x : Conat, Decidable (x = top)) (s : Nat → Bool) :
    Decidable (∀ j, s j = false) :=
  decidable_of_iff (watch s = top) (watch_top_iff s)

end HypermathTop

#print axioms HypermathTop.extrapolated_top_unique
#print axioms HypermathTop.succ_top
#print axioms HypermathTop.watch_top_iff
#print axioms HypermathTop.finite_or_top
