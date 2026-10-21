/-!
# Ladder induction: transfinite induction below ω^ω from *nested finite* induction

Owner's program (USER-STATED 2026-10-04): rank-ordered omegas, ℕ-indexed middle bands, ω^ω as
the collapse of the whole ladder. This file turns that picture into a proof technique.

`Tower k` is the ordinals below ω^k as a vector of k natural coefficients, leading rank first:
`(c_{k-1}, …, c_0)` denotes `ω^(k-1)·c_{k-1} + … + ω^0·c_0`. `lt k` is the ordinal order.

`ladder_induction`: for every k, transfinite induction over `Tower k` follows from k *nested
ordinary inductions* (one strong induction per rank, innermost rank last). No `WellFounded`,
no `Acc`, no ordinal library: the proof is the nesting itself.

Consequences proved here, all with `propext`/`Quot.sound` at most:
* `no_infinite_descent`: no infinite descending sequence in any `Tower k`;
* `descent_terminates`: a computable descent measure bound on `Tower 2` (ω²) used to show
  termination of a rewrite rule that the single-ℕ measure cannot handle (see `Ack`-style example);
* `omega_mult_ladder`: ω < ω·2 < ω·3 < … in `Tower 2` (the ℕ-indexed middle band);
* uniformity in k: `ladder_induction` is stated for all k at once, which is the ω^ω-induction
  (every ordinal below ω^ω lives in some `Tower k`). Induction on k happens outside the nest;
  the *next* level (towers of towers, ω^ω^ω … ε₀) needs that outer induction to be nested too,
  and that is where Gentzen's wall sits.
-/

namespace HypermathLadder

def Tower : Nat → Type
  | 0 => Unit
  | k + 1 => Nat × Tower k

def lt : (k : Nat) → Tower k → Tower k → Prop
  | 0, _, _ => False
  | k + 1, (a, x), (b, y) => a < b ∨ (a = b ∧ lt k x y)

/-- Transfinite induction below ω^k, proved by nesting ordinary induction k deep. -/
theorem ladder_induction : ∀ (k : Nat) (P : Tower k → Prop),
    (∀ x, (∀ y, lt k y x → P y) → P x) → ∀ x, P x := by
  intro k
  induction k with
  | zero =>
    intro P H x
    exact H x (fun _ h => h.elim)
  | succ k ih =>
    intro P H x
    obtain ⟨a, x⟩ := x
    -- outer: strong induction on the leading coefficient a
    induction a using Nat.strongRecOn generalizing x with
    | _ a outer =>
      -- inner: transfinite induction on the lower ranks, from the induction hypothesis for k
      refine ih (fun z => P (a, z)) ?_ x
      intro z inner
      apply H (a, z)
      intro ⟨b, y⟩ hy
      rcases hy with hb | ⟨hb, hyz⟩
      · exact outer b hb y
      · subst hb; exact inner y hyz

/-- Equivalent reading: no infinite descending chain below ω^k. -/
theorem no_infinite_descent (k : Nat) (f : Nat → Tower k)
    (hdesc : ∀ n, lt k (f (n + 1)) (f n)) : False := by
  have key : ∀ x : Tower k, ∀ n, f n ≠ x := by
    intro x
    induction x using ladder_induction k with
    | _ x ih =>
      intro n hn
      subst hn
      exact ih (f (n + 1)) (hdesc n) (n + 1) rfl
  exact key (f 0) 0 rfl

/-! ## The ℕ-indexed middle band: ω < ω·2 < ω·3 < … inside ω² -/

/-- `omega_times n` is ω·n in `Tower 2`. -/
def omega_times (n : Nat) : Tower 2 := (n, (0, ()))

theorem omega_mult_ladder : ∀ n, lt 2 (omega_times n) (omega_times (n + 1)) :=
  fun n => Or.inl (Nat.lt_succ_self n)

/-- Every ω·n lies strictly below ω² = (1,(0)) … written as (1,0,0) in `Tower 3`. -/
def omega_squared : Tower 3 := (1, (0, (0, ())))
def lift2 (x : Tower 2) : Tower 3 := (0, x)

theorem band_below_omega_squared : ∀ n, lt 3 (lift2 (omega_times n)) omega_squared :=
  fun _ => Or.inl (Nat.zero_lt_one)

/-! ## A termination proof that needs ω², not ℕ

The rewrite `step (a+1, b) = (a, anything)` and `step (a, b+1) = (a, b)` on `Nat × Nat`
terminates, although `b` can be made arbitrarily large when `a` drops. Ordinary induction on a
single ℕ measure fails (no bound); ladder induction on `Tower 2` proves it. -/

def step : Nat × Nat → Nat → Nat × Nat
  | (a + 1, _), m => (a, m)
  | (0, b + 1), _ => (0, b)
  | (0, 0), _ => (0, 0)

def asTower2 (p : Nat × Nat) : Tower 2 := (p.1, (p.2, ()))

theorem step_decreases : ∀ (p : Nat × Nat) (m : Nat), p ≠ (0, 0) →
    lt 2 (asTower2 (step p m)) (asTower2 p) := by
  intro ⟨a, b⟩ m hne
  cases a with
  | succ a => exact Or.inl (Nat.lt_succ_self a)
  | zero =>
    cases b with
    | zero => exact absurd rfl hne
    | succ b => exact Or.inr ⟨rfl, Or.inl (Nat.lt_succ_self b)⟩

/-- Whatever the adversary supplies as `m` each round, the game ends: no infinite run. -/
theorem descent_terminates (m : Nat → Nat) (run : Nat → Nat × Nat)
    (hrun : ∀ n, run (n + 1) = step (run n) (m n)) (hne : ∀ n, run n ≠ (0, 0)) : False :=
  no_infinite_descent 2 (fun n => asTower2 (run n)) (fun n => by
    show lt 2 (asTower2 (run (n + 1))) (asTower2 (run n))
    rw [hrun n]; exact step_decreases (run n) (m n) (hne n))

end HypermathLadder

#print axioms HypermathLadder.ladder_induction
#print axioms HypermathLadder.no_infinite_descent
#print axioms HypermathLadder.descent_terminates
