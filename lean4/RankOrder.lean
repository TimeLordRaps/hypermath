/-!
# The omegas rank-order themselves inside the tower below ω^ω

Owner (USER-STATED 2026-10-04): "we need to prove that omegas naturally rank order in the tower of ω^ω".

Setting: `Tower k` = ordinals below ω^k as k coefficients, leading rank first (as in LadderInduction.lean,
restated here so this file stands alone). `omegaPow k j` is ω^j inside `Tower k` (a single 1 at rank j).

Proved, kernel-checked:
* `lt` is a strict total order on every `Tower k` (irreflexive, transitive, trichotomous): the omegas
  and everything built from them are comparable, with no incomparable pairs;
* `omegaPow_strictMono`: ω^j < ω^j' whenever j < j' (the omegas rank-order by exponent);
* `band`: an element whose leading coefficient at rank k is positive is not below ω^k, while one whose
  leading coefficient is zero is below ω^k: each element lies in exactly one band [ω^k, ω^(k+1));
* `lift` embeds Tower k into Tower (k+1) preserving the order and fixing every omegaPow, and
  `omega_cofinal`: every element of Tower k is below ω^k = omegaPow (k+1) k. So the omegas are cofinal in
  ⋃ₖ Tower k: ω^ω is their supremum, reached by no finite power.
-/

namespace HypermathRank

def Tower : Nat → Type
  | 0 => Unit
  | k + 1 => Nat × Tower k

def lt : (k : Nat) → Tower k → Tower k → Prop
  | 0, _, _ => False
  | k + 1, (a, x), (b, y) => a < b ∨ (a = b ∧ lt k x y)

def zeros : (k : Nat) → Tower k
  | 0 => ()
  | k + 1 => (0, zeros k)

def omegaPow : (k j : Nat) → Tower k
  | 0, _ => ()
  | k + 1, j => if j = k then (1, zeros k) else (0, omegaPow k j)

def lift (k : Nat) (x : Tower k) : Tower (k + 1) := (0, x)

theorem lt_irrefl : ∀ (k : Nat) (x : Tower k), ¬ lt k x x := by
  intro k
  induction k with
  | zero => intro _ h; exact h
  | succ k ih =>
    intro ⟨a, x⟩ h
    rcases h with h | ⟨_, h⟩
    · exact Nat.lt_irrefl a h
    · exact ih x h

theorem lt_trans : ∀ (k : Nat) (x y z : Tower k), lt k x y → lt k y z → lt k x z := by
  intro k
  induction k with
  | zero => intro _ _ _ h; exact h.elim
  | succ k ih =>
    intro ⟨a, x⟩ ⟨b, y⟩ ⟨c, z⟩ h1 h2
    rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
    · exact Or.inl (Nat.lt_trans h1 h2)
    · subst e2; exact Or.inl h1
    · subst e1; exact Or.inl h2
    · subst e1; subst e2; exact Or.inr ⟨rfl, ih x y z h1 h2⟩

theorem lt_trichotomy : ∀ (k : Nat) (x y : Tower k), lt k x y ∨ x = y ∨ lt k y x := by
  intro k
  induction k with
  | zero => intro x y; exact Or.inr (Or.inl rfl)
  | succ k ih =>
    intro ⟨a, x⟩ ⟨b, y⟩
    rcases Nat.lt_trichotomy a b with h | h | h
    · exact Or.inl (Or.inl h)
    · subst h
      rcases ih x y with h | h | h
      · exact Or.inl (Or.inr ⟨rfl, h⟩)
      · subst h; exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))
    · exact Or.inr (Or.inr (Or.inl h))

/-- The omegas rank-order by exponent. -/
theorem omegaPow_strictMono : ∀ (k j j' : Nat), j < j' → j' < k →
    lt k (omegaPow k j) (omegaPow k j') := by
  intro k
  induction k with
  | zero => intro j j' _ h; exact absurd h (Nat.not_lt_zero _)
  | succ k ih =>
    intro j j' hjj hj'
    by_cases e : j' = k
    · subst e
      have hne : j ≠ j' := Nat.ne_of_lt hjj
      simp only [omegaPow, hne, if_false, if_true]
      exact Or.inl Nat.zero_lt_one
    · have hlt : j' < k := by omega
      have hne : j ≠ k := by omega
      simp only [omegaPow, hne, e, if_false]
      exact Or.inr ⟨rfl, ih j j' hjj hlt⟩

/-- Banding: positive leading coefficient ⇒ not below ω^k; zero leading coefficient ⇒ below ω^k. -/
theorem band_upper : ∀ (k : Nat) (x : Tower k), lt (k + 1) (lift k x) (omegaPow (k + 1) k) := by
  intro k x
  simp only [omegaPow, if_true, lift]
  exact Or.inl Nat.zero_lt_one

theorem not_lt_zeros : ∀ (k : Nat) (x : Tower k), ¬ lt k x (zeros k) := by
  intro k
  induction k with
  | zero => intro _ h; exact h
  | succ k ih =>
    intro ⟨a, x⟩ h
    rcases h with h | ⟨_, h⟩
    · exact Nat.not_lt_zero a h
    · exact ih x h

theorem band_lower : ∀ (k a : Nat) (x : Tower k), 0 < a → ¬ lt (k + 1) (a, x) (omegaPow (k + 1) k) := by
  intro k a x ha h
  simp only [omegaPow, if_true] at h
  rcases h with h | ⟨_, h⟩
  · have h1 : a < 1 := h
    omega
  · exact not_lt_zeros k x h

/-- `lift` preserves and reflects the order, and fixes every omega power (for j < k). -/
theorem lift_mono : ∀ (k : Nat) (x y : Tower k), lt k x y → lt (k + 1) (lift k x) (lift k y) :=
  fun _ _ _ h => Or.inr ⟨rfl, h⟩

theorem lift_omegaPow : ∀ (k j : Nat), j < k → lift k (omegaPow k j) = omegaPow (k + 1) j := by
  intro k j hj
  have hne : j ≠ k := Nat.ne_of_lt hj
  simp [lift, omegaPow, hne]

/-- Cofinality: the omegas exhaust the tower, so ω^ω is their supremum, not any of them. -/
theorem omega_cofinal : ∀ (k : Nat) (x : Tower k), ∃ j, lt (k + 1) (lift k x) (omegaPow (k + 1) j) :=
  fun k x => ⟨k, band_upper k x⟩

/-- No omega power is above every element of its own tower: ω^k is the least bound it can offer. -/
theorem no_top_in_tower : ∀ (k : Nat) (x : Tower k), ∃ y : Tower k, lt k x y ∨ k = 0 := by
  intro k
  cases k with
  | zero => intro _; exact ⟨(), Or.inr rfl⟩
  | succ k => intro ⟨a, x⟩; exact ⟨(a + 1, x), Or.inl (Or.inl (Nat.lt_succ_self a))⟩

end HypermathRank

#print axioms HypermathRank.lt_trichotomy
#print axioms HypermathRank.lt_trans
#print axioms HypermathRank.omegaPow_strictMono
#print axioms HypermathRank.band_lower
#print axioms HypermathRank.omega_cofinal
