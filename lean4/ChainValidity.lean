/-!
# Chain validity: a valid derivation chain is forced by its start

Bridge file for the owner's reading of a form as a *reachable closed derivation chain* with `derives`
directional (USER-STATED 2026-10-04), and for the finite model in hyperphysics (`hyperphysics.chain`)
where the energy of a clock-system state is the total squared violation of derivation steps.

Here the discrete core, with no analysis: a chain is a function `psi : Nat → α`, a rule is
`step : Nat → α → α` (`step t` applied to `psi t` should give `psi (t+1)`), and the *violation count*
up to `n` counts the steps that fail.

Proved (no `sorry`; axioms: `propext`, `Quot.sound` only):
* `viol_eq_zero_iff`: the violation count is `0` exactly when every step below `n` is valid;
* `valid_unique`: two chains valid up to `n` with the same start agree up to `n` (derivation is forced);
* `valid_eq_forced`: a chain valid up to `n` equals the forced chain `iter`;
* `viol_pos_of_broken`: changing the value at one interior position of a valid chain gives a positive count
  (the negative control: a corrupted state is detected);
* `closed_periodic`: a closed circuit (the forced chain returns to its start after `p` steps under a
  `p`-periodic rule) repeats with period `p`.

Not claimed: any statement about unitary operators, norms or energies (that is the finite model in
hyperphysics, checked numerically there), or that every form is such a chain.
-/

namespace HypermathChain

variable {α : Type} (step : Nat → α → α)

/-- the forced chain from `a`, starting at step index `s`. -/
def iter : Nat → Nat → α → α
  | 0, _, a => a
  | n + 1, s, a => iter n (s + 1) (step s a)

/-- a step is valid when it is the rule applied to its predecessor. -/
def Valid (psi : Nat → α) (t : Nat) : Prop := psi (t + 1) = step t (psi t)

/-- violation count: the number of failed steps below `n`. -/
def viol [DecidableEq α] (psi : Nat → α) : Nat → Nat
  | 0 => 0
  | n + 1 => viol psi n + (if psi (n + 1) = step n (psi n) then 0 else 1)

theorem viol_eq_zero_iff [DecidableEq α] (psi : Nat → α) :
    ∀ n, viol step psi n = 0 ↔ ∀ t, t < n → Valid step psi t := by
  intro n
  induction n with
  | zero => simp [viol]
  | succ n ih =>
      constructor
      · intro h
        have h1 : viol step psi n = 0 := by
          unfold viol at h
          omega
        have h2 : (if psi (n + 1) = step n (psi n) then 0 else 1) = 0 := by
          unfold viol at h
          omega
        have hv : psi (n + 1) = step n (psi n) := by
          by_cases c : psi (n + 1) = step n (psi n)
          · exact c
          · simp [c] at h2
        intro t ht
        by_cases e : t = n
        · subst e; exact hv
        · exact (ih.mp h1) t (by omega)
      · intro h
        have h1 : viol step psi n = 0 := ih.mpr (fun t ht => h t (by omega))
        have hv : psi (n + 1) = step n (psi n) := h n (by omega)
        unfold viol
        simp [h1, hv]

/-- a chain valid up to `n` from `psi 0 = a` is the forced chain: `psi n = iter step n 0 a`. -/
theorem valid_eq_forced (psi : Nat → α) :
    ∀ n, (∀ t, t < n → Valid step psi t) → psi n = iter step n 0 (psi 0) := by
  have key : ∀ n s, (∀ t, t < n → Valid step psi (s + t)) → psi (s + n) = iter step n s (psi s) := by
    intro n
    induction n with
    | zero => intro s _; rfl
    | succ n ih =>
        intro s h
        have h0 : psi (s + 1) = step s (psi s) := by
          have := h 0 (by omega)
          simpa [Valid] using this
        have h' : ∀ t, t < n → Valid step psi ((s + 1) + t) := by
          intro t ht
          have := h (t + 1) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 t, Nat.add_left_comm] using this
        have := ih (s + 1) h'
        simp only [iter]
        rw [← h0]
        have e : s + (n + 1) = s + 1 + n := by omega
        rw [e]
        exact this
  intro n h
  have := key n 0 (by simpa using h)
  simpa using this

/-- derivation is forced: two chains with the same start, both valid up to `n`, agree at `n`. -/
theorem valid_unique (psi phi : Nat → α) (n : Nat) (h0 : psi 0 = phi 0)
    (hp : ∀ t, t < n → Valid step psi t) (hq : ∀ t, t < n → Valid step phi t) :
    psi n = phi n := by
  rw [valid_eq_forced step psi n hp, valid_eq_forced step phi n hq, h0]

/-- negative control: if one step is broken, the violation count is positive. -/
theorem viol_pos_of_broken [DecidableEq α] (psi : Nat → α) (n t : Nat) (ht : t < n)
    (hb : ¬ Valid step psi t) : 0 < viol step psi n := by
  by_cases z : viol step psi n = 0
  · exact absurd ((viol_eq_zero_iff step psi n).mp z t ht) hb
  · omega

/-- a closed circuit repeats: if the rule is `p`-periodic and `iter step p 0 a = a`, the forced chain
    from `a` returns to `a` at every multiple of `p`. -/
theorem closed_periodic (p : Nat) (hper : ∀ t a, step (t + p) a = step t a)
    (a : α) (hclosed : iter step p 0 a = a) :
    ∀ k, iter step (k * p) 0 a = a := by
  have shift : ∀ n s b, iter step n (s + p) b = iter step n s b := by
    intro n
    induction n with
    | zero => intro s b; rfl
    | succ n ih =>
        intro s b
        simp only [iter]
        rw [show s + p + 1 = (s + 1) + p by omega, ih, hper]
  have shift_mul : ∀ j n s b, iter step n (s + j * p) b = iter step n s b := by
    intro j
    induction j with
    | zero => intro n s b; simp
    | succ j ih =>
        intro n s b
        rw [show s + (j + 1) * p = (s + j * p) + p by rw [Nat.succ_mul]; omega, shift, ih]
  have append : ∀ m n s b, iter step (m + n) s b = iter step n (s + m) (iter step m s b) := by
    intro m
    induction m with
    | zero => intro n s b; simp [iter]
    | succ m ih =>
        intro n s b
        rw [show m + 1 + n = (m + n) + 1 by omega]
        simp only [iter]
        rw [ih n (s + 1) (step s b)]
        rw [show s + 1 + m = s + (m + 1) by omega]
  intro k
  induction k with
  | zero => simp [iter]
  | succ k ih =>
      rw [show (k + 1) * p = k * p + p by rw [Nat.succ_mul]]
      rw [append (k * p) p 0 a, ih, show 0 + k * p = 0 + k * p from rfl, shift_mul k p 0 a, hclosed]

end HypermathChain
