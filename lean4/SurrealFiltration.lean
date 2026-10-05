/-!
# A surreal-normal-form model of hypermath's relation filtration

Owner's decision (USER-STATED 2026-10-04): ℕ is definable only at `==`.

Carrier: finite sums `Σ cᵢ·ω^eᵢ` (exponents strictly descending, coefficients nonzero
integers): a fragment of Conway normal form, enough to separate orders of infinity.

* `x == y` : equal.
* `x =~ y` : same leading term (they differ by something of strictly smaller order).
* `x ~~ y` : same leading exponent: same archimedean class, "equatable in continuation".

□ (`f2f`) is doubling. At `~~` it is the identity (every order of infinity is kept); at `==` it
is never the identity off zero and never returns to `ground = 1`. The □-tower `2ⁿ` collapses
to a single point at `~~` and stays injective at `==`, so counting lives only at `==`.
Integer coefficients keep this in Lean core (no Mathlib); the numerical fold check was not migrated.
Not shown: that every clause of hypermath's `FullAxioms` holds here.
-/

namespace HypermathSurreal

abbrev Term := Int × Int  -- (exponent of ω, coefficient)

structure Form where
  terms : List Term
  nz : ∀ t ∈ terms, t.2 ≠ 0
  desc : terms.Pairwise (fun a b => a.1 > b.1)

theorem Form.ext {x y : Form} (h : x.terms = y.terms) : x = y := by
  cases x; cases y; simp only at h; subst h; rfl

def ground : Form := ⟨[(0, 1)], by simp, by simp⟩

def dbl (t : Term) : Term := (t.1, 2 * t.2)

def f2f (x : Form) : Form where
  terms := x.terms.map dbl
  nz := by
    intro t ht
    simp only [List.mem_map] at ht
    obtain ⟨a, ha, rfl⟩ := ht
    have := x.nz a ha
    simp only [dbl]; omega
  desc := List.pairwise_map.2 x.desc

def leadTerm (x : Form) : Option Term := x.terms.head?
def leadExp (x : Form) : Option Int := (leadTerm x).map Prod.fst

def Simulation (x y : Form) : Prop := x = y
def Congruent (x y : Form) : Prop := leadTerm x = leadTerm y
def Similar (x y : Form) : Prop := leadExp x = leadExp y

/-- hypermath `filtrationSimCong` and `filtrationCongSim`: `== ⊂ =~ ⊂ ~~`. -/
theorem filtration_sim_cong : ∀ x y : Form, Simulation x y → Congruent x y := by
  intro x y h; subst h; rfl

theorem filtration_cong_sim : ∀ x y : Form, Congruent x y → Similar x y := by
  intro x y h; exact congrArg (Option.map Prod.fst) h

theorem similar_equivalence : Equivalence Similar :=
  ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

theorem map_dbl_ne_one : ∀ l : List Term, l.map dbl ≠ [(0, 1)] := by
  intro l h
  cases l with
  | nil => simp at h
  | cons a l =>
    simp only [List.map, List.cons.injEq, dbl, Prod.mk.injEq] at h
    omega

theorem map_dbl_injective : ∀ l m : List Term, l.map dbl = m.map dbl → l = m := by
  intro l
  induction l with
  | nil => intro m h; cases m <;> simp_all
  | cons a l ih =>
    intro m h
    cases m with
    | nil => simp at h
    | cons b m =>
      simp only [List.map, List.cons.injEq, dbl, Prod.mk.injEq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      rw [ih m h3]
      exact congrArg (· :: m) (Prod.ext h1 (by omega))

theorem map_dbl_fixed : ∀ l : List Term, (∀ t ∈ l, t.2 ≠ 0) → l.map dbl = l → l = [] := by
  intro l nz h
  cases l with
  | nil => rfl
  | cons a l =>
    obtain ⟨k, c⟩ := a
    have hc := nz (k, c) (List.mem_cons_self _ l)
    simp only [List.map, List.cons.injEq, dbl, Prod.mk.injEq] at h
    simp only at hc
    omega

/-- hypermath `axDiff` at `==`: □ never lands on ground. -/
theorem ax_diff : ∀ x : Form, ¬ Simulation (f2f x) ground :=
  fun x h => map_dbl_ne_one x.terms (congrArg Form.terms h)

/-- □ is injective at `==`. -/
theorem f2f_injective : ∀ x y : Form, f2f x = f2f y → x = y :=
  fun _ _ h => Form.ext (map_dbl_injective _ _ (congrArg Form.terms h))

/-- hypermath `traceLevels` (first conjunct, and the two implications): □ is the identity at `~~`. -/
theorem trace_levels : ∀ x : Form,
    Similar (f2f x) x ∧ (Congruent (f2f x) x → Similar (f2f x) x) ∧
      (Simulation (f2f x) x → Congruent (f2f x) x) := by
  intro x
  have s : Similar (f2f x) x := by
    simp only [Similar, leadExp, leadTerm, f2f, List.head?_map, Option.map_map]
    rfl
  exact ⟨s, fun _ => s, fun h => by rw [h]; rfl⟩

/-- Off zero, □ is never the identity at `==`, while it always is at `~~`. -/
theorem identity_at_similar_not_at_simulation :
    ∀ x : Form, x.terms ≠ [] → Similar (f2f x) x ∧ ¬ Simulation (f2f x) x :=
  fun x hne => ⟨(trace_levels x).1,
    fun h => hne (map_dbl_fixed x.terms x.nz (congrArg Form.terms h))⟩

/-! ## The □-tower: one point at `~~`, a copy of ℕ at `==` -/

def tower (n : Nat) : Form := Nat.repeat f2f n ground

theorem tower_collapses_at_similar : ∀ n : Nat, Similar (tower n) ground := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => exact (trace_levels (tower n)).1.trans ih

/-- Any `~~`-invariant property is blind to the tower height: counting is invisible at `~~`. -/
theorem similar_invariants_cannot_count (P : Form → Prop)
    (inv : ∀ x y, Similar x y → (P x ↔ P y)) : ∀ n : Nat, P (tower n) ↔ P ground :=
  fun n => inv _ _ (tower_collapses_at_similar n)

theorem tower_terms : ∀ n : Nat, (tower n).terms = [(0, (2 : Int) ^ n)] := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show (f2f (tower n)).terms = _
    simp only [f2f, ih, List.map, dbl, Int.pow_succ]
    congr 2
    omega

theorem pow2_pos : ∀ n : Nat, 0 < (2 : Int) ^ n := by
  intro n; induction n with
  | zero => decide
  | succ n ih => rw [Int.pow_succ]; omega

theorem pow2_lt : ∀ m n : Nat, m < n → (2 : Int) ^ m < 2 ^ n := by
  intro m n h
  induction n with
  | zero => omega
  | succ n ih =>
    have step : (2 : Int) ^ n < 2 ^ (n + 1) := by rw [Int.pow_succ]; have := pow2_pos n; omega
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
    · exact Int.lt_trans (ih h) step
    · subst h; exact step

/-- Counting is recoverable at `==`: the tower is injective. -/
theorem tower_injective_at_simulation : ∀ m n : Nat, Simulation (tower m) (tower n) → m = n := by
  intro m n h
  have e := congrArg Form.terms h
  rw [tower_terms, tower_terms] at e
  simp only [List.cons.injEq, Prod.mk.injEq, and_true, true_and] at e
  rcases Nat.lt_trichotomy m n with lt | eq | gt
  · have := pow2_lt m n lt; omega
  · exact eq
  · have := pow2_lt n m gt; omega

/-! ## Each rung of the ω-tower carries the same coefficient line (fractal across scales) -/

def monomial (k c : Int) (hc : c ≠ 0) : Form := ⟨[(k, c)], by simp [hc], by simp⟩

theorem monomial_in_rung (k c : Int) (hc : c ≠ 0) : leadExp (monomial k c hc) = some k := rfl

theorem monomials_congruent_iff (k c d : Int) (hc : c ≠ 0) (hd : d ≠ 0) :
    Congruent (monomial k c hc) (monomial k d hd) ↔ c = d := by
  simp [Congruent, leadTerm, monomial]

/-- Different rungs are never similar: orders of infinity stay apart at `~~`. -/
theorem rungs_separate (j k c d : Int) (hc : c ≠ 0) (hd : d ≠ 0) (h : j ≠ k) :
    ¬ Similar (monomial j c hc) (monomial k d hd) := by
  simp [Similar, leadExp, leadTerm, monomial, h]

end HypermathSurreal

#print axioms HypermathSurreal.tower_injective_at_simulation
#print axioms HypermathSurreal.similar_invariants_cannot_count
#print axioms HypermathSurreal.identity_at_similar_not_at_simulation
#print axioms HypermathSurreal.ax_diff
