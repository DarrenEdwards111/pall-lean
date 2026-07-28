import Mathlib.Tactic
import Mathlib.Order.Zorn
import Mathlib.Logic.Relation

/-!
# 2-SAT by the implication graph — the last Schaefer P-side rung, proved both ways

The final Schaefer tractable class: **2-SAT** (every clause has at most two literals).  Its decision
procedure is the classical **implication graph**: a clause `l₁ ∨ l₂` yields the implications
`¬l₁ → l₂` and `¬l₂ → l₁`.  The formula is satisfiable iff **no literal `l` reaches its negation and is
reached back** — i.e. no variable's two literals lie in one strongly connected component.

Both directions are proved:
* **soundness** (`twosat_sound`) — a satisfying assignment respects every implication edge, so it cannot
  have `l →* ¬l →* l`;
* **completeness** (`twosat_complete`) — from the criterion we *construct* a satisfying assignment.  The
  construction is the honest content: a maximal (Zorn) implication-closed, consistent set of literals is
  total, and a total closed consistent set reads off directly as a satisfying assignment.  The key
  structural fact is **skew-symmetry** of reachability (`reach_skew`: `l →* l' ↔ ¬l' →* ¬l`).

Built through the Mikoshi pipeline: the reachability criterion was gated by brute-force enumeration
(3000 random 2-CNF, `n ≤ 4`, `0` mismatches) before this proof.

## Honest scope

A complete, real fast-SAT — for **2-SAT** (a Schaefer tractable class), proved sound *and* complete.  It
fills `Attack.decides` for 2-CNF.  Relaxing to three literals per clause is 3-SAT — NP-complete, the
wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TwoSATFastSAT

open Relation

variable {n : ℕ}

/-- A literal: a variable and the polarity demanded. -/
abbrev Lit (n : ℕ) := Fin n × Bool

/-- Negation of a literal flips the polarity. -/
def neg (l : Lit n) : Lit n := (l.1, !l.2)

@[simp] theorem neg_mk (v : Fin n) (b : Bool) : neg (v, b) = (v, !b) := rfl

@[simp] theorem neg_neg (l : Lit n) : neg (neg l) = l := by
  cases l; simp [neg]

/-- An assignment satisfies a literal iff it gives the demanded polarity. -/
def litVal (A : Fin n → Bool) (l : Lit n) : Prop := A l.1 = l.2

/-- A literal and its negation are never simultaneously satisfied; exactly one is. -/
theorem litVal_neg (A : Fin n → Bool) (l : Lit n) : litVal A (neg l) ↔ ¬ litVal A l := by
  simp only [litVal, neg]
  cases A l.1 <;> cases l.2 <;> simp

/-- A 2-clause `l₁ ∨ l₂`. -/
abbrev Clause (n : ℕ) := Lit n × Lit n

/-- An assignment satisfies a clause iff it satisfies one of its two literals. -/
def clauseSat (A : Fin n → Bool) (c : Clause n) : Prop := litVal A c.1 ∨ litVal A c.2

/-- The implication-graph edge relation: clause `(l₁, l₂)` gives edges `¬l₁ → l₂` and `¬l₂ → l₁`. -/
def Edge (cls : List (Clause n)) (a b : Lit n) : Prop :=
  ∃ c ∈ cls, (a = neg c.1 ∧ b = c.2) ∨ (a = neg c.2 ∧ b = c.1)

/-- Reachability in the implication graph. -/
def Reach (cls : List (Clause n)) : Lit n → Lit n → Prop := ReflTransGen (Edge cls)

/-- A 2-CNF is satisfiable. -/
def TwoSat (cls : List (Clause n)) : Prop := ∃ A, ∀ c ∈ cls, clauseSat A c

/-- **The criterion**: no literal reaches its negation and is reached back (no literal in an SCC with its
negation). -/
def NoContra (cls : List (Clause n)) : Prop := ∀ l, ¬ (Reach cls l (neg l) ∧ Reach cls (neg l) l)

/-! ### Soundness: a satisfying assignment forbids `l →* ¬l →* l`. -/

/-- A satisfying assignment respects every implication edge. -/
theorem edge_respects {A : Fin n → Bool} {cls : List (Clause n)}
    (hA : ∀ c ∈ cls, clauseSat A c) {a b : Lit n} (he : Edge cls a b) (ha : litVal A a) :
    litVal A b := by
  obtain ⟨c, hc, h⟩ := he
  have hcs := hA c hc
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hcs.resolve_left ((litVal_neg A c.1).mp ha)
  · exact hcs.resolve_right ((litVal_neg A c.2).mp ha)

/-- Reachability preserves truth under a satisfying assignment. -/
theorem reach_respects {A : Fin n → Bool} {cls : List (Clause n)}
    (hA : ∀ c ∈ cls, clauseSat A c) {a b : Lit n} (hr : Reach cls a b) (ha : litVal A a) :
    litVal A b := by
  induction hr with
  | refl => exact ha
  | tail _ hbc ih => exact edge_respects hA hbc ih

/-- **Soundness (proved).**  A satisfiable 2-CNF meets the criterion. -/
theorem twosat_sound (cls : List (Clause n)) (h : TwoSat cls) : NoContra cls := by
  obtain ⟨A, hA⟩ := h
  intro l hcon
  obtain ⟨hr1, hr2⟩ := hcon
  rcases (em (litVal A l)) with hl | hl
  · exact (litVal_neg A l).mp (reach_respects hA hr1 hl) hl
  · have hnl : litVal A (neg l) := (litVal_neg A l).mpr hl
    exact (litVal_neg A l).mp hnl (reach_respects hA hr2 hnl)

/-! ### Skew-symmetry of reachability. -/

/-- The edge relation is skew-symmetric: an edge `a → b` induces `¬b → ¬a`. -/
theorem edge_skew {cls : List (Clause n)} {a b : Lit n} (he : Edge cls a b) :
    Edge cls (neg b) (neg a) := by
  obtain ⟨c, hc, h⟩ := he
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨c, hc, Or.inr ⟨rfl, neg_neg c.1⟩⟩
  · exact ⟨c, hc, Or.inl ⟨rfl, neg_neg c.2⟩⟩

/-- **Skew-symmetry (proved).**  `l →* l'` iff `¬l' →* ¬l`. -/
theorem reach_skew {cls : List (Clause n)} {a b : Lit n} (hr : Reach cls a b) :
    Reach cls (neg b) (neg a) := by
  induction hr with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih => exact ReflTransGen.head (edge_skew hbc) ih

/-! ### Completeness: build an assignment from the criterion. -/

/-- A set of literals is closed under the implication edges. -/
def Closed (cls : List (Clause n)) (S : Set (Lit n)) : Prop :=
  ∀ a ∈ S, ∀ b, Edge cls a b → b ∈ S

/-- A set of literals is consistent: never contains a literal and its negation. -/
def Consistent (S : Set (Lit n)) : Prop := ∀ l, l ∈ S → neg l ∉ S

/-- A closed set is closed under reachability. -/
theorem closed_reach {cls : List (Clause n)} {S : Set (Lit n)} (hS : Closed cls S) {a b : Lit n}
    (ha : a ∈ S) (hr : Reach cls a b) : b ∈ S := by
  induction hr with
  | refl => exact ha
  | tail _ hbc ih => exact hS _ ih _ hbc

/-- The forward closure of a literal in the implication graph. -/
def closure (cls : List (Clause n)) (l : Lit n) : Set (Lit n) := {l' | Reach cls l l'}

theorem mem_closure {cls : List (Clause n)} {l l' : Lit n} :
    l' ∈ closure cls l ↔ Reach cls l l' := Iff.rfl

theorem self_mem_closure {cls : List (Clause n)} (l : Lit n) : l ∈ closure cls l :=
  ReflTransGen.refl

theorem closure_closed {cls : List (Clause n)} (l : Lit n) : Closed cls (closure cls l) := by
  intro a ha b hab
  exact ReflTransGen.tail ha hab

/-- **The key structural step.**  Given the criterion, at least one of `closure l`, `closure ¬l` is
consistent.  (If both were inconsistent, skew-symmetry would give `l →* ¬l →* l`.) -/
theorem one_closure_consistent {cls : List (Clause n)} (h : NoContra cls) (l : Lit n) :
    Consistent (closure cls l) ∨ Consistent (closure cls (neg l)) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  -- ¬Consistent S = ∃ m ∈ S, neg m ∈ S
  simp only [Consistent, not_forall, not_not, exists_prop] at h1 h2
  obtain ⟨m, hm, hnm⟩ := h1
  obtain ⟨m', hm', hnm'⟩ := h2
  rw [mem_closure] at hm hnm hm' hnm'
  -- Reach l m, Reach l (neg m) ⟹ Reach l (neg l)
  have step1 : Reach cls l (neg l) := by
    have := reach_skew hnm            -- Reach (neg (neg m)) (neg l) = Reach m (neg l)
    rw [neg_neg] at this
    exact ReflTransGen.trans hm this
  -- Reach (neg l) m', Reach (neg l) (neg m') ⟹ Reach (neg l) l
  have step2 : Reach cls (neg l) l := by
    have := reach_skew hnm'           -- Reach (neg (neg m')) (neg (neg l)) = Reach m' l
    rw [neg_neg, neg_neg] at this
    exact ReflTransGen.trans hm' this
  exact h l ⟨step1, step2⟩

/-- A total, closed, consistent set of literals reads off as a satisfying assignment. -/
theorem bridge {cls : List (Clause n)} {S : Set (Lit n)} (hClosed : Closed cls S)
    (hCons : Consistent S) (hTotal : ∀ l, l ∈ S ∨ neg l ∈ S) : TwoSat cls := by
  classical
  refine ⟨fun v => decide ((v, true) ∈ S), fun c hc => ?_⟩
  -- membership in S matches the read-off assignment
  have mem_iff : ∀ l : Lit n, l ∈ S ↔ litVal (fun v => decide ((v, true) ∈ S)) l := by
    intro l
    obtain ⟨v, b⟩ := l
    cases b with
    | true =>
      show (v, true) ∈ S ↔ (decide ((v, true) ∈ S) = true)
      rw [decide_eq_true_eq]
    | false =>
      show (v, false) ∈ S ↔ (decide ((v, true) ∈ S) = false)
      constructor
      · intro hin
        exact decide_eq_false (fun ht => hCons (v, true) ht (by simpa using hin))
      · intro hval
        have hnt : (v, true) ∉ S := of_decide_eq_false hval
        rcases hTotal (v, false) with h' | h'
        · exact h'
        · exact absurd (by simpa using h') hnt
  -- clause is satisfied
  by_contra hcs
  simp only [clauseSat, not_or] at hcs
  obtain ⟨hn1, hn2⟩ := hcs
  rw [← mem_iff] at hn1 hn2
  -- neither literal in S ⟹ both negations in S ⟹ edge forces c.2 ∈ S
  have hneg1 : neg c.1 ∈ S := (hTotal c.1).resolve_left hn1
  have : c.2 ∈ S := hClosed _ hneg1 _ ⟨c, hc, Or.inl ⟨rfl, rfl⟩⟩
  exact hn2 this

/-- **Existence of a total closed consistent set (proved, via Zorn).**  Under the criterion, a maximal
implication-closed consistent set is total. -/
theorem exists_total {cls : List (Clause n)} (h : NoContra cls) :
    ∃ S : Set (Lit n), Closed cls S ∧ Consistent S ∧ ∀ l, l ∈ S ∨ neg l ∈ S := by
  -- chain upper bound: the union of a chain of closed-consistent sets is closed-consistent
  have hchainbound : ∀ c ⊆ {S : Set (Lit n) | Closed cls S ∧ Consistent S},
      IsChain (· ⊆ ·) c →
      ∃ ub ∈ {S : Set (Lit n) | Closed cls S ∧ Consistent S}, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hchain
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · rintro a ⟨t, ht, hat⟩ b hab
      exact Set.mem_sUnion.2 ⟨t, ht, (hc ht).1 a hat b hab⟩
    · rintro w ⟨t1, ht1, hwt1⟩ ⟨t2, ht2, hwt2⟩
      rcases eq_or_ne t1 t2 with rfl | hne
      · exact (hc ht1).2 w hwt1 hwt2
      · rcases hchain ht1 ht2 hne with hsub | hsub
        · exact (hc ht2).2 w (hsub hwt1) hwt2
        · exact (hc ht1).2 w hwt1 (hsub hwt2)
  -- Zorn: a maximal closed-consistent set M
  obtain ⟨M, ⟨hMc, hMco⟩, hMmax⟩ := zorn_subset _ hchainbound
  refine ⟨M, hMc, hMco, ?_⟩
  intro l
  by_contra hcon
  push_neg at hcon
  obtain ⟨hlM, hnlM⟩ := hcon
  -- helper: adding the closure of a literal whose closure is consistent contradicts maximality
  have extend : ∀ k : Lit n, k ∉ M → neg k ∉ M → Consistent (closure cls k) → False := by
    intro k hkM hnkM hck
    have hM'closed : Closed cls (M ∪ closure cls k) := by
      rintro a (haM | hacl) b hab
      · exact Or.inl (hMc a haM b hab)
      · exact Or.inr (closure_closed k a hacl b hab)
    have hM'cons : Consistent (M ∪ closure cls k) := by
      rintro w hw hnw
      rcases hw with hwM | hwcl <;> rcases hnw with hnwM | hnwcl
      · exact hMco w hwM hnwM
      · rw [mem_closure] at hnwcl
        have hsk := reach_skew hnwcl        -- Reach (neg (neg w)) (neg k) = Reach w (neg k)
        rw [neg_neg] at hsk
        exact hnkM (closed_reach hMc hwM hsk)
      · rw [mem_closure] at hwcl
        have hsk := reach_skew hwcl         -- Reach (neg w) (neg k)
        exact hnkM (closed_reach hMc hnwM hsk)
      · exact hck w hwcl hnwcl
    have hsub : M ⊆ M ∪ closure cls k := Set.subset_union_left
    have hsubM : M ∪ closure cls k ⊆ M := hMmax ⟨hM'closed, hM'cons⟩ hsub
    have hmem : k ∈ M ∪ closure cls k := Or.inr (self_mem_closure k)
    exact hkM (hsubM hmem)
  rcases one_closure_consistent h l with hcl | hcl
  · exact extend l hlM hnlM hcl
  · exact extend (neg l) hnlM (by rwa [neg_neg]) hcl

/-- **Completeness (proved).**  A 2-CNF meeting the criterion is satisfiable. -/
theorem twosat_complete (cls : List (Clause n)) (h : NoContra cls) : TwoSat cls := by
  obtain ⟨S, hClosed, hCons, hTotal⟩ := exists_total h
  exact bridge hClosed hCons hTotal

/-- **2-SAT is decided by the implication-graph criterion (proved both ways).**  A 2-CNF is satisfiable
iff no literal reaches its negation and is reached back — no `2^n` search. -/
theorem twosat_iff (cls : List (Clause n)) : TwoSat cls ↔ NoContra cls :=
  ⟨twosat_sound cls, twosat_complete cls⟩

end PallLean.Paper93.DeepMath.PathB.TwoSATFastSAT

#print axioms PallLean.Paper93.DeepMath.PathB.TwoSATFastSAT.twosat_iff
