import Mathlib.Data.List.Basic

/-!
# A harder-class fast-SAT: DNF-SAT decided by a local consistency check (no 2^n search)

The junta fast-SAT (`RestrictedFastSAT`) fills the crossing socket for a *very* weak class — circuits
depending on only `d` of `n` inputs.  This file strengthens the fill to a genuinely richer class: **DNF**
(an OR of terms, each an AND of literals), which may depend on *all* `n` variables.  Its satisfiability
is still decided *without* any exponential search — by a purely local check on each term — so DNF-SAT is
a real faster-than-brute-force Circuit-SAT algorithm, proved correct.

The algorithm: a DNF is satisfiable **iff some term is consistent** — i.e. some term never demands a
variable be both `true` and `false`.  Checking consistency of every term is a polynomial list scan; the
`2^n` assignment space is never touched.

## What is proved

* **`dnf_sat_iff_consistent_term`** — the algorithm is CORRECT: `SAT φ ↔ ∃ t ∈ φ, consistent t`.
  Forward: a satisfied term can't demand conflicting values.  Backward: from a consistent term, read off
  a satisfying assignment (`x v = true` iff some literal `(v, true)` is in the term; consistency makes
  this well-defined).

## Honest scope

A real, complete fast-SAT algorithm — for **DNF** (depth-2, still a restricted class below AC⁰), harder
than juntas (it can depend on every variable).  It fills the `Attack.decides` socket for this class.
Pushing the same "decide by local structure, not by search" idea to a class *past ACC⁰* is the open
direction — and ultimately the wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DNFFastSAT

variable {n : ℕ}

/-- A literal: a variable and the value it demands. -/
abbrev Lit (n : ℕ) := Fin n × Bool

/-- A term: an AND of literals. -/
abbrev Term (n : ℕ) := List (Lit n)

/-- A DNF: an OR of terms. -/
abbrev DNF (n : ℕ) := List (Term n)

/-- An assignment satisfies a term iff it meets every literal's demand. -/
def termSat (x : Fin n → Bool) (t : Term n) : Prop := ∀ l ∈ t, x l.1 = l.2

/-- An assignment satisfies a DNF iff it satisfies some term. -/
def dnfSat (x : Fin n → Bool) (φ : DNF n) : Prop := ∃ t ∈ φ, termSat x t

/-- The DNF is satisfiable. -/
def SAT (φ : DNF n) : Prop := ∃ x, dnfSat x φ

/-- A term is **consistent** if it never demands a variable be two different values.  This is the
algorithm's local check — decidable by a list scan, no assignment search. -/
def consistent (t : Term n) : Prop := ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.1 = l₂.1 → l₁.2 = l₂.2

private theorem decide_bool_eq (b : Bool) : decide (b = true) = b := by cases b <;> rfl

/-- **The DNF-SAT algorithm is correct (proved).**  A DNF is satisfiable iff some term is consistent —
a polynomial local check, with the `2^n` assignment space never searched. -/
theorem dnf_sat_iff_consistent_term (φ : DNF n) : SAT φ ↔ ∃ t ∈ φ, consistent t := by
  constructor
  · rintro ⟨x, t, htφ, htsat⟩
    refine ⟨t, htφ, ?_⟩
    intro l₁ hl₁ l₂ hl₂ hvar
    have h1 := htsat l₁ hl₁
    have h2 := htsat l₂ hl₂
    rw [hvar] at h1
    rw [h2] at h1
    exact h1.symm
  · rintro ⟨t, htφ, hcons⟩
    refine ⟨fun v => decide (∃ l ∈ t, l.1 = v ∧ l.2 = true), t, htφ, ?_⟩
    intro l hl
    have key : (∃ l' ∈ t, l'.1 = l.1 ∧ l'.2 = true) ↔ l.2 = true := by
      constructor
      · rintro ⟨l', hl', hvar, htrue⟩
        rw [← hcons l' hl' l hl hvar]; exact htrue
      · intro h; exact ⟨l, hl, rfl, h⟩
    show decide (∃ l' ∈ t, l'.1 = l.1 ∧ l'.2 = true) = l.2
    rw [decide_eq_decide.mpr key]
    exact decide_bool_eq l.2

end PallLean.Paper93.DeepMath.PathB.DNFFastSAT

#print axioms PallLean.Paper93.DeepMath.PathB.DNFFastSAT.dnf_sat_iff_consistent_term
