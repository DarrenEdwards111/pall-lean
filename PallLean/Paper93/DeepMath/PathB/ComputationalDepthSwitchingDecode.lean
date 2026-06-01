import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCircuitPath

/-!
# The decode/replay invariant and `decode_encode_id` (the Håstad recovery core)

**STATUS: REAL.  GLOBAL RECOVERY + INJECTIVITY OF THE CANONICAL PATH ENCODING.**

The recovery half of the switching injection, built with the invariant visible:

* **State.**  The encoder maps `ρ` to its path restriction `circuitPath ρ ts a`
  (the shortened restriction) and selected set `circuitSel ρ ts a`.  The decoder
  is `freeOn _ (circuitSel ρ ts a)`.
* **Prefix invariant** (`circuitPath_eq_outside`, via `termPath_eq_outside`,
  `fixOn_eq_outside`): the path restriction agrees with `ρ` on every coordinate
  **outside** the selected set — the encoder only ever touches selected
  coordinates.
* **`decode_encode_id`** (`freeOn_circuitPath`): freeing the selected coordinates
  of the path restriction returns `ρ` exactly.

Consequently the canonical encoding `ρ ↦ (circuitPath ρ ts a, circuitSel ρ ts a)`
is **injective** (`circuitPath_inj`).  This is the genuine recovery/injectivity at
the *set-label* level; composing it with the free-literal label
(`canonicalSel_eq_freeLits`) to reach the tight `(2w)^s` count is the remaining
refinement.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- `fixOn` only changes coordinates in `S`. -/
theorem fixOn_eq_outside (ρ : Restriction n) (S : Finset (Fin n)) (a : Fin n → Bool)
    {i : Fin n} (hi : i ∉ S) : fixOn ρ S a i = ρ i := by
  simp only [fixOn, if_neg hi]

/-- **Term-level invariant.**  `termPath` agrees with `ρ` outside its selected set. -/
theorem termPath_eq_outside :
    ∀ (cs : List (Clause n)) (ρ : Restriction n) (a : Fin n → Bool) (i : Fin n),
      i ∉ termSel ρ cs a → termPath ρ cs a i = ρ i := by
  intro cs
  induction cs with
  | nil => intro ρ a i _; rfl
  | cons C cs ih =>
    intro ρ a i hi
    rw [show termSel ρ (C :: cs) a
        = canonicalSel ρ C ∪ termSel (fixOn ρ (canonicalSel ρ C) a) cs a from rfl,
      Finset.mem_union, not_or] at hi
    show termPath (fixOn ρ (canonicalSel ρ C) a) cs a i = ρ i
    rw [ih (fixOn ρ (canonicalSel ρ C) a) a i hi.2]
    exact fixOn_eq_outside ρ (canonicalSel ρ C) a hi.1

/-- **Circuit-level invariant.**  `circuitPath` agrees with `ρ` outside its selected
set — the encoder touches only selected coordinates. -/
theorem circuitPath_eq_outside :
    ∀ (ts : List (Term n)) (ρ : Restriction n) (a : Fin n → Bool) (i : Fin n),
      i ∉ circuitSel ρ ts a → circuitPath ρ ts a i = ρ i := by
  intro ts
  induction ts with
  | nil => intro ρ a i _; rfl
  | cons T ts ih =>
    intro ρ a i hi
    rw [show circuitSel ρ (T :: ts) a
        = termSel ρ T.clauses a ∪ circuitSel (termPath ρ T.clauses a) ts a from rfl,
      Finset.mem_union, not_or] at hi
    show circuitPath (termPath ρ T.clauses a) ts a i = ρ i
    rw [ih (termPath ρ T.clauses a) a i hi.2]
    exact termPath_eq_outside T.clauses ρ a i hi.1

/-- **`decode_encode_id`.**  Freeing the selected coordinates of the path
restriction recovers `ρ` exactly. -/
theorem freeOn_circuitPath (ρ : Restriction n) (ts : List (Term n)) (a : Fin n → Bool) :
    freeOn (circuitPath ρ ts a) (circuitSel ρ ts a) = ρ := by
  funext i
  simp only [freeOn]
  by_cases hi : i ∈ circuitSel ρ ts a
  · rw [if_pos hi]
    exact (mem_freeVars.mp (circuitSel_subset_freeVars ts ρ a hi)).symm
  · rw [if_neg hi]
    exact circuitPath_eq_outside ts ρ a i hi

/-- **Injectivity of the canonical encoding.**  `ρ` is determined by its path
restriction together with its selected set — the recovery is a left inverse. -/
theorem circuitPath_inj (ts : List (Term n)) (a : Fin n → Bool) {ρ σ : Restriction n}
    (hp : circuitPath ρ ts a = circuitPath σ ts a)
    (hs : circuitSel ρ ts a = circuitSel σ ts a) : ρ = σ := by
  rw [← freeOn_circuitPath ρ ts a, hp, hs, freeOn_circuitPath σ ts a]

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.freeOn_circuitPath
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.circuitPath_inj
