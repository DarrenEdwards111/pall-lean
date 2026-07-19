import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingComplexity

/-!
# Locality: the missing foundation for crossing-sequence cut-and-paste

Every superlinear crossing-sequence lower bound (palindromes need `Ω(n²)` one-tape time, etc.) rests
on a **cut-and-paste / determinism** step: two computations with the same crossing sequence at a
boundary `b`, agreeing on the tape right of `b`, behave identically to the right of `b`.  The crossing
files so far have the *capacity* side (`crossing_info_capacity`) and the *pumping* entry point
(`crossing_state_repeat`), but not this determinism.  Its rigorous core is two step-level locality
facts, proved here.

* `step_local_right` — if two configurations share state and head position `h > b` and agree on all
  tape cells right of `b`, then after one step they still share state and head and agree right of `b`.
  (While the head is right of `b`, the transition reads and writes only cells `> b`.)
* `step_right_frozen` — if the head is at `≤ b`, one step leaves every cell right of `b` unchanged.
  (A left-region step writes only at `≤ b`.)

Together these are the two halves of cut-and-paste: right-excursions are determined by their entry
state and the right tape (`step_local_right`), and left-excursions freeze the right tape
(`step_right_frozen`).  Gluing them across the alternation of excursions — aligning the two
computations by crossing index rather than by time, since the left-excursion lengths differ — is the
remaining bookkeeping, **not** carried out here.

## Honest ceiling — why this does not reach SAT

Even with the full cut-and-paste, crossing sequences give *time* lower bounds for one-tape machines,
and `crossingCount ≤ time` (`crossingCount_le_time`) caps them at polynomial: they can prove `Ω(n²)`
for a structured family like palindromes (beyond `Ω(n log n)`), but they cannot exceed polynomial, and
a one-tape polynomial-time bound does not separate (one-tape P `=` P).  So this pushes the *technique*
past `Ω(n log n)` on structured families — an unconditional restricted lower bound — but does **not**
bear on `SAT ∉ P`.  It supplies the reusable determinism foundation, with its ceiling stated plainly.

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- Appending blanks does not change any positional read. -/
theorem append_replicate_getD (t : List Bool) (n i : ℕ) :
    (t ++ List.replicate n false).getD i false = t.getD i false := by
  by_cases hi : i < t.length
  · rw [List.getD, List.getD, List.getElem?_append_left hi]
  · push_neg at hi
    have h1 : t[i]? = none := List.getElem?_eq_none hi
    have h2 : (t ++ List.replicate n false)[i]? = (List.replicate n false)[i - t.length]? :=
      List.getElem?_append_right hi
    rw [List.getD, List.getD, h1, h2, Option.getD_none]
    rcases lt_or_ge (i - t.length) n with hlt | hge
    · rw [List.getElem?_replicate]; simp [hlt]
    · rw [List.getElem?_eq_none (by simpa using hge)]; rfl

/-- Positional read-after-write: reading position `p` gives `w`, every other position is unchanged. -/
theorem writeAt_getD (t : List Bool) (p : ℕ) (w : Bool) (i : ℕ) :
    (writeAt t p w).getD i false = if i = p then w else t.getD i false := by
  unfold writeAt
  set u := t ++ List.replicate (p + 1 - t.length) false with hu
  have hlen : p < u.length := by
    rw [hu, List.length_append, List.length_replicate]; omega
  by_cases hip : i = p
  · subst hip
    simp [List.getD, List.getElem?_set_self hlen]
  · have hne : (u.set p w)[i]? = u[i]? := List.getElem?_set_ne (Ne.symm hip)
    rw [if_neg hip, List.getD, hne, ← List.getD, hu, append_replicate_getD]

/-- The transition value of a non-halted step (the `else` branch, with the `let` inlined). -/
theorem step_eq_of_not_halted (M : Machine) {c : Cfg M} (h : M.halt c.st = false) :
    step M c =
      ⟨(M.δ c.st (c.tp.getD c.hd false)).1,
       moveHead c.hd (M.δ c.st (c.tp.getD c.hd false)).2.2,
       match (M.δ c.st (c.tp.getD c.hd false)).2.1 with
       | none => c.tp
       | some w => writeAt c.tp c.hd w⟩ := by
  unfold step; rw [h]; rfl

/-- **Locality (right excursion).**  Two configurations sharing state and head `h > b` and agreeing
on all cells right of `b` still share state and head and agree right of `b` after one step. -/
theorem step_local_right (M : Machine) (b : ℕ) (c₁ c₂ : Cfg M)
    (hst : c₁.st = c₂.st) (hhd : c₁.hd = c₂.hd) (hhb : b < c₁.hd)
    (hagree : ∀ p, b < p → c₁.tp.getD p false = c₂.tp.getD p false) :
    (step M c₁).st = (step M c₂).st ∧ (step M c₁).hd = (step M c₂).hd ∧
      (∀ p, b < p → (step M c₁).tp.getD p false = (step M c₂).tp.getD p false) := by
  have hread : c₁.tp.getD c₁.hd false = c₂.tp.getD c₂.hd false := by
    rw [hhd]; exact hagree c₂.hd (by rw [← hhd]; exact hhb)
  by_cases hh : M.halt c₁.st = true
  · have hh2 : M.halt c₂.st = true := by rw [← hst]; exact hh
    rw [step_of_halted M hh, step_of_halted M hh2]
    exact ⟨hst, hhd, hagree⟩
  · have hh1 : M.halt c₁.st = false := by simpa using hh
    have hh2 : M.halt c₂.st = false := by rw [← hst]; exact hh1
    have htr : M.δ c₁.st (c₁.tp.getD c₁.hd false) = M.δ c₂.st (c₂.tp.getD c₂.hd false) := by
      rw [hst, hread]
    rw [step_eq_of_not_halted M hh1, step_eq_of_not_halted M hh2]
    refine ⟨congrArg (fun r => r.1) htr, by rw [htr, hhd], ?_⟩
    intro p hp
    rw [htr]
    dsimp only
    rcases hw : (M.δ c₂.st (c₂.tp.getD c₂.hd false)).2.1 with _ | w
    · exact hagree p hp
    · rw [writeAt_getD, writeAt_getD, hhd]
      by_cases hpc : p = c₂.hd
      · rw [if_pos hpc, if_pos hpc]
      · rw [if_neg hpc, if_neg hpc]; exact hagree p hp

/-- **Frozen right region.**  If the head is at `≤ b`, one step leaves every cell right of `b`
unchanged. -/
theorem step_right_frozen (M : Machine) (b : ℕ) (c : Cfg M) (hb : c.hd ≤ b) (p : ℕ) (hp : b < p) :
    (step M c).tp.getD p false = c.tp.getD p false := by
  by_cases hh : M.halt c.st = true
  · rw [step_of_halted M hh]
  · have hh1 : M.halt c.st = false := by simpa using hh
    rw [step_eq_of_not_halted M hh1]
    dsimp only
    rcases hw : (M.δ c.st (c.tp.getD c.hd false)).2.1 with _ | w
    · rfl
    · rw [writeAt_getD, if_neg (by omega : ¬ p = c.hd)]

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
