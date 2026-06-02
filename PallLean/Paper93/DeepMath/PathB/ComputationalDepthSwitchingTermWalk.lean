import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingHastad
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingWalk

/-!
# The DNF decoder walk on the sound `termSat` selector

**STATUS: REAL.  THE WALK FOLD OVER THE SOUND SELECTOR.**

The decoder walks `cs`, at each step finding the first term satisfied under `σ*` (the sound
selector — `dropWhile_eq_of_prefix` lands on it since the prefix is non-`termSat`), collects
that term's block variables, and recurses on the terms after it.  Unlike the CNF walk this
needs no `hpre`: the selector is `termSat`, which is sound by `find_termSat_first_processed`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- The decoder's collected variable set: walk `cs`, collect the block of each
`termSat`-confirmed term, advance past it. -/
def termWalkVars (σstar : Restriction n) (sel : Clause n → Finset (Fin n)) :
    List (Clause n) → ℕ → Finset (Fin n)
  | _, 0 => ∅
  | cs, k + 1 =>
    match cs.dropWhile (fun T => !termSat σstar T) with
    | [] => ∅
    | T :: rest => sel T ∪ termWalkVars σstar sel rest k

theorem termWalkVars_zero (σstar : Restriction n) (sel : Clause n → Finset (Fin n))
    (cs : List (Clause n)) : termWalkVars σstar sel cs 0 = ∅ := rfl

/-- **One-step walk correctness.**  When the first `termSat` term in `cs` is `T` (with the
prefix non-`termSat`), the walk collects `sel T` and recurses on the terms after `T`. -/
theorem termWalk_step (σstar : Restriction n) (sel : Clause n → Finset (Fin n))
    {cs : List (Clause n)} {pre : List (Clause n)} {T : Clause n} {rest : List (Clause n)}
    (k : ℕ) (hcs : cs = pre ++ T :: rest)
    (hpre : ∀ T' ∈ pre, termSat σstar T' = false) (hT : termSat σstar T = true) :
    termWalkVars σstar sel cs (k + 1) = sel T ∪ termWalkVars σstar sel rest k := by
  have hdw : cs.dropWhile (fun T => !termSat σstar T) = T :: rest := by
    rw [hcs]
    exact dropWhile_eq_of_prefix (fun T' hT' => by simp [hpre T' hT']) (by simp [hT])
  show (match cs.dropWhile (fun T => !termSat σstar T) with
    | [] => ∅ | T :: rest => sel T ∪ termWalkVars σstar sel rest k) = _
  rw [hdw]

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.termWalk_step
