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

/-- Dropping a `¬p` prefix does not change the `p`-filter. -/
theorem filter_dropWhile_not {α : Type*} (p : α → Bool) (l : List α) :
    (l.dropWhile (fun x => !p x)).filter p = l.filter p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hunfold : (a :: l).dropWhile (fun x => !p x)
        = match !p a with | true => l.dropWhile (fun x => !p x) | false => a :: l := rfl
    cases hpa : p a with
    | true => rw [hunfold, hpa]; simp [List.filter_cons, hpa]
    | false => rw [hunfold, hpa]; simp only [Bool.not_false]; rw [List.filter_cons, hpa]; simp; exact ih

/-- **Walk = first-`k` confirmed blocks.**  The walk collects the block of each of the
first `k` `termSat`-confirmed terms (the ones the sound selector lands on, in order). -/
theorem termWalkVars_eq_filter (σstar : Restriction n) (sel : Clause n → Finset (Fin n)) :
    ∀ (k : ℕ) (cs : List (Clause n)),
      termWalkVars σstar sel cs k
        = ((cs.filter (termSat σstar)).take k).foldr (fun T acc => sel T ∪ acc) ∅ := by
  intro k
  induction k with
  | zero => intro cs; simp [termWalkVars]
  | succ k ih =>
    intro cs
    show (match cs.dropWhile (fun T => !termSat σstar T) with
      | [] => ∅ | T :: rest => sel T ∪ termWalkVars σstar sel rest k) = _
    have hfd : (cs.dropWhile (fun T => !termSat σstar T)).filter (termSat σstar)
        = cs.filter (termSat σstar) := filter_dropWhile_not (termSat σstar) cs
    cases hdw : cs.dropWhile (fun T => !termSat σstar T) with
    | nil =>
      rw [hdw] at hfd
      simp only [List.filter_nil] at hfd
      rw [← hfd]; simp
    | cons T rest =>
      rw [hdw] at hfd
      have hT : termSat σstar T = true := by
        have := dropWhile_head_not hdw; simpa using this
      rw [List.filter_cons, hT] at hfd
      show sel T ∪ termWalkVars σstar sel rest k
        = ((cs.filter (termSat σstar)).take (k + 1)).foldr (fun T acc => sel T ∪ acc) ∅
      rw [ih rest, ← hfd]
      simp

/-- **Recovery wrapper.**  If the walk collects exactly the path variables, then freeing
them from `σ*` returns `ρ` — `decode_encode_id` for the DNF walk, modulo the encoder bridge
`heq` (that the walk's output equals the path-variable set). -/
theorem termWalk_recovers_of_eq {ρ : Restriction n} {litList : List (Rung4Literal n)}
    {sel : Clause n → Finset (Fin n)} {cs : List (Clause n)} {k : ℕ}
    (hfree : ∀ v ∈ litList.map litVar, ρ v = none)
    (heq : termWalkVars (complete ρ litList) sel cs k = ((litList.map litVar).toFinset)) :
    freeOn (complete ρ litList) (termWalkVars (complete ρ litList) sel cs k) = ρ := by
  rw [heq]
  exact freeOn_complete_recover hfree (fun _ => List.mem_toFinset)

/-- With enough fuel, the walk collects the block of *every* `termSat`-confirmed term. -/
theorem termWalk_eq_filter_full (σstar : Restriction n) (sel : Clause n → Finset (Fin n))
    (cs : List (Clause n)) (k : ℕ) (h : (cs.filter (termSat σstar)).length ≤ k) :
    termWalkVars σstar sel cs k
      = (cs.filter (termSat σstar)).foldr (fun T acc => sel T ∪ acc) ∅ := by
  rw [termWalkVars_eq_filter, List.take_of_length_le h]

/-- **DNF decoder `decode_encode_id` (sound selector).**  The decoder recovers `ρ` from
`σ*` and the per-term blocks, with the single encoder bridge `hcollect`: the blocks of the
`σ*`-satisfied terms collect to the path-variable set.  Everything else (the sound selector,
the walk, the recovery) is discharged. -/
theorem termWalk_decode_encode {ρ : Restriction n} {litList : List (Rung4Literal n)}
    {sel : Clause n → Finset (Fin n)} {cs : List (Clause n)} {k : ℕ}
    (hfree : ∀ v ∈ litList.map litVar, ρ v = none)
    (hfuel : (cs.filter (termSat (complete ρ litList))).length ≤ k)
    (hcollect : (cs.filter (termSat (complete ρ litList))).foldr (fun T acc => sel T ∪ acc) ∅
        = (litList.map litVar).toFinset) :
    freeOn (complete ρ litList) (termWalkVars (complete ρ litList) sel cs k) = ρ := by
  apply termWalk_recovers_of_eq hfree
  rw [termWalk_eq_filter_full _ _ _ _ hfuel, hcollect]

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.termWalk_step
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.termWalk_decode_encode
