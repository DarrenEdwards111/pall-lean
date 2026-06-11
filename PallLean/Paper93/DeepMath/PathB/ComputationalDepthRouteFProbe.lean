import Mathlib.Tactic

/-!
# Route F tiny test — profile compression vs. the identity minor (SPDP rank gap at small scale)

A computational probe of the **Route F** mechanism (`CookLevinFrontierHyp`): the P-side Cook–Levin
compilation has *low* SPDP rank because, though the tableau has many cells, it has only **few distinct
"profiles"**, and *#profiles bounds the rank*.  The NP-side identity/Tseitin minor has *high* rank.  This
is the rank **gap** the whole separation rests on — here at the smallest scale, computed by `native_decide`.

`f2rank` is a Gaussian-elimination matrix rank over `F₂` (a clean computable stand-in for the partition /
SPDP rank).  Findings:

* `identity_full_rank` — the `4×4` identity minor has rank `4` (NP-side: full rank).
* `profile_compressed_low_rank` — a `6×4` matrix with only **2 distinct row-profiles** has rank `2`,
  **despite 6 rows** — profile compression bounds rank by #profiles, not size (P-side mechanism).
* `separable_rank_one` — a separable/product matrix has rank `1`.
* `f2rank_le_length` — **proved**: rank `≤` number of rows.  The honest refinement Route F needs is the
  *profile* bound rank `≤ #distinct profiles` (demonstrated computationally above); the open work is showing
  the actual Cook–Levin compilation has `poly(n)`-many profiles.

**Honest status.**  This shows the rank gap is real and the profile-compression mechanism works at tiny
scale — structural plausibility for `CookLevinFrontierHyp`.  It is **not** the bound itself: the open lemma
is that the *specific* Cook–Levin compilation at `n = 2⁸⁰⁴` has `≤ n²⁰⁰` profiles/rank, which no tiny test
establishes.
-/

namespace PallLean.Paper93.DeepMath.PathB.RouteFProbe

/-- F₂ vector add (xor, entrywise). -/
def vadd (a b : List Bool) : List Bool := List.zipWith xor a b

/-- Index of the first `true` (the leading entry of a row). -/
def leadIdx (row : List Bool) : Option ℕ := row.findIdx? id

/-- Reduce a row against accumulated pivots (Gaussian elimination over F₂). -/
def reduceRow (pivots : List (List Bool)) (row : List Bool) : List Bool :=
  pivots.foldl (fun r piv =>
    match leadIdx piv with
    | some i => if r.getD i false then vadd r piv else r
    | none => r) row

/-- **F₂ matrix rank** via Gaussian elimination: the number of pivots. -/
def f2rank (rows : List (List Bool)) : ℕ :=
  (rows.foldl (fun pivots row =>
    if (reduceRow pivots row).any id then pivots ++ [reduceRow pivots row] else pivots) []).length

/-! ### The rank gap at tiny scale (`native_decide`) -/

/-- NP-side: the `4×4` identity minor has **full** rank `4` (the high-rank Tseitin/identity-minor side). -/
theorem identity_full_rank :
    f2rank [[true,false,false,false],[false,true,false,false],
            [false,false,true,false],[false,false,false,true]] = 4 := by native_decide

/-- P-side **profile compression**: a `6×4` matrix with only **2 distinct row-profiles** has rank `2`,
*despite having 6 rows* — #profiles bounds the rank, not the size. -/
theorem profile_compressed_low_rank :
    f2rank [[true,true,false,false],[true,true,false,false],[true,true,false,false],
            [false,false,true,true],[false,false,true,true],[false,false,true,true]] = 2 := by
  native_decide

/-- P-side separable/product structure has rank `1`. -/
theorem separable_rank_one :
    f2rank [[true,false,true],[true,false,true],[true,false,true]] = 1 := by native_decide

/-! ### The proved bound: rank ≤ #rows (the trivial direction of profile compression) -/

theorem f2rank_le_length (rows : List (List Bool)) : f2rank rows ≤ rows.length := by
  unfold f2rank
  suffices h : ∀ (l acc : List (List Bool)),
      (l.foldl (fun pivots row =>
        if (reduceRow pivots row).any id then pivots ++ [reduceRow pivots row] else pivots)
        acc).length ≤ acc.length + l.length by
    simpa using h rows []
  intro l
  induction l with
  | nil => intro acc; simp
  | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons]
      by_cases hc : (reduceRow acc x).any id
      · simp only [hc, if_true]
        refine le_trans (ih _) ?_
        simp [List.length_append, List.length_cons]; omega
      · simp only [hc, if_false]
        refine le_trans (ih _) ?_
        simp [List.length_cons]

end PallLean.Paper93.DeepMath.PathB.RouteFProbe
