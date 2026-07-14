import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinWholeRun

/-!
# Cook–Levin M1 — the INIT phase, the full run from `init`, and the `InP`/`Decides` packaging

`wholeRun` (CookLevinWholeRun) runs the master from the **LOOPCHK round-start** config (head at `SEP` low `2v+2`).
But the forced initial config is `init masterM x = ⟨start, 0, x⟩` — group `INIT`, head `0`.  The **INIT phase**
(`scanRightSep`, group `0`) scans right from head `0` to `SEP`, then seams to `LOOPCHK` — bridging `init` to the
round-start.  Composing INIT with `wholeRun` gives the complete run from the forced initial config.

We then build the concrete `encode` (assignment + index `v` ↦ doubled `LSENT counterᵛ SEP data REND` tape), prove
`encode` satisfies `RoundInv`, and package `masterM` with the polynomial clock as a **promise `Decides`** witness:
on well-formed inputs the master halts in polynomial time reading the doubled `a_v`.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinInP

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinMasterSim
open PallLean.Paper93.DeepMath.PathB.CookLevinMasterRound
open PallLean.Paper93.DeepMath.PathB.CookLevinScanRightSep (scanRightSep run_scan_right_halt)
open PallLean.Paper93.DeepMath.PathB.CookLevinPhaseBounds
open PallLean.Paper93.DeepMath.PathB.CookLevinRoundInvariant
open PallLean.Paper93.DeepMath.PathB.CookLevinWholeRun

/-- **The INIT phase.**  From the forced initial config `⟨start, 0, T⟩` (group `INIT`, head `0`), the master scans
right past `LSENT` and the `v` counters to `SEP`, then seams to `LOOPCHK` at the `SEP` low cell `2v+2` — the
round-start config `wholeRun` expects.  The scan's non-`SEP` and `SEP` facts come from `RoundInv` (`lsent`, `ctr`,
`seplo`, `sephi`); it takes `2(v+1)+2 + 1` steps. -/
theorem init_phase (T : List Bool) (v D : ℕ) (h : RoundInv T v D) :
    run masterM (2 * (v + 1) + 2 + 1) ⟨(0, 0, false, false), 0, T⟩ = ⟨(1, 0, false, false), 2 * v + 2, T⟩ := by
  have hns : ∀ i, i < v + 1 → (!(T.getD (0 + 2 * i) false) && T.getD (0 + 2 * i + 1) false) = false := by
    intro i hi
    simp only [Nat.zero_add]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [show 2 * 0 + 1 = 1 from by norm_num, h.lsent]; simp
    · rw [(h.ctr i (by omega) (by omega)).1, (h.ctr i (by omega) (by omega)).2]; simp
  have hsep : (!(T.getD (0 + 2 * (v + 1)) false) && T.getD (0 + 2 * (v + 1) + 1) false) = true := by
    simp only [Nat.zero_add]
    rw [show 2 * (v + 1) + 1 = 2 * v + 3 from by omega, show 2 * (v + 1) = 2 * v + 2 from by omega,
      h.seplo, h.sephi]
    decide
  have eINIT : run masterM (2 * (v + 1) + 2) ⟨(0, 0, false, false), 0, T⟩
      = ⟨(0, 2, T.getD (2 * v + 2) false, false), 2 * v + 3, T⟩ := by
    rw [show (⟨(0, 0, false, false), 0, T⟩ : Cfg masterM) = embedScanR 0 ⟨(0, false), 0, T⟩ from rfl,
      sim_run_INIT (2 * (v + 1) + 2) ⟨(0, false), 0, T⟩ (scanRightSep_no_early_halt hns),
      run_scan_right_halt T 0 false (v + 1) hns hsep, Nat.zero_add,
      show 2 * (v + 1) + 1 = 2 * v + 3 from by omega, show 2 * (v + 1) = 2 * v + 2 from by omega]
    rfl
  rw [run_add, eINIT, run_one, seam_INIT, show 2 * v + 3 - 1 = 2 * v + 2 from by omega]

/-! ## The full run from `init`, and the promise `Decides` -/

/-- **The complete run from the forced initial config.**  INIT phase then `wholeRun`: from `⟨start, 0, T⟩` the
master halts in the `HALT` group reading the input's doubled `a_v`.  Total clock `2(v+1)+2 + 1 + (clockSum v D + 7)`. -/
theorem fullRun (T : List Bool) (v D : ℕ) (hv : v ≤ D) (h : RoundInv T v D) :
    ∃ T', run masterM (2 * (v + 1) + 2 + 1 + (clockSum v D + 7)) ⟨(0, 0, false, false), 0, T⟩
        = ⟨(9, 0, T.getD (2 * v + 4 + 2 * v) false, false), 4, T'⟩ := by
  obtain ⟨T', hrun⟩ := wholeRun v T D hv h
  exact ⟨T', by rw [run_add, init_phase T v D h, hrun]⟩

/-- **Promise `Decides`.**  On a well-formed input `T` (satisfying `RoundInv T v D`, `v ≤ D` — a doubled
`LSENT counterᵛ SEP a₀…a_{D-1} REND` tape), the master, started from its forced initial config, **halts** and its
decision bit is exactly the input's doubled `a_v` (`= T.getD (2v+4+2v) false`).  This is `HaltsBy`/`decideOut` at the
explicit clock — a promise-restricted `Decides` (the machine is only claimed correct on well-formed inputs). -/
theorem readAv_promise (T : List Bool) (v D : ℕ) (hv : v ≤ D) (h : RoundInv T v D) :
    HaltsBy masterM T (2 * (v + 1) + 2 + 1 + (clockSum v D + 7))
    ∧ decideOut masterM T (2 * (v + 1) + 2 + 1 + (clockSum v D + 7)) = T.getD (2 * v + 4 + 2 * v) false := by
  obtain ⟨T', hrun⟩ := fullRun T v D hv h
  refine ⟨?_, ?_⟩
  · unfold HaltsBy
    rw [master_forced_init, hrun]
    rfl
  · unfold decideOut
    rw [master_forced_init, hrun]
    rfl

/-- **Polynomial clock.**  The full-run clock is `≤ 32(D+1)² + 2D + 12` — quadratic in the data count `D` (`≤ |T|`),
hence polynomial in the input length.  So the promise `Decides` runs in polynomial time. -/
theorem readAv_clock_poly (v D : ℕ) (hv : v ≤ D) :
    2 * (v + 1) + 2 + 1 + (clockSum v D + 7) ≤ 32 * (D + 1) * (D + 1) + 2 * D + 12 := by
  have := clockSum_le_quad v D hv
  omega

/-! ## A concrete encoding realising the promise -/

/-- Double each bit: `b ↦ b b` (the data-region doubling). -/
def double : List Bool → List Bool
  | [] => []
  | b :: rest => b :: b :: double rest

theorem double_length (l : List Bool) : (double l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons b rest ih => simp only [double, List.length_cons, ih]; omega

/-- Reading the doubled list at `2j` or `2j+1` returns the `j`-th original bit. -/
theorem double_getD (l : List Bool) : ∀ j,
    (double l).getD (2 * j) false = l.getD j false ∧ (double l).getD (2 * j + 1) false = l.getD j false := by
  induction l with
  | nil => intro j; simp [double, List.getD_nil]
  | cons b rest ih =>
    intro j
    cases j with
    | zero => exact ⟨rfl, rfl⟩
    | succ j =>
      rw [double, show 2 * (j + 1) = 2 * j + 1 + 1 from by omega]
      simp only [List.getD_cons_succ]
      exact ih j

/-- `getD` on the left part of an append. -/
theorem getD_append_lt {l l' : List Bool} {n : ℕ} (h : n < l.length) :
    (l ++ l').getD n false = l.getD n false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, List.getD_eq_getElem?_getD]

/-- `getD` on the right part of an append. -/
theorem getD_append_ge {l l' : List Bool} {n : ℕ} (h : l.length ≤ n) :
    (l ++ l').getD n false = l'.getD (n - l.length) false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h, List.getD_eq_getElem?_getD]

/-- `getD` inside a `true`-block. -/
theorem getD_replicate_true {n i : ℕ} (h : i < n) : (List.replicate n true).getD i false = true := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos h]; rfl

/-- Peel a doubled-cell (2-element) prefix. -/
theorem getD_pair_ge {a b : Bool} {l' : List Bool} {n : ℕ} (h : 2 ≤ n) :
    ([a, b] ++ l').getD n false = l'.getD (n - 2) false := getD_append_ge h

/-- Peel the counter (`replicate`) block. -/
theorem getD_repl_ge {l' : List Bool} {m n : ℕ} (h : m ≤ n) :
    (List.replicate m true ++ l').getD n false = l'.getD (n - m) false := by
  rw [getD_append_ge (by rwa [List.length_replicate]), List.length_replicate]

/-- Peel the doubled-data block. -/
theorem getD_data_ge {a l' : List Bool} {n : ℕ} (h : 2 * a.length ≤ n) :
    (double a ++ l').getD n false = l'.getD (n - 2 * a.length) false := by
  rw [getD_append_ge (by rwa [double_length]), double_length]

/-- The concrete SAT-witness encoding: doubled `LSENT counterᵛ SEP (double assignment) REND`.  `SEP` low sits at
`2v+2`; the counter block is `2v` ones (`v` doubled `11` pairs); the data is the doubled assignment. -/
def encode (assignment : List Bool) (v : ℕ) : List Bool :=
  [true, false] ++ (List.replicate (2 * v) true ++ ([false, true] ++ (double assignment ++ [true, false])))

/-- **The encoding is well-formed.**  `encode assignment v` satisfies `RoundInv` with `v` counters and
`assignment.length` data pairs — so the whole `read a_v` machinery applies to it. -/
theorem encode_roundInv (assignment : List Bool) (v : ℕ) :
    RoundInv (encode assignment v) v assignment.length := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- counters: getD (2i), getD (2i+1) = true for 1 ≤ i ≤ v
    intro i hi1 hi2
    refine ⟨?_, ?_⟩ <;>
    · rw [encode, getD_pair_ge (by omega), getD_append_lt (by rw [List.length_replicate]; omega)]
      exact getD_replicate_true (by omega)
  · -- SEP low = 0
    rw [encode, getD_pair_ge (by omega), getD_repl_ge (by omega),
      show 2 * v + 2 - 2 - 2 * v = 0 from by omega, getD_append_lt (by simp)]
    rfl
  · -- SEP high = 1
    rw [encode, getD_pair_ge (by omega), getD_repl_ge (by omega),
      show 2 * v + 3 - 2 - 2 * v = 1 from by omega, getD_append_lt (by simp)]
    rfl
  · -- data pairs equal (both = assignment[j])
    intro j hj
    have key : ∀ p, p < 2 * assignment.length →
        (encode assignment v).getD (2 * v + 4 + p) false = (double assignment).getD p false := by
      intro p hp
      rw [encode, getD_pair_ge (by omega), getD_repl_ge (by omega), getD_pair_ge (by omega),
        show 2 * v + 4 + p - 2 - 2 * v - 2 = p from by omega, getD_append_lt (by rw [double_length]; omega)]
    rw [show 2 * v + 5 + 2 * j = 2 * v + 4 + (2 * j + 1) from by omega,
      show 2 * v + 4 + 2 * j = 2 * v + 4 + (2 * j) from rfl,
      key (2 * j) (by omega), key (2 * j + 1) (by omega),
      (double_getD assignment j).1, (double_getD assignment j).2]
  · -- REND low = 1
    rw [encode, getD_pair_ge (by omega), getD_repl_ge (by omega), getD_pair_ge (by omega),
      getD_data_ge (by omega),
      show 2 * v + 4 + 2 * assignment.length - 2 - 2 * v - 2 - 2 * assignment.length = 0 from by omega]
    rfl
  · -- REND high = 0
    rw [encode, getD_pair_ge (by omega), getD_repl_ge (by omega), getD_pair_ge (by omega),
      getD_data_ge (by omega),
      show 2 * v + 5 + 2 * assignment.length - 2 - 2 * v - 2 - 2 * assignment.length = 1 from by omega]
    rfl
  · -- LSENT high (pos 1) = 0
    rw [encode, getD_append_lt (by simp)]
    rfl

/-- **Cook–Levin M1 read-`a_v`, fully concrete.**  For any assignment and valid index `v < |assignment|`, the master,
started from its forced initial config on the concrete encoding `encode assignment v`, **halts** and its decision bit
is exactly the assignment's `v`-th bit `assignment.getD v false`, within `2(v+1)+2 + 1 + (clockSum v |assignment| + 7)`
steps — polynomial in `|assignment|` (`readAv_clock_poly`).  This is a concrete, halting, provably-correct,
polynomial-time variable-lookup machine on the faithful `ComposableMachine` model. -/
theorem readAv_encoded (assignment : List Bool) (v : ℕ) (hv : v < assignment.length) :
    HaltsBy masterM (encode assignment v) (2 * (v + 1) + 2 + 1 + (clockSum v assignment.length + 7))
    ∧ decideOut masterM (encode assignment v) (2 * (v + 1) + 2 + 1 + (clockSum v assignment.length + 7))
        = assignment.getD v false := by
  have hav : (encode assignment v).getD (2 * v + 4 + 2 * v) false = assignment.getD v false := by
    rw [encode, getD_pair_ge (by omega), getD_repl_ge (by omega), getD_pair_ge (by omega),
      show 2 * v + 4 + 2 * v - 2 - 2 * v - 2 = 2 * v from by omega,
      getD_append_lt (by rw [double_length]; omega)]
    exact (double_getD assignment v).1
  have H := readAv_promise (encode assignment v) v assignment.length (by omega) (encode_roundInv assignment v)
  rwa [hav] at H

end PallLean.Paper93.DeepMath.PathB.CookLevinInP
