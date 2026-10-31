import PallLean.Paper93.DeepMath.PathB.ComputationalDepthComposableStepCircuit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATCircuitSeparationBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitClockBounds3

/-!
# `P ⊆ P/poly` for the faithful model: the seam discharged

Final brick of the machine-to-circuit route.  For every language `L` in the
repository's faithful uniform `P` (a `ComposableMachine` deciding `L` on every input
within a `PolyBounded` clock), the length-`n` slices of `L` have circuits of size
`n^K + K` in the genuine `CGate` DAG model.  Concretely:

* `pidx` — linearisation of the snapshot ports into wire positions;
* `initGates` — the closed input layer: cells load the input word (padding `false`),
  head and control bits load their one-hot time-`0` values;
* `stepTrees` / `unrollC` — `T(n)` step layers of fixed-slot wire trees, followed by
  the compiled acceptance readout as the circuit's last wire;
* **`unrollC_spec` (proved)** — the grand induction: from any wire state holding the
  time-`t₀` snapshot, the unrolled circuit ends with
  `M.accept (run M (t₀+t) (init M x)).st` on its last wire;
* **`circuitFor_computes` (proved)** — the assembled circuit computes
  `lengthSlice L n` exactly;
* **`circuitFor_length` (proved)** — the exact gate count, polynomially bounded via
  the `PB` closure kit and `PolyBounded T`;
* **`composableP_subset_Ppoly` (proved)** — `ComposablePSubsetPpoly` holds:
  `∀ L, InP L → PolyCBudget (lengthSlice L)`;
* **capstones** — the SAT-circuit separation bridge with its simulation seam
  discharged: `NFrameCircuitLowerBoundTarget SATFamily → SAT_not_in_P`,
  unconditionally in the seam.

What remains after this file is exactly one statement, and it is not touched here:
`∀ k, ∃ n, n^k + k < cbudget (SATFamily n)` — the superpolynomial SAT circuit lower
bound, the open problem itself.
-/

namespace PallLean.Paper93.DeepMath.PathB.ComposablePpolyDischarge

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.ComposableStepCircuit
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitClockBounds3 (PB_const PB_id PB_le PB_add PB_mul)

variable {n : ℕ}

/-! ### Port linearisation -/

/-- Wire position of each snapshot port. -/
def pidx (M : Machine) (S : ℕ) : CPort M S → ℕ
  | Sum.inl p => p.val
  | Sum.inr (Sum.inl p) => S + p.val
  | Sum.inr (Sum.inr q) => S + S + q.val

theorem pidx_lt (M : Machine) (S : ℕ) (pt : CPort M S) :
    pidx M S pt < S + S + QM M := by
  rcases pt with p | p | q
  · have := p.isLt; simp only [pidx]; omega
  · have := p.isLt; simp only [pidx]; omega
  · have := q.isLt; simp only [pidx]; omega

/-! ### The input layer -/

/-- The closed initial layer: input cells, one-hot head at `0`, one-hot start state. -/
noncomputable def initGates (M : Machine) (n S : ℕ) : List (CGate n) :=
  ((List.finRange S).map fun p =>
      if h : p.val < n then CGate.var ⟨p.val, h⟩ else CGate.cst false)
    ++ (((List.finRange S).map fun p => CGate.cst (decide (0 = p.val)))
    ++ ((List.finRange (QM M)).map fun q =>
        CGate.cst (decide (Fintype.equivFin M.State M.start = q))))

theorem initGates_length (M : Machine) (n S : ℕ) :
    (initGates M n S).length = S + S + QM M := by
  simp [initGates]
  omega

theorem initGates_closed (M : Machine) (n S : ℕ) :
    ∀ g ∈ initGates M n S, IsClosedGate g := by
  intro g hg
  simp only [initGates, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨p, _, rfl⟩ | ⟨p, _, rfl⟩ | ⟨q, _, rfl⟩
  · by_cases h : p.val < n
    · rw [dif_pos h]; trivial
    · rw [dif_neg h]; trivial
  · trivial
  · trivial

/-- `getD` through a `finRange`-map. -/
theorem getD_map_finRange {m : ℕ} (f : Fin m → Bool) (i : ℕ) (h : i < m) :
    ((List.finRange m).map f).getD i false = f ⟨i, h⟩ := by
  rw [List.getD_eq_getElem ((List.finRange m).map f) false (by simpa using h)]
  simp

/-- The word loaded on the tape, read at any position. -/
theorem wordOfFin_getD (x' : Fin n → Bool) (j : ℕ) :
    (wordOfFin x').getD j false = if h : j < n then x' ⟨j, h⟩ else false := by
  by_cases h : j < n
  · rw [dif_pos h,
      List.getD_eq_getElem (wordOfFin x') false (by rw [wordOfFin_length]; exact h)]
    simp [wordOfFin]
  · rw [dif_neg h]
    exact List.getD_eq_default _ _ (by rw [wordOfFin_length]; omega)

/-- The initial layer's values are exactly the time-`0` snapshot. -/
theorem initVals_at (M : Machine) (S : ℕ) (x' : Fin n → Bool) (pt : CPort M S) :
    ((initGates M n S).map (closedEval x')).getD (pidx M S pt) false
      = snapV M S (wordOfFin x') 0 pt := by
  have hl1 : (((List.finRange S).map fun p : Fin S =>
      if h : p.val < n then CGate.var ⟨p.val, h⟩ else CGate.cst false).map
        (closedEval x')).length = S := by simp
  have hl2 : (((List.finRange S).map fun p : Fin S =>
      CGate.cst (decide (0 = p.val))).map (closedEval x')).length = S := by simp
  rcases pt with p | p | q
  · -- cell port
    show ((initGates M n S).map (closedEval x')).getD p.val false = _
    rw [initGates, List.map_append, List.getD_append _ _ false p.val (by rw [hl1]; exact p.isLt)]
    rw [List.map_map, getD_map_finRange _ p.val p.isLt]
    have hsnap : snapV M S (wordOfFin x') 0 (Sum.inl p)
        = (wordOfFin x').getD p.val false := by
      show (run M 0 (init M (wordOfFin x'))).tp.getD p.val false = _
      rw [run_zero]
      rfl
    rw [hsnap, wordOfFin_getD]
    by_cases h : p.val < n
    · rw [dif_pos h]
      simp only [Function.comp_apply, dif_pos h]
      rfl
    · rw [dif_neg h]
      simp only [Function.comp_apply, dif_neg h]
      rfl
  · -- head port
    show ((initGates M n S).map (closedEval x')).getD (S + p.val) false = _
    rw [initGates, List.map_append,
      List.getD_append_right _ _ false (S + p.val) (by rw [hl1]; omega)]
    rw [hl1, show S + p.val - S = p.val from by omega]
    rw [List.map_append, List.getD_append _ _ false p.val (by rw [hl2]; exact p.isLt)]
    rw [List.map_map, getD_map_finRange _ p.val p.isLt]
    show closedEval x' (CGate.cst (decide (0 = p.val))) = _
    show decide (0 = p.val) = _
    show _ = decide ((run M 0 (init M (wordOfFin x'))).hd = p.val)
    rw [run_zero]
    rfl
  · -- control port
    show ((initGates M n S).map (closedEval x')).getD (S + S + q.val) false = _
    rw [initGates, List.map_append,
      List.getD_append_right _ _ false (S + S + q.val) (by rw [hl1]; omega)]
    rw [hl1, show S + S + q.val - S = S + q.val from by omega]
    rw [List.map_append,
      List.getD_append_right _ _ false (S + q.val) (by rw [hl2]; omega)]
    rw [hl2, show S + q.val - S = q.val from by omega]
    rw [List.map_map, getD_map_finRange _ q.val q.isLt]
    show closedEval x' (CGate.cst (decide (Fintype.equivFin M.State M.start = q))) = _
    show decide (Fintype.equivFin M.State M.start = q) = _
    show _ = decide (Fintype.equivFin M.State (run M 0 (init M (wordOfFin x'))).st = q)
    rw [run_zero]
    rfl

/-! ### The step layer and its tree list -/

/-- The step trees in port order. -/
noncomputable def stepTrees (M : Machine) (S : ℕ) : List (WTree (CPort M S)) :=
  ((List.finRange S).map fun p => cellT M S p)
    ++ (((List.finRange S).map fun p => headT M S p)
    ++ ((List.finRange (QM M)).map fun q => ctrlT M S q))

theorem stepTrees_length (M : Machine) (S : ℕ) :
    (stepTrees M S).length = S + S + QM M := by
  simp [stepTrees]
  omega

theorem stepTrees_wvol_le (M : Machine) (S : ℕ) :
    ∀ t ∈ stepTrees M S, wvol t ≤ stepV M S := by
  intro t ht
  simp only [stepTrees, List.mem_append, List.mem_map] at ht
  rcases ht with ⟨p, _, rfl⟩ | ⟨p, _, rfl⟩ | ⟨q, _, rfl⟩
  · exact wvol_cellT_le M S p
  · exact wvol_headT_le M S p
  · exact wvol_ctrlT_le M S q

/-- `getD` through a `finRange`-map, any element type. -/
theorem getD_map_finRange' {α : Type} (d : α) {m : ℕ} (f : Fin m → α) (i : ℕ) (h : i < m) :
    ((List.finRange m).map f).getD i d = f ⟨i, h⟩ := by
  rw [List.getD_eq_getElem ((List.finRange m).map f) d (by simpa using h)]
  simp

theorem stepTrees_getD (M : Machine) (S : ℕ) (pt : CPort M S) :
    (stepTrees M S).getD (pidx M S pt) (WTree.cst false) = stepTreeOf M S pt := by
  have hl1 : ((List.finRange S).map fun p => cellT M S p).length = S := by simp
  have hl2 : ((List.finRange S).map fun p => headT M S p).length = S := by simp
  rcases pt with p | p | q
  · show (stepTrees M S).getD p.val _ = cellT M S p
    rw [stepTrees, List.getD_append _ _ _ p.val (by rw [hl1]; exact p.isLt)]
    rw [getD_map_finRange' _ _ p.val p.isLt]
  · show (stepTrees M S).getD (S + p.val) _ = headT M S p
    rw [stepTrees, List.getD_append_right _ _ _ (S + p.val) (by rw [hl1]; omega)]
    rw [hl1, show S + p.val - S = p.val from by omega]
    rw [List.getD_append _ _ _ p.val (by rw [hl2]; exact p.isLt)]
    rw [getD_map_finRange' _ _ p.val p.isLt]
  · show (stepTrees M S).getD (S + S + q.val) _ = ctrlT M S q
    rw [stepTrees, List.getD_append_right _ _ _ (S + S + q.val) (by rw [hl1]; omega)]
    rw [hl1, show S + S + q.val - S = S + q.val from by omega]
    rw [List.getD_append_right _ _ _ (S + q.val) (by rw [hl2]; omega)]
    rw [hl2, show S + q.val - S = q.val from by omega]
    rw [getD_map_finRange' _ _ q.val q.isLt]

theorem stepTrees_get (M : Machine) (S : ℕ) (pt : CPort M S)
    (h : pidx M S pt < (stepTrees M S).length) :
    (stepTrees M S).get ⟨pidx M S pt, h⟩ = stepTreeOf M S pt := by
  rw [List.get_eq_getElem,
    ← List.getD_eq_getElem (stepTrees M S) (WTree.cst false) h]
  exact stepTrees_getD M S pt

/-! ### The unrolled circuit -/

/-- `t` step layers from offset `off` with port positions `pos`, then the compiled
acceptance readout (the circuit's final wire). -/
noncomputable def unrollC (M : Machine) (S : ℕ) :
    (CPort M S → ℕ) → ℕ → ℕ → List (CGate n)
  | pos, off, 0 => compileW pos off (acceptT M S)
  | pos, off, t + 1 =>
      layerW pos (stepV M S) off (stepTrees M S)
        ++ unrollC M S (fun pt => off + (pidx M S pt + 1) * stepV M S - 1)
            (off + (S + S + QM M) * stepV M S) t

theorem unrollC_length (M : Machine) (S : ℕ) :
    ∀ (t : ℕ) (pos : CPort M S → ℕ) (off : ℕ),
      (unrollC (n := n) M S pos off t).length
        = t * ((S + S + QM M) * stepV M S) + wvol (acceptT M S) := by
  intro t
  induction t with
  | zero =>
    intro pos off
    show (compileW pos off (acceptT M S)).length = _
    rw [compileW_length]
    ring
  | succ t ih =>
    intro pos off
    show (layerW pos (stepV M S) off (stepTrees M S)
        ++ unrollC M S _ (off + (S + S + QM M) * stepV M S) t).length = _
    rw [List.length_append, layerW_length _ _ _ _ (stepTrees_wvol_le M S), ih,
      stepTrees_length]
    ring

/-- The head stays inside the snapshot along the run. -/
theorem run_hd_lt (M : Machine) (x' : Fin n → Bool) {S τ : ℕ} (h : n + τ < S) :
    (run M τ (init M (wordOfFin x'))).hd < S := by
  have hb := (run_bounds M (wordOfFin x') τ).1
  rw [wordOfFin_length] at hb
  omega

/-- **The grand induction.**  From any wire state holding the time-`t₀` snapshot, the
unrolled circuit appends its block and finishes with the acceptance bit of the real run
at time `t₀ + t` on its final wire. -/
theorem unrollC_spec (M : Machine) (S : ℕ) (x' : Fin n → Bool) :
    ∀ (t t₀ : ℕ) (pos : CPort M S → ℕ) (vals : List Bool),
      n + t₀ + t ≤ S →
      (∀ pt : CPort M S, pos pt < vals.length ∧
        vals.getD (pos pt) false = snapV M S (wordOfFin x') t₀ pt) →
      ∃ w' : List Bool,
        runFrom x' vals (unrollC M S pos vals.length t) = vals ++ w' ∧
        w'.length = t * ((S + S + QM M) * stepV M S) + wvol (acceptT M S) ∧
        (vals ++ w').getD ((vals ++ w').length - 1) false
          = M.accept (run M (t₀ + t) (init M (wordOfFin x'))).st := by
  intro t
  induction t with
  | zero =>
    intro t₀ pos vals hS hpos
    obtain ⟨w, hrun, hlen, hval⟩ :=
      compileW_spec (acceptT M S) x' pos (snapV M S (wordOfFin x') t₀) vals hpos
    refine ⟨w, hrun, by rw [hlen]; ring, ?_⟩
    rw [show (vals ++ w).length - 1 = vals.length + wvol (acceptT M S) - 1 from by
      rw [List.length_append, hlen]]
    rw [hval, weval_acceptT, Nat.add_zero]
  | succ t ih =>
    intro t₀ pos vals hS hpos
    have hhd : (run M t₀ (init M (wordOfFin x'))).hd < S :=
      run_hd_lt M x' (by omega)
    have hV1 : 1 ≤ stepV M S := by
      have h8 : (8 : ℕ) ≤ QM M * (8 * S + 10) + QM M + 8 := Nat.le_add_left 8 _
      have := Nat.le_add_left (QM M * (8 * S + 10) + QM M + 8)
        (QM M * (S * (8 * S + 10) + S + 3) + QM M + 1)
      have := Nat.le_add_right
        ((QM M * (S * (8 * S + 10) + S + 3) + QM M + 1) + (QM M * (8 * S + 10) + QM M + 8))
        (QM M * (8 * S + 10) + QM M + 1)
      unfold stepV
      omega
    obtain ⟨w₀, hrun₀, hlen₀, hval₀⟩ :=
      layerW_spec x' pos (snapV M S (wordOfFin x') t₀) (stepV M S) (stepTrees M S)
        vals (stepTrees_wvol_le M S) hpos
    have hL₀ : (vals ++ w₀).length = vals.length + (S + S + QM M) * stepV M S := by
      rw [List.length_append, hlen₀, stepTrees_length]
    have hpos' : ∀ pt : CPort M S,
        (fun pt => vals.length + (pidx M S pt + 1) * stepV M S - 1) pt < (vals ++ w₀).length ∧
        (vals ++ w₀).getD ((fun pt => vals.length + (pidx M S pt + 1) * stepV M S - 1) pt) false
          = snapV M S (wordOfFin x') (t₀ + 1) pt := by
      intro pt
      have hidx : pidx M S pt < (stepTrees M S).length := by
        rw [stepTrees_length]; exact pidx_lt M S pt
      have hmul : (pidx M S pt + 1) * stepV M S ≤ (S + S + QM M) * stepV M S :=
        Nat.mul_le_mul_right _ (pidx_lt M S pt)
      have hone : 1 ≤ (pidx M S pt + 1) * stepV M S :=
        le_trans hV1 (Nat.le_mul_of_pos_left _ (by omega))
      constructor
      · show vals.length + (pidx M S pt + 1) * stepV M S - 1 < (vals ++ w₀).length
        rw [hL₀]
        omega
      · show (vals ++ w₀).getD (vals.length + (pidx M S pt + 1) * stepV M S - 1) false
          = snapV M S (wordOfFin x') (t₀ + 1) pt
        rw [hval₀ ⟨pidx M S pt, hidx⟩, stepTrees_get M S pt hidx]
        exact weval_stepTreeOf (wordOfFin x') t₀ pt hhd
    obtain ⟨w₁, hrun₁, hlen₁, hval₁⟩ :=
      ih (t₀ + 1) (fun pt => vals.length + (pidx M S pt + 1) * stepV M S - 1)
        (vals ++ w₀) (by omega) hpos'
    refine ⟨w₀ ++ w₁, ?_, ?_, ?_⟩
    · show runFrom x' vals
        (layerW pos (stepV M S) vals.length (stepTrees M S)
          ++ unrollC M S (fun pt => vals.length + (pidx M S pt + 1) * stepV M S - 1)
              (vals.length + (S + S + QM M) * stepV M S) t) = vals ++ (w₀ ++ w₁)
      rw [runFrom_append, hrun₀, show vals.length + (S + S + QM M) * stepV M S
          = (vals ++ w₀).length from hL₀.symm, hrun₁, List.append_assoc]
    · rw [List.length_append, hlen₀, hlen₁, stepTrees_length]
      ring
    · rw [show vals ++ (w₀ ++ w₁) = (vals ++ w₀) ++ w₁ from (List.append_assoc _ _ _).symm]
      rw [hval₁, show t₀ + 1 + t = t₀ + (t + 1) from by omega]

/-! ### The assembled circuit -/

/-- The full circuit: input layer, `T₀` step layers, acceptance readout. -/
noncomputable def circuitFor (M : Machine) (n T₀ : ℕ) : List (CGate n) :=
  initGates M n (n + T₀ + 1)
    ++ unrollC M (n + T₀ + 1) (pidx M (n + T₀ + 1))
        ((n + T₀ + 1) + (n + T₀ + 1) + QM M) T₀

theorem circuitFor_length (M : Machine) (n T₀ : ℕ) :
    (circuitFor M n T₀).length
      = ((n + T₀ + 1) + (n + T₀ + 1) + QM M)
        + (T₀ * (((n + T₀ + 1) + (n + T₀ + 1) + QM M) * stepV M (n + T₀ + 1))
          + wvol (acceptT M (n + T₀ + 1))) := by
  rw [circuitFor, List.length_append, initGates_length, unrollC_length]

/-- **The circuit computes the length slice (proved).** -/
theorem circuitFor_computes (M : Machine) (L : List Bool → Bool) (T : ℕ → ℕ)
    (hDec : Decides M L T) (n : ℕ) :
    computes (circuitFor M n (T n)) (lengthSlice L n) := by
  intro x'
  have hclock : T (wordOfFin x').length = T n := by rw [wordOfFin_length]
  have hinit := runFrom_closed x' (initGates M n (n + T n + 1)) [] (initGates_closed M n _)
  rw [List.nil_append] at hinit
  have hlen0 : ((initGates M n (n + T n + 1)).map (closedEval x')).length
      = (n + T n + 1) + (n + T n + 1) + QM M := by
    rw [List.length_map, initGates_length]
  have hpos0 : ∀ pt : CPort M (n + T n + 1),
      pidx M (n + T n + 1) pt < ((initGates M n (n + T n + 1)).map (closedEval x')).length ∧
      ((initGates M n (n + T n + 1)).map (closedEval x')).getD (pidx M (n + T n + 1) pt) false
        = snapV M (n + T n + 1) (wordOfFin x') 0 pt := by
    intro pt
    exact ⟨by rw [hlen0]; exact pidx_lt M _ pt, initVals_at M _ x' pt⟩
  obtain ⟨w', hrun, hlen, hval⟩ :=
    unrollC_spec M (n + T n + 1) x' (T n) 0 (pidx M (n + T n + 1))
      ((initGates M n (n + T n + 1)).map (closedEval x')) (by omega) hpos0
  unfold output
  rw [circuitFor, runFrom_append, hinit,
    show ((n + T n + 1) + (n + T n + 1) + QM M)
      = ((initGates M n (n + T n + 1)).map (closedEval x')).length from hlen0.symm,
    hrun]
  rw [show (initGates M n (n + T n + 1)
        ++ unrollC (n := n) M (n + T n + 1) (pidx M (n + T n + 1))
            ((initGates M n (n + T n + 1)).map (closedEval x')).length (T n)).length
      = (((initGates M n (n + T n + 1)).map (closedEval x')) ++ w').length from by
    rw [List.length_append, List.length_append, initGates_length, unrollC_length, hlen0, hlen]]
  rw [hval, Nat.zero_add]
  have := (hDec (wordOfFin x')).2
  rw [hclock] at this
  rw [show M.accept (run M (T n) (init M (wordOfFin x'))).st
      = decideOut M (wordOfFin x') (T n) from rfl, this]
  rfl

/-- The circuit witnesses the `cbudget` bound. -/
theorem cbudget_lengthSlice_le (M : Machine) (L : List Bool → Bool) (T : ℕ → ℕ)
    (hDec : Decides M L T) (n : ℕ) :
    cbudget (lengthSlice L n) ≤ (circuitFor M n (T n)).length :=
  Nat.sInf_le ⟨circuitFor M n (T n), circuitFor_computes M L T hDec n, rfl⟩

/-! ### Polynomial size -/

/-- Polynomially bounded functions fit under `n^K + K`. -/
theorem polyBounded_nk {g : ℕ → ℕ} (hg : PolyBounded g) :
    ∃ K : ℕ, ∀ n, g n ≤ n ^ K + K := by
  obtain ⟨c, k, h⟩ := hg
  refine ⟨c * 2 ^ k + k + c + 1, fun n => ?_⟩
  match n with
  | 0 =>
    have h0 := h 0
    have h1 : c * (0 + 1) ^ k = c := by norm_num
    rw [h1] at h0
    have hz : (0 : ℕ) ^ (c * 2 ^ k + k + c + 1) = 0 := Nat.zero_pow (by omega)
    rw [hz]
    omega
  | Nat.succ m =>
    show g (m + 1) ≤ (m + 1) ^ (c * 2 ^ k + k + c + 1) + (c * 2 ^ k + k + c + 1)
    have hb := h (m + 1)
    have hp1 : (m + 1 + 1) ^ k ≤ (2 * (m + 1)) ^ k := Nat.pow_le_pow_left (by omega) k
    have hp2 : (2 * (m + 1)) ^ k = 2 ^ k * (m + 1) ^ k := by rw [mul_pow]
    have hchain : g (m + 1) ≤ c * 2 ^ k * (m + 1) ^ k := by
      calc g (m + 1) ≤ c * (m + 1 + 1) ^ k := hb
        _ ≤ c * (2 * (m + 1)) ^ k := Nat.mul_le_mul_left c hp1
        _ = c * 2 ^ k * (m + 1) ^ k := by rw [hp2]; ring
    have hfin : c * 2 ^ k * (m + 1) ^ k
        ≤ (m + 1) ^ (c * 2 ^ k + k + c + 1) + (c * 2 ^ k + k + c + 1) := by
      match m with
      | 0 =>
        have e1 : c * 2 ^ k * (0 + 1) ^ k = c * 2 ^ k := by norm_num
        have e2 : (0 + 1 : ℕ) ^ (c * 2 ^ k + k + c + 1) = 1 := one_pow _
        rw [e1, e2]
        omega
      | Nat.succ m' =>
        show c * 2 ^ k * (m' + 2) ^ k
          ≤ (m' + 2) ^ (c * 2 ^ k + k + c + 1) + (c * 2 ^ k + k + c + 1)
        have hsplit : (m' + 2) ^ (c * 2 ^ k + k + c + 1)
            = (m' + 2) ^ (c * 2 ^ k + c + 1) * (m' + 2) ^ k := by
          rw [← pow_add]
          congr 1
          omega
        have hpow2 : (2 : ℕ) ^ (c * 2 ^ k + c + 1) ≤ (m' + 2) ^ (c * 2 ^ k + c + 1) :=
          Nat.pow_le_pow_left (by omega) _
        have hm2 : c * 2 ^ k + c + 1 < 2 ^ (c * 2 ^ k + c + 1) :=
          Nat.lt_two_pow_self
        have hc2k : c * 2 ^ k ≤ (m' + 2) ^ (c * 2 ^ k + c + 1) := by omega
        have hmono : c * 2 ^ k * (m' + 2) ^ k
            ≤ (m' + 2) ^ (c * 2 ^ k + c + 1) * (m' + 2) ^ k :=
          Nat.mul_le_mul_right _ hc2k
        rw [hsplit]
        omega
    omega

/-- The gate count of `circuitFor` is polynomially bounded when the clock is. -/
theorem circuitFor_length_polyBounded (M : Machine) (T : ℕ → ℕ) (hT : PolyBounded T) :
    PolyBounded (fun n => (circuitFor M n (T n)).length) := by
  have hSf : PolyBounded (fun n => n + T n + 1) :=
    PB_add (PB_add PB_id hT) (PB_const 1)
  have hw : PolyBounded (fun n => (n + T n + 1) + (n + T n + 1) + QM M) :=
    PB_add (PB_add hSf hSf) (PB_const (QM M))
  have hlin : PolyBounded (fun n => 8 * (n + T n + 1) + 10) :=
    PB_add (PB_mul (PB_const 8) hSf) (PB_const 10)
  have hquad : PolyBounded (fun n =>
      (n + T n + 1) * (8 * (n + T n + 1) + 10) + (n + T n + 1) + 3) :=
    PB_add (PB_add (PB_mul hSf hlin) hSf) (PB_const 3)
  have hQ : PolyBounded (fun _ : ℕ => QM M) := PB_const (QM M)
  have hstepV : PolyBounded (fun n => stepV M (n + T n + 1)) := by
    unfold stepV
    exact PB_add
      (PB_add (PB_add (PB_add (PB_mul hQ hquad) hQ) (PB_const 1))
        (PB_add (PB_add (PB_mul hQ hlin) hQ) (PB_const 8)))
      (PB_add (PB_add (PB_mul hQ hlin) hQ) (PB_const 1))
  have hacc : PolyBounded (fun n => wvol (acceptT M (n + T n + 1))) := by
    have : ∀ n : ℕ, wvol (acceptT M (n + T n + 1)) = QM M * 3 + QM M + 1 :=
      fun n => wvol_acceptT M (n + T n + 1)
    exact PB_le (fun n => le_of_eq (this n)) (PB_const (QM M * 3 + QM M + 1))
  have htot : PolyBounded (fun n =>
      ((n + T n + 1) + (n + T n + 1) + QM M)
        + (T n * (((n + T n + 1) + (n + T n + 1) + QM M) * stepV M (n + T n + 1))
          + wvol (acceptT M (n + T n + 1)))) :=
    PB_add hw (PB_add (PB_mul hT (PB_mul hw hstepV)) hacc)
  exact PB_le (fun n => le_of_eq (circuitFor_length M n (T n))) htot

/-! ### THE SEAM, DISCHARGED -/

/-- **`P ⊆ P/poly` for the faithful model (proved).**  Every language decided by a
faithful polynomial-time `ComposableMachine` has polynomially bounded circuit budget on
its fixed-length slices.  The one seam of the SAT-circuit separation bridge is now a
theorem. -/
theorem composableP_subset_Ppoly : ComposablePSubsetPpoly := by
  intro L hL
  obtain ⟨M, T, hT, hDec⟩ := hL
  obtain ⟨K, hK⟩ := polyBounded_nk (circuitFor_length_polyBounded M T hT)
  exact ⟨K, fun n => le_trans (cbudget_lengthSlice_le M L T hDec n) (hK n)⟩

/-! ### The capstones, seam-free -/

/-- **The circuit route, standard plumbing complete.**  A super-polynomial `cbudget`
lower bound for the exact SAT slices proves `SAT ∉ P` — no simulation hypothesis
remains. -/
theorem sat_circuit_lower_bound_implies_target
    (hard : NFrameCircuitLowerBoundTarget SATFamily) : SAT_not_in_P :=
  sat_target_implies_SAT_not_in_P composableP_subset_Ppoly hard

/-- Fully expanded: the single remaining statement between this repository and
`SAT ∉ P` is the superpolynomial SAT circuit lower bound itself. -/
theorem sat_superpoly_cbudget_implies_SAT_not_in_P
    (hard : ∀ k, ∃ n, n ^ k + k < cbudget (SATFamily n)) :
    ¬ PallLean.Paper93.DeepMath.PathB.SeparationTarget.InP SATLang :=
  faithful_separation_capstone (fun L hL => composableP_subset_Ppoly L hL) hard

end PallLean.Paper93.DeepMath.PathB.ComposablePpolyDischarge

#print axioms PallLean.Paper93.DeepMath.PathB.ComposablePpolyDischarge.composableP_subset_Ppoly
#print axioms PallLean.Paper93.DeepMath.PathB.ComposablePpolyDischarge.sat_circuit_lower_bound_implies_target
#print axioms PallLean.Paper93.DeepMath.PathB.ComposablePpolyDischarge.sat_superpoly_cbudget_implies_SAT_not_in_P
