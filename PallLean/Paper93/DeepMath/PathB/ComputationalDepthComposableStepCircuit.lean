import PallLean.Paper93.DeepMath.PathB.ComputationalDepthWireTreeCircuit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthComposableCircuitSnapshot

/-!
# Faithful-machine circuit simulation: the Boolean step trees

Second brick for discharging `ComposablePSubsetPpoly`.  The snapshot brick proved the
exact transition equations of the real `ComposableMachine` semantics; those equations
still mention real-run values (`(run …).hd`, `.tp.getD …`).  This file re-expresses one
full step as **syntactic wire trees over the snapshot ports themselves** and proves the
re-expression exact:

* ports `CPort M S` = tape cells `⊕` one-hot head bits `⊕` one-hot control bits, with
  the real-run valuation `snapV`;
* `scanT` — the scanned bit as a one-hot select `⋁_p head_p ∧ cell_p`;
* select gadgets `selScanT` / `selStateT` / `selHeadT` — one-hot dispatch over the
  scanned bit, the control state, and the head position (the head dispatch is the
  linear-size OR that absorbs the reset-to-zero move);
* step trees `cellT` / `headT` / `ctrlT` and the readout `acceptT`, with hardwired
  transition-table constants (`writtenBit`, `stepStateHead`) — no substitute model;
* **`weval_stepTreeOf` (proved)**: on the real snapshot, every step tree evaluates to
  the time-`t+1` snapshot bit, for every port, including halted self-loops and all four
  moves — the only hypothesis is that the current head lies inside the snapshot;
* **exact volume formulas** and the slot bound `stepV`, polynomial in the snapshot
  width `S` and the state count `QM M`.

No lower bound and no complexity claim lives here: this is the semantic layer of the
standard `P ⊆ P/poly` tableau, stated against the faithful model.
-/

namespace PallLean.Paper93.DeepMath.PathB.ComposableStepCircuit

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDynamics (stepStateHead step_via_stepStateHead)
open PallLean.Paper93.DeepMath.PathB.CookLevinWrite (writtenBit step_tape_getD_head)
open PallLean.Paper93.DeepMath.PathB.CookLevinTransition (step_tape_getD_ne_all)
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- Number of control states. -/
def QM (M : Machine) : ℕ := Fintype.card M.State

variable (M : Machine) (S : ℕ)

/-- Snapshot ports: tape cell `p`, one-hot head bit `p`, one-hot control bit `q`. -/
def CPort : Type := Fin S ⊕ Fin S ⊕ Fin (QM M)

/-- Cell port. -/
def cellP (p : Fin S) : CPort M S := Sum.inl p
/-- Head port. -/
def headP (p : Fin S) : CPort M S := Sum.inr (Sum.inl p)
/-- Control port. -/
def ctrlP (q : Fin (QM M)) : CPort M S := Sum.inr (Sum.inr q)

/-- The real-run snapshot valuation of the ports at time `t`. -/
noncomputable def snapV (x : List Bool) (t : ℕ) : CPort M S → Bool
  | Sum.inl p => (run M t (init M x)).tp.getD p.val false
  | Sum.inr (Sum.inl p) => decide ((run M t (init M x)).hd = p.val)
  | Sum.inr (Sum.inr q) => decide (Fintype.equivFin M.State (run M t (init M x)).st = q)

@[simp] theorem snapV_cell (x : List Bool) (t : ℕ) (p : Fin S) :
    snapV M S x t (cellP M S p) = (run M t (init M x)).tp.getD p.val false := rfl

@[simp] theorem snapV_head (x : List Bool) (t : ℕ) (p : Fin S) :
    snapV M S x t (headP M S p) = decide ((run M t (init M x)).hd = p.val) := rfl

@[simp] theorem snapV_ctrl (x : List Bool) (t : ℕ) (q : Fin (QM M)) :
    snapV M S x t (ctrlP M S q) = decide (Fintype.equivFin M.State (run M t (init M x)).st = q) :=
  rfl

/-! ### Transition-table constants -/

/-- The state carried by control index `q`. -/
noncomputable def stN (q : Fin (QM M)) : M.State := (Fintype.equivFin M.State).symm q

/-- Next control index under scanned bit `b` (position-independent). -/
noncomputable def nextStIdx (q : Fin (QM M)) (b : Bool) : Fin (QM M) :=
  Fintype.equivFin M.State (stepStateHead M (stN M q) 0 b).1

/-- Next head position from control index `q`, head `p`, scanned bit `b`. -/
noncomputable def nextHd (q : Fin (QM M)) (p : ℕ) (b : Bool) : ℕ :=
  (stepStateHead M (stN M q) p b).2

/-- The bit left under the head, from control index `q` and scanned bit `b`. -/
noncomputable def wBit (q : Fin (QM M)) (b : Bool) : Bool := writtenBit M (stN M q) b

/-- The next state does not depend on the head position. -/
theorem stepStateHead_fst (s : M.State) (p : ℕ) (b : Bool) :
    (stepStateHead M s p b).1 = (stepStateHead M s 0 b).1 := by
  unfold stepStateHead
  by_cases hh : M.halt s <;> simp [hh]

/-! ### The step trees -/

/-- The scanned bit: `⋁_p head_p ∧ cell_p`. -/
def scanT : WTree (CPort M S) :=
  orListW ((List.finRange S).map fun p =>
    .bin (fun a b => a && b) (.port (headP M S p)) (.port (cellP M S p)))

/-- Dispatch on the scanned bit. -/
def selScanT (g : Bool → WTree (CPort M S)) : WTree (CPort M S) :=
  .bin (fun a b => a || b)
    (.bin (fun a b => a && b) (scanT M S) (g true))
    (.bin (fun a b => a && b) (.un (fun a => !a) (scanT M S)) (g false))

/-- One-hot dispatch on the control state. -/
def selStateT (g : Fin (QM M) → WTree (CPort M S)) : WTree (CPort M S) :=
  orListW ((List.finRange (QM M)).map fun q =>
    .bin (fun a b => a && b) (.port (ctrlP M S q)) (g q))

/-- One-hot dispatch on the head position (linear-size OR — this is what absorbs the
reset-to-zero move: the new head value is a hardwired constant per window). -/
def selHeadT (g : Fin S → WTree (CPort M S)) : WTree (CPort M S) :=
  orListW ((List.finRange S).map fun p =>
    .bin (fun a b => a && b) (.port (headP M S p)) (g p))

/-- Next cell bit `p`: the written bit under the head, a copy elsewhere. -/
noncomputable def cellT (p : Fin S) : WTree (CPort M S) :=
  .bin (fun a b => a || b)
    (.bin (fun a b => a && b) (.port (headP M S p))
      (selStateT M S fun q => selScanT M S fun b => .cst (wBit M q b)))
    (.bin (fun a b => a && b) (.un (fun a => !a) (.port (headP M S p))) (.port (cellP M S p)))

/-- Next head bit `p`: hardwired transition table over (state, head, scanned). -/
noncomputable def headT (p : Fin S) : WTree (CPort M S) :=
  selStateT M S fun q => selHeadT M S fun p' => selScanT M S fun b =>
    .cst (decide (nextHd M q p'.val b = p.val))

/-- Next control bit `q`: hardwired transition table over (state, scanned). -/
noncomputable def ctrlT (q : Fin (QM M)) : WTree (CPort M S) :=
  selStateT M S fun q' => selScanT M S fun b => .cst (decide (nextStIdx M q' b = q))

/-- The acceptance readout. -/
noncomputable def acceptT : WTree (CPort M S) :=
  selStateT M S fun q => .cst (M.accept (stN M q))

/-- The step tree of each port. -/
noncomputable def stepTreeOf : CPort M S → WTree (CPort M S)
  | Sum.inl p => cellT M S p
  | Sum.inr (Sum.inl p) => headT M S p
  | Sum.inr (Sum.inr q) => ctrlT M S q

/-! ### Evaluation on the real snapshot -/

variable {M S}

theorem weval_scanT (x : List Bool) (t : ℕ)
    (hhd : (run M t (init M x)).hd < S) :
    weval (scanT M S) (snapV M S x t)
      = (run M t (init M x)).tp.getD (run M t (init M x)).hd false := by
  have h := any_finRange_select (run M t (init M x)).hd hhd
    (fun p : Fin S => (run M t (init M x)).tp.getD p.val false)
  rw [scanT, weval_orListW, List.any_map]
  simp only [Function.comp_def, weval, snapV_head, snapV_cell]
  exact h

theorem weval_selScanT (g : Bool → WTree (CPort M S)) (v : CPort M S → Bool) :
    weval (selScanT M S g) v = weval (g (weval (scanT M S) v)) v := by
  cases h : weval (scanT M S) v <;> simp [selScanT, weval, h]

theorem weval_selStateT (x : List Bool) (t : ℕ) (g : Fin (QM M) → WTree (CPort M S)) :
    weval (selStateT M S g) (snapV M S x t)
      = weval (g (Fintype.equivFin M.State (run M t (init M x)).st)) (snapV M S x t) := by
  have h := any_finRange_select_fin (Fintype.equivFin M.State (run M t (init M x)).st)
    (fun q : Fin (QM M) => weval (g q) (snapV M S x t))
  rw [selStateT, weval_orListW, List.any_map]
  simp only [Function.comp_def, weval, snapV_ctrl]
  exact h

theorem weval_selHeadT (x : List Bool) (t : ℕ) (g : Fin S → WTree (CPort M S))
    (hhd : (run M t (init M x)).hd < S) :
    weval (selHeadT M S g) (snapV M S x t)
      = weval (g ⟨(run M t (init M x)).hd, hhd⟩) (snapV M S x t) := by
  have h := any_finRange_select (run M t (init M x)).hd hhd
    (fun p : Fin S => weval (g p) (snapV M S x t))
  rw [selHeadT, weval_orListW, List.any_map]
  simp only [Function.comp_def, weval, snapV_head]
  exact h

/-- The one-hot control dispatch lands on the real state. -/
theorem stN_equivFin (x : List Bool) (t : ℕ) :
    stN M (Fintype.equivFin M.State (run M t (init M x)).st) = (run M t (init M x)).st := by
  rw [stN, Equiv.symm_apply_apply]

/-! ### The exact step equations, tree side = machine side -/

/-- **Next cell bit.** -/
theorem weval_cellT (x : List Bool) (t : ℕ) (p : Fin S)
    (hhd : (run M t (init M x)).hd < S) :
    weval (cellT M S p) (snapV M S x t) = snapV M S x (t + 1) (cellP M S p) := by
  have hwrite : weval (selStateT M S fun q => selScanT M S fun b => .cst (wBit M q b))
      (snapV M S x t)
      = writtenBit M (run M t (init M x)).st
          ((run M t (init M x)).tp.getD (run M t (init M x)).hd false) := by
    rw [weval_selStateT, weval_selScanT, weval_scanT x t hhd]
    simp only [weval, wBit]
    rw [stN_equivFin]
  rw [snapV_cell, run_succ]
  by_cases hp : (run M t (init M x)).hd = p.val
  · rw [show p.val = (run M t (init M x)).hd from hp.symm, step_tape_getD_head]
    simp only [cellT, weval, snapV_head, snapV_cell]
    rw [show decide ((run M t (init M x)).hd = p.val) = true from by simp [hp]]
    simp only [Bool.true_and, Bool.not_true, Bool.false_and, Bool.or_false]
    exact hwrite
  · rw [step_tape_getD_ne_all M _ p.val (fun h => hp (h.symm))]
    simp only [cellT, weval, snapV_head, snapV_cell]
    rw [show decide ((run M t (init M x)).hd = p.val) = false from by simp [hp]]
    simp only [Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_or]

/-- **Next head bit** (reset move included: the target position is a hardwired constant
per (state, head, scanned) window). -/
theorem weval_headT (x : List Bool) (t : ℕ) (p : Fin S)
    (hhd : (run M t (init M x)).hd < S) :
    weval (headT M S p) (snapV M S x t) = snapV M S x (t + 1) (headP M S p) := by
  rw [headT, weval_selStateT, weval_selHeadT x t _ hhd, weval_selScanT, weval_scanT x t hhd]
  simp only [weval, nextHd, snapV_head, stN_equivFin, run_succ,
    (step_via_stepStateHead M (run M t (init M x))).2]

/-- **Next control bit.** -/
theorem weval_ctrlT (x : List Bool) (t : ℕ) (q : Fin (QM M))
    (hhd : (run M t (init M x)).hd < S) :
    weval (ctrlT M S q) (snapV M S x t) = snapV M S x (t + 1) (ctrlP M S q) := by
  rw [ctrlT, weval_selStateT, weval_selScanT, weval_scanT x t hhd]
  simp only [weval, nextStIdx, snapV_ctrl, stN_equivFin, run_succ,
    (step_via_stepStateHead M (run M t (init M x))).1, stepStateHead_fst]

/-- **THE STEP THEOREM.**  On the real snapshot, every step tree computes the next
snapshot bit — all ports, all moves (reset included), halted self-loops included. -/
theorem weval_stepTreeOf (x : List Bool) (t : ℕ) (pt : CPort M S)
    (hhd : (run M t (init M x)).hd < S) :
    weval (stepTreeOf M S pt) (snapV M S x t) = snapV M S x (t + 1) pt := by
  rcases pt with p | p | q
  · exact weval_cellT x t p hhd
  · exact weval_headT x t p hhd
  · exact weval_ctrlT x t q hhd

/-- **The acceptance readout is exact** (no head hypothesis needed). -/
theorem weval_acceptT (x : List Bool) (t : ℕ) :
    weval (acceptT M S) (snapV M S x t) = M.accept (run M t (init M x)).st := by
  rw [acceptT, weval_selStateT]
  simp only [weval]
  rw [stN_equivFin]

/-! ### Exact volumes -/

variable (M S)

theorem wvol_scanT : wvol (scanT M S) = 4 * S + 1 := by
  rw [scanT, wvol_orListW, List.map_map]
  rw [show ((fun t => wvol t) ∘ fun p : Fin S =>
      WTree.bin (fun a b => a && b) (.port (headP M S p)) (.port (cellP M S p)))
    = fun _ => 3 from by funext p; simp [Function.comp, wvol]]
  rw [sum_map_const, List.length_map, List.length_finRange]
  omega

theorem wvol_selScanT (g : Bool → WTree (CPort M S)) :
    wvol (selScanT M S g) = wvol (g true) + wvol (g false) + 8 * S + 6 := by
  simp only [selScanT, wvol, wvol_scanT]
  omega

theorem wvol_selStateT (g : Fin (QM M) → WTree (CPort M S)) (G : ℕ)
    (hG : ∀ q, wvol (g q) = G) :
    wvol (selStateT M S g) = QM M * (G + 2) + QM M + 1 := by
  rw [selStateT, wvol_orListW, List.map_map]
  rw [show ((fun t => wvol t) ∘ fun q : Fin (QM M) =>
      WTree.bin (fun a b => a && b) (.port (ctrlP M S q)) (g q))
    = fun _ => G + 2 from by funext q; simp [Function.comp, wvol, hG q]; omega]
  rw [sum_map_const, List.length_map, List.length_finRange]

theorem wvol_selHeadT (g : Fin S → WTree (CPort M S)) (G : ℕ)
    (hG : ∀ p, wvol (g p) = G) :
    wvol (selHeadT M S g) = S * (G + 2) + S + 1 := by
  rw [selHeadT, wvol_orListW, List.map_map]
  rw [show ((fun t => wvol t) ∘ fun p : Fin S =>
      WTree.bin (fun a b => a && b) (.port (headP M S p)) (g p))
    = fun _ => G + 2 from by funext p; simp [Function.comp, wvol, hG p]; omega]
  rw [sum_map_const, List.length_map, List.length_finRange]

theorem wvol_ctrlT (q : Fin (QM M)) :
    wvol (ctrlT M S q) = QM M * (8 * S + 10) + QM M + 1 := by
  rw [ctrlT, wvol_selStateT M S _ (8 * S + 8)
    (fun q' => by rw [wvol_selScanT]; simp [wvol]; omega)]

theorem wvol_headT (p : Fin S) :
    wvol (headT M S p) = QM M * (S * (8 * S + 10) + S + 3) + QM M + 1 := by
  rw [headT, wvol_selStateT M S _ (S * (8 * S + 8 + 2) + S + 1)
    (fun q' => by
      rw [wvol_selHeadT M S _ (8 * S + 8)
        (fun p' => by rw [wvol_selScanT]; simp [wvol]; omega)])]

theorem wvol_cellT (p : Fin S) :
    wvol (cellT M S p) = QM M * (8 * S + 10) + QM M + 8 := by
  simp only [cellT, wvol]
  rw [wvol_selStateT M S _ (8 * S + 8)
    (fun q' => by rw [wvol_selScanT]; simp [wvol]; omega)]
  ring

theorem wvol_acceptT : wvol (acceptT M S) = QM M * 3 + QM M + 1 := by
  rw [acceptT, wvol_selStateT M S _ 1 (fun q => rfl)]

/-- The uniform slot size: the sum of the three per-port step-tree volumes. -/
def stepV : ℕ :=
  (QM M * (S * (8 * S + 10) + S + 3) + QM M + 1)
    + (QM M * (8 * S + 10) + QM M + 8)
    + (QM M * (8 * S + 10) + QM M + 1)

theorem wvol_headT_le (p : Fin S) : wvol (headT M S p) ≤ stepV M S := by
  rw [wvol_headT, stepV]
  exact le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

theorem wvol_cellT_le (p : Fin S) : wvol (cellT M S p) ≤ stepV M S := by
  rw [wvol_cellT, stepV]
  exact le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)

theorem wvol_ctrlT_le (q : Fin (QM M)) : wvol (ctrlT M S q) ≤ stepV M S := by
  rw [wvol_ctrlT, stepV]
  exact Nat.le_add_left _ _

theorem wvol_stepTreeOf_le (pt : CPort M S) : wvol (stepTreeOf M S pt) ≤ stepV M S := by
  rcases pt with p | p | q
  · exact wvol_cellT_le M S p
  · exact wvol_headT_le M S p
  · exact wvol_ctrlT_le M S q

end PallLean.Paper93.DeepMath.PathB.ComposableStepCircuit

#print axioms PallLean.Paper93.DeepMath.PathB.ComposableStepCircuit.weval_stepTreeOf
#print axioms PallLean.Paper93.DeepMath.PathB.ComposableStepCircuit.weval_acceptT
#print axioms PallLean.Paper93.DeepMath.PathB.ComposableStepCircuit.wvol_stepTreeOf_le
