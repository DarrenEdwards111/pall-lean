import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAEmGadgetG

/-!
# Brick B of the ∀m `SlackComposes` campaign: general extraction + per-gadget necessity

The unwinding of an *arbitrary* circuit into a `GTree` — every gate shape
absorbed, out-of-range reads folded into constants — and the first pillar:

* **`extractG` / `extractG_eval` (proved)** — the fuel-indexed unwinding
  computes the wire at every in-range position, with no structural hypotheses
  on the circuit whatsoever;
* **`AEm_gadget_cnt_ne` (proved, S1)** — for every circuit computing `AEm m`
  and every gadget, the extracted tree cannot have all three gadget variables
  with leaf count 1: `gtree_split_cnt` would split the gadget's `allEq3`
  restriction (`AEm_gadget_g`), refuted by `allEq3_no_split`.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-- The general unwinding: every gate shape absorbed. -/
def extractG (c : List (CGate n)) : ℕ → ℕ → GTree n
  | 0, _ => .cst false
  | fuel + 1, w =>
    match c.getD w (.cst false) with
    | .var i => .leaf i
    | .cst b => .cst b
    | .un op j => if j < w then .un op (extractG c fuel j) else .cst (op false)
    | .bin op j k =>
        if j < w then
          if k < w then .node op (extractG c fuel j) (extractG c fuel k)
          else .un (fun v => op v false) (extractG c fuel j)
        else
          if k < w then .un (fun v => op false v) (extractG c fuel k)
          else .cst (op false false)

/-- **The unwinding computes the wire (proved)** — no structural hypotheses. -/
theorem extractG_eval {n : ℕ} (c : List (CGate n)) :
    ∀ (fuel w : ℕ), w < fuel → w < c.length →
      ∀ x, (extractG c fuel w).eval x = wire c x w := by
  intro fuel
  induction fuel with
  | zero => intro w hw _ _; exact absurd hw (Nat.not_lt_zero w)
  | succ fuel ih =>
    intro w hw hwlt x
    have hVlen : (runFrom x [] (c.take w)).length = w := by
      rw [runFrom_length, List.length_take]
      simp
      omega
    cases hg : c.getD w (.cst false) with
    | var i =>
      show (extractG c (fuel + 1) w).eval x = wire c x w
      simp only [extractG]
      rw [hg, wire_eq c x hwlt, hg]
      rfl
    | cst b =>
      simp only [extractG]
      rw [hg, wire_eq c x hwlt, hg]
      rfl
    | un op j =>
      simp only [extractG]
      rw [hg, wire_eq c x hwlt, hg]
      show (if j < w then GTree.un op (extractG c fuel j)
          else GTree.cst (op false)).eval x
        = evalGate x (runFrom x [] (c.take w)) (CGate.un op j)
      by_cases hj : j < w
      · rw [if_pos hj]
        show op ((extractG c fuel j).eval x)
          = op ((runFrom x [] (c.take w)).getD j false)
        rw [wire_prefix c x hj (le_of_lt hwlt), ih j (by omega) (by omega) x]
      · rw [if_neg hj]
        show op false = op ((runFrom x [] (c.take w)).getD j false)
        rw [List.getD_eq_default _ _ (by omega)]
    | bin op j k =>
      simp only [extractG]
      rw [hg, wire_eq c x hwlt, hg]
      show (if j < w then
          if k < w then GTree.node op (extractG c fuel j) (extractG c fuel k)
          else GTree.un (fun v => op v false) (extractG c fuel j)
        else
          if k < w then GTree.un (fun v => op false v) (extractG c fuel k)
          else GTree.cst (op false false)).eval x
        = evalGate x (runFrom x [] (c.take w)) (CGate.bin op j k)
      by_cases hj : j < w
      · by_cases hk : k < w
        · rw [if_pos hj, if_pos hk]
          show op ((extractG c fuel j).eval x) ((extractG c fuel k).eval x)
            = op ((runFrom x [] (c.take w)).getD j false)
              ((runFrom x [] (c.take w)).getD k false)
          rw [wire_prefix c x hj (le_of_lt hwlt), wire_prefix c x hk (le_of_lt hwlt),
            ih j (by omega) (by omega) x, ih k (by omega) (by omega) x]
        · rw [if_pos hj, if_neg hk]
          show op ((extractG c fuel j).eval x) false
            = op ((runFrom x [] (c.take w)).getD j false)
              ((runFrom x [] (c.take w)).getD k false)
          rw [wire_prefix c x hj (le_of_lt hwlt), ih j (by omega) (by omega) x,
            List.getD_eq_default (l := runFrom x [] (c.take w)) _ (by omega)]
      · by_cases hk : k < w
        · rw [if_neg hj, if_pos hk]
          show op false ((extractG c fuel k).eval x)
            = op ((runFrom x [] (c.take w)).getD j false)
              ((runFrom x [] (c.take w)).getD k false)
          rw [wire_prefix c x hk (le_of_lt hwlt), ih k (by omega) (by omega) x,
            List.getD_eq_default (l := runFrom x [] (c.take w)) _ (by omega)]
        · rw [if_neg hj, if_neg hk]
          show op false false
            = op ((runFrom x [] (c.take w)).getD j false)
              ((runFrom x [] (c.take w)).getD k false)
          rw [List.getD_eq_default (l := runFrom x [] (c.take w)) _ (by omega : (runFrom x [] (c.take w)).length ≤ j),
            List.getD_eq_default (l := runFrom x [] (c.take w)) _ (by omega : (runFrom x [] (c.take w)).length ≤ k)]

/-- The root unwinding computes the function. -/
theorem extractG_root {n : ℕ} (c : List (CGate n)) (f : (Fin n → Bool) → Bool)
    (hcomp : computes c f) (hs : 0 < c.length) :
    (extractG c c.length (c.length - 1)).eval = f := by
  funext x
  rw [extractG_eval c c.length (c.length - 1) (by omega) (by omega) x,
    ← output_eq_wire]
  exact hcomp x

/-- **S1, per-gadget necessity (proved)**: no gadget of `AEm m` can have all
three variables with leaf count 1 in the unwinding of any circuit. -/
theorem AEm_gadget_cnt_ne (m : ℕ) (c : List (CGate (3 * m)))
    (hcomp : computes c (AEm m)) (hs : 0 < c.length) (g : ℕ) (hg : g < m)
    (ha : 3 * g < 3 * m) (hb : 3 * g + 1 < 3 * m) (hc : 3 * g + 2 < 3 * m) :
    ¬ ((extractG c c.length (c.length - 1)).cnt ⟨3 * g, ha⟩ = 1
      ∧ (extractG c c.length (c.length - 1)).cnt ⟨3 * g + 1, hb⟩ = 1
      ∧ (extractG c c.length (c.length - 1)).cnt ⟨3 * g + 2, hc⟩ = 1) := by
  rintro ⟨hc1, hc2, hc3⟩
  have hsp := gtree_split_cnt (extractG c c.length (c.length - 1))
    ⟨3 * g, ha⟩ ⟨3 * g + 1, hb⟩ ⟨3 * g + 2, hc⟩
    (by intro he; have h' : 3 * g = 3 * g + 1 := congrArg Fin.val he; omega)
    (by intro he; have h' : 3 * g = 3 * g + 2 := congrArg Fin.val he; omega)
    (by intro he; have h' : 3 * g + 1 = 3 * g + 2 := congrArg Fin.val he; omega)
    (fun _ => true) hc1 hc2 hc3
  rw [extractG_root c (AEm m) hcomp hs] at hsp
  rw [AEm_gadget_g m g hg ha hb hc] at hsp
  rcases hsp with h | h | h
  · exact allEq3_no_split_a h
  · exact allEq3_no_split_b h
  · exact allEq3_no_split_c h

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.extractG_eval
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.AEm_gadget_cnt_ne
