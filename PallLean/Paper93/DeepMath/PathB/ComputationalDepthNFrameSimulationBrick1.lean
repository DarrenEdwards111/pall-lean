import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameGodMovePrinciple

/-!
# N-Frame simulation, brick 1: rebasing circuits onto wires + the one-step coordinate theorem

Item 1 of the plan — discharging the conditional theorem's `simulation` hypothesis (polytime decider ⇒ polynomial
`cbudget`) — needs Cook–Levin-style tabling: iterate a machine's step function as circuit layers.  The load-bearing
infrastructure is **rebasing**: taking a circuit that reads *inputs* and re-pointing it at existing *wires*, so layers
compose.  This file builds that brick and proves the one-step coordinate theorem.

  `rebaseGate` / `rebase` — re-point a circuit at wires: input reads `var i` become wire reads at `base i`; internal
        references shift by the layer's start position `L`.
  `rebase_go` — **PROVED, the rebasing theorem**: running the rebased circuit from a wire state `vals` (with all base
        positions in range) appends exactly what the original circuit computes from the *extracted* inputs
        `i ↦ vals[base i]`.  Layers compose without disturbing earlier wires.
  `step_coord` — **PROVED, the one-step coordinate theorem**: if `c` computes a step-coordinate function `Sᵢ` of the
        machine configuration, then from any wire state holding the current configuration at positions `pos`, the rebased
        `c` appends `c.length` wires whose last carries `Sᵢ (config)` — with the **size bound** `(rebase … c).length =
        c.length` (rebasing is free).

## Honest scope — the first brick of a multi-brick project

This brick gives layer composition its engine: circuits-on-wires with exact semantics and zero size overhead.  The
remaining bricks of item 1, named: (2) the full `B`-coordinate step layer (all coordinates of the next configuration, with
position bookkeeping); (3) `T`-fold iteration (the tableau — size `≤ T · Σᵢ|cᵢ| + B`); (4) hooking a concrete machine
model's step function into per-coordinate circuits (the RAM window analysis); (5) the polynomial cost accounting that
discharges `simulation`.  Until all are in place, `simulation` remains a named hypothesis of the conditional theorem.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {B : ℕ}

/-- Re-point one gate at wires: input reads become wire reads at `base`; internal references shift by the layer start
`L`. -/
def rebaseGate (base : Fin B → ℕ) (L : ℕ) : CGate B → CGate B
  | .var i => .un id (base i)
  | .cst b => .cst b
  | .un op j => .un op (j + L)
  | .bin op j k => .bin op (j + L) (k + L)

/-- Re-point a whole circuit at wires. -/
def rebase (base : Fin B → ℕ) (L : ℕ) (c : List (CGate B)) : List (CGate B) :=
  c.map (rebaseGate base L)

/-- **Rebasing is free (proved)**: the gate count is unchanged. -/
theorem rebase_length (base : Fin B → ℕ) (L : ℕ) (c : List (CGate B)) :
    (rebase base L c).length = c.length :=
  List.length_map ..

/-- **The rebasing theorem (proved).**  Running the rebased circuit from wire state `vals` appends exactly what the
original computes from the extracted inputs `i ↦ vals[base i]` — for any ambient input `x` (the rebased gates read no
inputs), from any partial original wire state `w`. -/
theorem rebase_go (base : Fin B → ℕ) (vals : List Bool)
    (hbase : ∀ i, base i < vals.length) (x : Fin B → Bool) (c : List (CGate B)) :
    ∀ w : List Bool,
      runFrom x (vals ++ w) (rebase base vals.length c)
        = vals ++ runFrom (fun i => vals.getD (base i) false) w c := by
  induction c with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have hgate : evalGate x (vals ++ w) (rebaseGate base vals.length g)
        = evalGate (fun i => vals.getD (base i) false) w g := by
      cases g with
      | var i =>
        show id ((vals ++ w).getD (base i) false) = vals.getD (base i) false
        rw [List.getD_append vals w false (base i) (hbase i)]
        rfl
      | cst b => rfl
      | un op j =>
        show op ((vals ++ w).getD (j + vals.length) false) = op (w.getD j false)
        rw [List.getD_append_right vals w false (j + vals.length) (Nat.le_add_left _ _),
          Nat.add_sub_cancel]
      | bin op j k =>
        show op ((vals ++ w).getD (j + vals.length) false)
            ((vals ++ w).getD (k + vals.length) false)
          = op (w.getD j false) (w.getD k false)
        rw [List.getD_append_right vals w false (j + vals.length) (Nat.le_add_left _ _),
          List.getD_append_right vals w false (k + vals.length) (Nat.le_add_left _ _),
          Nat.add_sub_cancel, Nat.add_sub_cancel]
    show runFrom x ((vals ++ w) ++ [evalGate x (vals ++ w) (rebaseGate base vals.length g)])
        (rebase base vals.length gs)
      = vals ++ runFrom (fun i => vals.getD (base i) false)
          (w ++ [evalGate (fun i => vals.getD (base i) false) w g]) gs
    rw [hgate, List.append_assoc]
    exact ih (w ++ [evalGate (fun i => vals.getD (base i) false) w g])

/-- **The one-step coordinate theorem (proved).**  If `c` computes the step-coordinate `Sᵢ` of the configuration, then
from any wire state holding the current configuration at positions `pos`, the rebased `c` appends `c.length` wires whose
*last* carries `Sᵢ (config)` — at zero size overhead. -/
theorem step_coord (c : List (CGate B)) (hc : 0 < c.length)
    (Si : (Fin B → Bool) → Bool) (hcomp : computes c Si)
    (vals : List Bool) (pos : Fin B → ℕ) (hpos : ∀ i, pos i < vals.length)
    (cfg : Fin B → Bool) (hcfg : ∀ i, vals.getD (pos i) false = cfg i)
    (x : Fin B → Bool) :
    (runFrom x vals (rebase pos vals.length c)).getD (vals.length + c.length - 1) false
      = Si cfg := by
  have hx : (fun i => vals.getD (pos i) false) = cfg := funext hcfg
  have hrun := rebase_go pos vals hpos x c []
  rw [hx, List.append_nil] at hrun
  rw [hrun]
  have hout := hcomp cfg
  unfold output at hout
  rw [List.getD_append_right vals _ false (vals.length + c.length - 1) (by omega)]
  rw [show vals.length + c.length - 1 - vals.length = c.length - 1 by omega]
  exact hout

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.rebase_go
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.step_coord
