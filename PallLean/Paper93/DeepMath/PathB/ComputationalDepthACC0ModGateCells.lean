import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CircuitModel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameACC0Speedup

/-!
# Bridge — the concrete `ACC0Circuit` `MOD` gate is a low-cell symmetric leaf (proved)

The honest refinement of the count-tree bridge: where the naive Boolean translation (`toCTree`) gives `MOD` gates trivial
`{0,1}` leaves, the *real* `ACC0Circuit` `MOD` gate is a **symmetric leaf** — its value depends only on `weightOn S x` (the
number of set inputs in its support `S`), which lies in `{0, …, |S|}` and so takes at most `|S|+1` distinct values.  Hence the
gate factors through a `≤ |S|+1`-cell count, and its SAT is decided by a residue check over those `≤ |S|+1` weight-cells
(`modGate_satisfiable_iff`) — **linear in `|S|`**, not `2^{|S|}`.

This is exactly the symmetric structure that makes the cell-count method non-trivial: the `MOD` gate over inputs is the genuine
`MOD ∘ AND`-block leaf (`AND`-gates = single literals), with the low cell count the polynomial-degree method cannot exploit
for prime-power moduli.

## What is proved (clean axioms, no `sorry`)

* **`weightOn_le`** (PROVED) — `weightOn S x ≤ |S|`.
* **`weightOn_cells_le`** (PROVED) — `(image (weightOn S)).card ≤ |S|+1` (the symmetric leaf has linearly many cells).
* **`modGate_satisfiable_iff`** (PROVED) — `Satisfiable (eval (.mod q S t)) ↔ ∃ w ∈ image (weightOn S), (w : ZMod q) = t`
  (SAT over `≤ |S|+1` weight-cells).

## Honest scope

This is the symmetric-leaf cell bound for the concrete `MOD` gate (fast-SAT over `≤ |S|+1` weight-cells).  Combining many such
leaves through the count-tree (`modpe_tree_cells_le`) gives the quasipolynomial regime; the unconditional `NEXP ⊄ ACC⁰`
(P≠NP-strength) is not done here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModGateCells

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (eval)
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation (weightOn modQStatOn)
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup (Satisfiable)

variable {n : ℕ}

/-- **The support weight is at most `|S|` (PROVED).** -/
theorem weightOn_le (S : Finset (Fin n)) (x : Fin n → Bool) : weightOn S x ≤ S.card := by
  unfold weightOn
  calc (∑ i ∈ S, (if x i then 1 else 0)) ≤ ∑ _i ∈ S, 1 :=
        Finset.sum_le_sum (fun i _ => by split <;> simp)
    _ = S.card := by simp

/-- **The symmetric leaf has `≤ |S|+1` cells (PROVED).** -/
theorem weightOn_cells_le (S : Finset (Fin n)) :
    (Finset.univ.image (weightOn S)).card ≤ S.card + 1 := by
  refine le_trans (Finset.card_le_card ?_) (le_of_eq (Finset.card_range (S.card + 1)))
  intro w hw
  simp only [Finset.mem_image] at hw
  obtain ⟨x, _, rfl⟩ := hw
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (weightOn_le S x))

/-- **The `MOD` gate's SAT is decided by a residue check over its `≤ |S|+1` weight-cells (PROVED).** -/
theorem modGate_satisfiable_iff (q : ℕ) (S : Finset (Fin n)) (t : ZMod q) :
    Satisfiable (eval (.mod q S t)) ↔
      ∃ w ∈ Finset.univ.image (weightOn S), (w : ZMod q) = t := by
  unfold Satisfiable
  simp only [eval, decide_eq_true_eq, modQStatOn, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx⟩; exact ⟨weightOn S x, ⟨x, rfl⟩, hx⟩
  · rintro ⟨w, ⟨x, rfl⟩, hx⟩; exact ⟨x, hx⟩

/-!
**The `MOD` gate is a low-cell symmetric leaf, proved.**  It factors through `weightOn S` (`≤ |S|+1` cells), so its SAT is a
residue check over `≤ |S|+1` weight-cells — linear in `|S|`, the symmetric structure the polynomial method cannot exploit for
prime powers.  Feeding such leaves through the count-tree (`modpe_tree_cells_le`) gives the quasipolynomial regime.  Remaining
(open, not faked): the unconditional `NEXP ⊄ ACC⁰`.  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ModGateCells

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModGateCells.modGate_satisfiable_iff
