import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModGateCells
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CellRecursion

/-!
# Bridge — a real circuit over a `MOD`-gate layer has quasipolynomial cell count (proved)

The payoff of the concrete↔abstract bridge: combining the symmetric-leaf bound for the real `MOD` gate
(`weightOn_cells_le`: `≤ |S|+1` cells) with the abstract recursion (`cells_factor`: a gate's cells `≤` product over its
sub-circuits' cells) gives the genuine quasipolynomial cell bound for an actual depth-2 circuit whose bottom layer is `MOD`
gates over the inputs.

If a function `F` factors through `t` `MOD` gates with supports `S_1, …, S_t` (each of size `≤ s`) — `F x = H(weightOn S_1 x,
…, weightOn S_t x)` for any top `H` — then `F` has at most `(s+1)^t` distinct cells (`modLayer_cells_le`).  For constant
fan-in `t` and bounded supports `s` this is polynomial, so SAT for such a circuit is a search over `(s+1)^t` weight-cells —
the symmetric structure the polynomial-degree method cannot exploit for prime-power moduli.

## What is proved (clean axioms, no `sorry`)

* **`modLayer_cells_le`** (PROVED) — a function factoring through `t` `MOD` gates (supports `≤ s`) has `≤ (s+1)^t` cells.
* **`modLayer_satisfiable_cells`** (PROVED) — such a (Boolean) circuit's SAT is decided over its `≤ (s+1)^t` cells.

## Honest scope

This is the quasipolynomial cell bound for a real depth-2 `MOD`-layer circuit (top `H` over `MOD` gates), combining the
concrete symmetric leaf with the abstract recursion.  Deeper interleaving and the unconditional `NEXP ⊄ ACC⁰`
(P≠NP-strength) are not done here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModLayerCells

open Finset
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation (weightOn)
open PallLean.Paper93.DeepMath.PathB.ACC0ModGateCells (weightOn_cells_le)
open PallLean.Paper93.DeepMath.PathB.ACC0CellRecursion (cells_factor)

variable {n : ℕ}

/-- **A function over a `MOD`-gate layer has `≤ (s+1)^t` cells (PROVED).**  If `F x = H(weightOn S_1 x, …, weightOn S_t x)`
with each `|S_i| ≤ s`, then `F` has at most `(s+1)^t` distinct cells. -/
theorem modLayer_cells_le {t s : ℕ} {β : Type*} [DecidableEq β]
    (S : Fin t → Finset (Fin n)) (hs : ∀ i, (S i).card ≤ s)
    (H : (Fin t → ℕ) → β) (F : (Fin n → Bool) → β)
    (hF : ∀ x, F x = H (fun i => weightOn (S i) x)) :
    (Finset.univ.image F).card ≤ (s + 1) ^ t :=
  cells_factor (s + 1) (fun i => weightOn (S i)) H F hF
    (fun i => le_trans (weightOn_cells_le (S i)) (by have := hs i; omega))

/-- **A `MOD`-layer circuit's SAT is decided over its `≤ (s+1)^t` cells (PROVED).** -/
theorem modLayer_satisfiable_cells {t s : ℕ}
    (S : Fin t → Finset (Fin n)) (hs : ∀ i, (S i).card ≤ s)
    (H : (Fin t → ℕ) → Bool) (F : (Fin n → Bool) → Bool)
    (hF : ∀ x, F x = H (fun i => weightOn (S i) x)) :
    (Finset.univ.image F).card ≤ (s + 1) ^ t
      ∧ ((∃ x, F x = true) ↔ ∃ x, H (fun i => weightOn (S i) x) = true) := by
  refine ⟨modLayer_cells_le S hs H F hF, ?_⟩
  constructor
  · rintro ⟨x, hx⟩; exact ⟨x, by rw [← hF]; exact hx⟩
  · rintro ⟨x, hx⟩; exact ⟨x, by rw [hF]; exact hx⟩

/-!
**Real `MOD`-layer circuit, quasipolynomial cells, proved.**  A circuit `H` over `t` `MOD` gates (supports `≤ s`) has
`≤ (s+1)^t` cells — polynomial for constant fan-in and bounded supports — so its SAT is a search over the weight-cells,
combining the concrete symmetric leaf (`weightOn_cells_le`) with the abstract recursion (`cells_factor`).  Remaining (open, not
faked): deeper interleaving and the unconditional `NEXP ⊄ ACC⁰`.  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ModLayerCells

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModLayerCells.modLayer_cells_le
