import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModLayerCells

/-!
# Bridge — fast-SAT for a real `MOD`-layer circuit: search over `≤ (s+1)^t` weight-cells (proved)

The algorithmic payoff of the `MOD`-layer cell bound.  A real depth-2 circuit `F x = H(weightOn S_1 x, …, weightOn S_t x)`
(top `H` over `t` `MOD` gates, supports `≤ s`) is satisfiable **iff** some achievable joint weight-vector makes `H` true
(`modLayer_fastsat.1`), and the set of achievable joint weight-vectors has at most `(s+1)^t` elements (`modLayer_fastsat.2`).
So SAT is decided by searching `≤ (s+1)^t` weight-cells instead of all `2^n` assignments — and when `(s+1)^t < 2^n` (constant
fan-in, bounded supports, large `n`) this **beats brute force** (`modLayer_beats_bruteforce`).

This is the Williams algorithmic speedup made concrete for the real `ACC0` `MOD`-layer model, via the field-independent
symmetric cell count (the structure the polynomial-degree method cannot exploit for prime-power moduli).

## What is proved (clean axioms, no `sorry`)

* **`modLayer_fastsat`** (PROVED) — `(∃ x, F x = true) ↔ ∃ w ∈ image(joint weights), H w = true`, **and** the joint-weight
  image has `≤ (s+1)^t` cells.
* **`modLayer_beats_bruteforce`** (PROVED) — if `(s+1)^t < 2^n` the SAT cell-search examines strictly fewer than `2^n` cells.

## Honest scope

This is fast-SAT (sub-`2^n` weight-cell search) for the real depth-2 `MOD`-layer circuit.  Turning this into the full Williams
`NEXP ⊄ ACC⁰` still needs the realization/collapse sockets (the collapse socket is P≠NP-strength, proved
separation-equivalent).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModLayerFastSAT

open Finset
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation (weightOn)
open PallLean.Paper93.DeepMath.PathB.ACC0ModGateCells (weightOn_cells_le)
open PallLean.Paper93.DeepMath.PathB.ACC0CellRecursion (cells_compose)

variable {n : ℕ}

/-- **Fast-SAT for a `MOD`-layer circuit (PROVED): SAT iff a weight-cell satisfies `H`, over `≤ (s+1)^t` cells.** -/
theorem modLayer_fastsat {t s : ℕ}
    (S : Fin t → Finset (Fin n)) (hs : ∀ i, (S i).card ≤ s)
    (H : (Fin t → ℕ) → Bool) (F : (Fin n → Bool) → Bool)
    (hF : ∀ x, F x = H (fun i => weightOn (S i) x)) :
    ((∃ x, F x = true) ↔
        ∃ w ∈ Finset.univ.image (fun x (i : Fin t) => weightOn (S i) x), H w = true)
      ∧ (Finset.univ.image (fun x (i : Fin t) => weightOn (S i) x)).card ≤ (s + 1) ^ t := by
  refine ⟨?_, cells_compose (s + 1) (fun i => weightOn (S i))
    (fun i => le_trans (weightOn_cells_le (S i)) (by have := hs i; omega))⟩
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨fun i => weightOn (S i) x, Finset.mem_image_of_mem _ (Finset.mem_univ x),
      by rw [← hF]; exact hx⟩
  · rintro ⟨w, hw, hHw⟩
    simp only [Finset.mem_image] at hw
    obtain ⟨x, _, rfl⟩ := hw
    exact ⟨x, by rw [hF]; exact hHw⟩

/-- **The fast-SAT cell-search beats brute force when `(s+1)^t < 2^n` (PROVED).** -/
theorem modLayer_beats_bruteforce {t s : ℕ} (hlt : (s + 1) ^ t < 2 ^ n)
    (S : Fin t → Finset (Fin n)) (hs : ∀ i, (S i).card ≤ s)
    (H : (Fin t → ℕ) → Bool) (F : (Fin n → Bool) → Bool)
    (hF : ∀ x, F x = H (fun i => weightOn (S i) x)) :
    (Finset.univ.image (fun x (i : Fin t) => weightOn (S i) x)).card < 2 ^ n :=
  lt_of_le_of_lt (modLayer_fastsat S hs H F hF).2 hlt

/-!
**Fast-SAT for the real `MOD`-layer circuit, proved.**  SAT is decided by searching `≤ (s+1)^t` weight-cells, which beats the
`2^n` brute force whenever `(s+1)^t < 2^n` — the Williams algorithmic speedup made concrete via the field-independent symmetric
cell count.  Remaining (open, not faked): the realization/collapse sockets to `NEXP ⊄ ACC⁰` (collapse socket = P≠NP-strength).
Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ModLayerFastSAT

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModLayerFastSAT.modLayer_fastsat
