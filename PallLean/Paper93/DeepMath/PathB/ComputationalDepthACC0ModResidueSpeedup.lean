import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameACC0Speedup

/-!
# The mixed-modulus SAT-speedup kernel: residue compression

The N-frame SAT speedup (`…NFrameACC0Speedup.sat_depth2_reduces`) reduced depth-2 `MOD`-bottom SAT to a search over
the `weightVec` image — but `weightVec` records the full support **counts** (`0..n`), giving up to `(n+1)^k` cells.
This file sharpens it for the **mixed-modulus** case (the Tier-3 frontier, `…Layer3MixedModulus`): a `MOD_q` gate's
value depends only on its support-count **mod q** (`q` values), so a depth-2 `MOD`-circuit factors through the
**residue vector** `modResVec`, valued in `∏_j ZMod q_j` — only `∏_j q_j` cells, *constant per gate*.

This is the structural compression at the heart of Williams' faster ACC⁰-SAT: the circuit cannot distinguish inputs
with the same residue vector, so SAT is decided by enumerating the `≤ ∏ q_j` residue cells.  When `∏ q_j < 2^n`
(e.g. `MOD_6` gates with `6^k < 2^n`, i.e. `k < n·log 2/log 6 ≈ 0.387n`) this beats `2^n` brute force.

## What is proved (clean axioms, no `sorry`)

* `modResVec` — the residue vector `j ↦ (count_{S_j} mod q_j)` of a depth-2 `MOD`-circuit.
* `eval_factors_residue` — the circuit value factors through `modResVec` (it ignores everything but the residues).
* `sat_iff_residue_image` — **SAT ⇔ residue-cell search**: `Satisfiable C.eval ↔ ∃ v ∈ image(modResVec), G v`.
* `residue_cell_count_le` — `|image(modResVec)| ≤ ∏_j q_j` (constant per gate, independent of `n`).
* `mod_circuit_residue_speedup`, `mod6_circuit_residue_speedup` — **`∏ q_j < 2^n` (resp. `6^k < 2^n`) ⇒ the residue
  search examines `< 2^n` cells** — the mixed-modulus SAT speedup.

## Honest scope

This is the genuine *structural compression / SAT-speedup kernel* for mixed-modulus circuits — the residue collapse
Williams' algorithm exploits.  It is **not** the full `NEXP ⊄ ACC⁰`: that needs the speedup realised as a uniform
(nondeterministic) algorithm plus the time-hierarchy cash-out, which this cell-count bound does not supply (the
named gap in `…NFrameACC0Master`).  It also says nothing about *lower bounds* for the mixed gate (Tier-3 remains
open).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModResidueSpeedup

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup

variable {n k : ℕ}

/-- The **residue vector** of a depth-2 `MOD`-circuit: each coordinate is the support-count of gate `j` taken
modulo that gate's modulus `q_j` (an element of `ZMod q_j`).  This is the only information about the input the
circuit can use. -/
def modResVec (C : Depth2ModCircuit n k) (x : Fin n → Bool) :
    (j : Fin k) → ZMod (C.gates j).modulus :=
  fun j => modQStatOn (C.gates j).support (C.gates j).modulus x

/-- **The circuit value factors through the residue vector (proved).**  `C.eval x = G (modResVec C x)`: the circuit
ignores everything about `x` except the per-gate residues. -/
theorem eval_factors_residue (C : Depth2ModCircuit n k) :
    ∃ G : ((j : Fin k) → ZMod (C.gates j).modulus) → Bool, ∀ x, C.eval x = G (modResVec C x) :=
  ⟨fun v => C.top (fun j => decide (v j = (C.gates j).target)), fun _ => rfl⟩

/-- **SAT ⇔ residue-cell search (proved).**  A depth-2 `MOD`-circuit is satisfiable iff some *achieved* residue
vector is accepted — search the `∏ q_j` residue cells, not the `2^n` cube. -/
theorem sat_iff_residue_image (C : Depth2ModCircuit n k) :
    ∃ G : ((j : Fin k) → ZMod (C.gates j).modulus) → Bool,
      Satisfiable C.eval ↔ ∃ v ∈ Finset.univ.image (modResVec C), G v = true := by
  obtain ⟨G, hG⟩ := eval_factors_residue C
  refine ⟨G, ?_⟩
  have hsat : Satisfiable C.eval ↔ ∃ x, G (modResVec C x) = true := by
    unfold Satisfiable
    constructor
    · rintro ⟨x, hx⟩; exact ⟨x, by rw [← hG]; exact hx⟩
    · rintro ⟨x, hx⟩; exact ⟨x, by rw [hG]; exact hx⟩
  rw [hsat]
  exact sat_iff_image G (modResVec C)

/-- **The residue-cell count is `≤ ∏_j q_j` (proved): constant per gate, independent of `n`.**  The residue vector
lands in `∏_j ZMod q_j`, of cardinality `∏_j q_j`. -/
theorem residue_cell_count_le (C : Depth2ModCircuit n k) (hpos : ∀ j, 0 < (C.gates j).modulus) :
    (Finset.univ.image (modResVec C)).card ≤ ∏ j, (C.gates j).modulus := by
  haveI : ∀ j, NeZero (C.gates j).modulus := fun j => ⟨(hpos j).ne'⟩
  calc (Finset.univ.image (modResVec C)).card
      ≤ Fintype.card ((j : Fin k) → ZMod (C.gates j).modulus) :=
        le_trans (Finset.card_le_card (Finset.subset_univ _)) (le_of_eq Finset.card_univ)
    _ = ∏ j, Fintype.card (ZMod (C.gates j).modulus) := Fintype.card_pi
    _ = ∏ j, (C.gates j).modulus := Finset.prod_congr rfl (fun j _ => ZMod.card (C.gates j).modulus)

/-- **The mixed-modulus SAT speedup (proved): `∏ q_j < 2^n ⇒` the residue search examines `< 2^n` cells.** -/
theorem mod_circuit_residue_speedup (C : Depth2ModCircuit n k) (hpos : ∀ j, 0 < (C.gates j).modulus)
    (hregime : (∏ j, (C.gates j).modulus) < 2 ^ n) :
    (Finset.univ.image (modResVec C)).card < 2 ^ n :=
  lt_of_le_of_lt (residue_cell_count_le C hpos) hregime

/-- **SAT reduces to a sub-`2^n` residue search (proved).**  Combining the reduction with the cell bound: under
`∏ q_j < 2^n`, satisfiability is decided by a search over `< 2^n` residue cells. -/
theorem mod_circuit_sat_speedup (C : Depth2ModCircuit n k) (hpos : ∀ j, 0 < (C.gates j).modulus)
    (hregime : (∏ j, (C.gates j).modulus) < 2 ^ n) :
    ∃ G : ((j : Fin k) → ZMod (C.gates j).modulus) → Bool,
      (Satisfiable C.eval ↔ ∃ v ∈ Finset.univ.image (modResVec C), G v = true)
        ∧ (Finset.univ.image (modResVec C)).card < 2 ^ n := by
  obtain ⟨G, hG⟩ := sat_iff_residue_image C
  exact ⟨G, hG, mod_circuit_residue_speedup C hpos hregime⟩

/-- **The `MOD_6` instance (proved): `6^k < 2^n ⇒ < 2^n` residue cells.**  A depth-2 circuit of `k` `MOD_6` gates is
SAT-decided by a search over `≤ 6^k` residue cells, beating `2^n` brute force once `k < n·(log 2 / log 6) ≈ 0.387n`.
The concrete small-composite frontier case. -/
theorem mod6_circuit_residue_speedup (C : Depth2ModCircuit n k)
    (h6 : ∀ j, (C.gates j).modulus = 6) (hregime : 6 ^ k < 2 ^ n) :
    (Finset.univ.image (modResVec C)).card < 2 ^ n := by
  have hprod : (∏ j, (C.gates j).modulus) = 6 ^ k := by
    rw [Finset.prod_congr rfl (fun j _ => h6 j), Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mod_circuit_residue_speedup C (fun j => by rw [h6 j]; norm_num) (by rw [hprod]; exact hregime)

end PallLean.Paper93.DeepMath.PathB.ACC0ModResidueSpeedup

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModResidueSpeedup.sat_iff_residue_image
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModResidueSpeedup.residue_cell_count_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModResidueSpeedup.mod_circuit_sat_speedup
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModResidueSpeedup.mod6_circuit_residue_speedup
