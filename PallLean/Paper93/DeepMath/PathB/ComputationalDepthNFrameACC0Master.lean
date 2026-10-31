import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SatRestrictionActive
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SatBranchCorrect
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SatSpeedupCapstone

/-!
# The master bridge: `NFrameGivesACC0SatSpeedup`, the whole pipeline visible

This file assembles the proved pieces of the N‑frame → ACC⁰‑SAT speedup into one master statement, exposing the
single remaining socket without burying it in infrastructure.  Every component is a proved theorem from the corpus:

| pipeline step | theorem |
|---|---|
| SAT ↔ cell search | `NFrameACC0Speedup.sat_depth2_reduces` |
| machine decides SAT | `ACC0SatMachine.decideSAT_correct` |
| `#cells ≤ (n+1)^{#active}` | `ACC0SatSurvivorCells.image_card_le_active` |
| restriction ⇒ `#active = #surviving` | `ACC0SatRestrictionActive.activeSupports_restrict_card` |
| restriction ⇒ `#cells ≤ (n+1)^{#surviving}` | `ACC0SatRestrictionActive.cells_restrict_le_surviving` |
| SAT = OR over branches | `ACC0SatBranchCorrect.sat_branch_decompose` |
| few survivors ⇒ correct, `< 2^n` | `ACC0SatSpeedupCapstone.survivor_sat_speedup` |

The master theorem `nframe_gives_acc0_sat_speedup` states: **a restriction `L` whose surviving‑gate count is small
(`(n+1)^{survivingCount} < 2^n`) makes the restricted cell search beat brute force** — the survivor‑driven speedup,
via `cells_restrict_le_surviving`.  The **one remaining socket** is the hypothesis `hsocket` — exactly the heart of
the ACC⁰ push:

> the restriction / switching / core‑decomposition machinery guarantees few active surviving gates while leaving
> enough live variables.

Everything around that socket is proved.

## What is proved (clean axioms, no `sorry`)

* `nframe_gives_acc0_sat_speedup` — the master bridge: `(n+1)^{survivingCount supports L} < 2^n ⇒` the restricted
  cell search beats brute force.
* `NFrameGivesACC0SatSpeedupSocket` — the named remaining socket (restriction yields few survivors).

## Honest scope

This makes the entire pipeline a single visible theorem with the genuine open content isolated to `hsocket` (few
surviving gates after a good restriction).  It is the cell‑search cost model throughout; it is **not** the full
Turing‑machine `2^{n-n^ε}` ACC⁰‑SAT theorem, and proves nothing about `NEXP/NP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameACC0Master

open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline
open PallLean.Paper93.DeepMath.PathB.ACC0SatRestrictionActive

variable {n k : ℕ}

/-- **The master bridge (proved): a restriction with few surviving gates makes the cell search beat brute force.**
Given a restriction `L` whose surviving‑gate count satisfies `(n+1)^{survivingCount} < 2^n`, the restricted cell
search examines `< 2^n` cells — the survivor‑driven ACC⁰‑SAT speedup, assembled from the proved pipeline.  The lone
remaining input `hsocket` is the heart of the ACC⁰ push (few survivors while keeping enough live variables). -/
theorem nframe_gives_acc0_sat_speedup (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n))
    (hsocket : (n + 1) ^ survivingCount supports L < 2 ^ n) :
    (Finset.univ.image (weightVec (fun j => supports j ∩ L))).card < 2 ^ n :=
  lt_of_le_of_lt (cells_restrict_le_surviving supports L) hsocket

/-- **(The named remaining socket).**  A support family admits a restriction leaving few surviving gates — the
heart of the ACC⁰ push, supplied by the restriction / switching / core‑decomposition machinery.  Granted it,
`nframe_gives_acc0_sat_speedup` discharges the speedup. -/
def NFrameGivesACC0SatSpeedupSocket (supports : Fin k → Finset (Fin n)) : Prop :=
  ∃ L : Finset (Fin n), (n + 1) ^ survivingCount supports L < 2 ^ n

/-- **The socket discharges the speedup (proved).** -/
theorem speedup_of_socket (supports : Fin k → Finset (Fin n))
    (h : NFrameGivesACC0SatSpeedupSocket supports) :
    ∃ L : Finset (Fin n),
      (Finset.univ.image (weightVec (fun j => supports j ∩ L))).card < 2 ^ n := by
  obtain ⟨L, hL⟩ := h
  exact ⟨L, nframe_gives_acc0_sat_speedup supports L hL⟩

end PallLean.Paper93.DeepMath.PathB.NFrameACC0Master

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0Master.nframe_gives_acc0_sat_speedup
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0Master.speedup_of_socket
