import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BeigelTaruiToy

/-!
# Depth-3 mixed fragment: arbitrary top over a MIXED `MOD`/bounded bottom is searchable

Combining the residue observer (`MOD` gates, `…ACC0ResidueObserver`) and the projection observer (bounded-fan-in
gates, `…ACC0BeigelTaruiToy`), this file proves the next rung: an **arbitrary** top gate over a bottom layer that
*mixes* `MOD_q` gates and bounded-fan-in `AND_w`/`OR_w` gates — each over input literals — is observer-searchable,
with state count `≤ ∏_i (per-gate states)`.

The key is that the observer composition law `observed_top_pi` allows the bottom gates to use **different observer
types** (`ZMod q_i` for a `MOD` gate, `↥T_i → Bool` for a bounded gate) — so a mixed bottom is handled uniformly:
each gate's observer has small state count (`q_i` resp. `2^{|T_i|}`), and the product stays sub-`2^n` when the
total is small.

## What is proved (clean axioms, no `sorry`)

* `depth_mixed_searchable` — **the generic depth-`d` fragment**: if every bottom gate `f i` is observed by *some*
  statistic of state count `≤ b_i`, then the (arbitrary) top is SAT-searchable in `< 2^n` cells when `∏ b_i < 2^n`.
  The observer types may vary per gate — this is what makes the bottom *mixed*.
* `modGate_card_le` — a `MOD_q` gate qualifies with `b = q` (`card (ZMod q) = q`).
* `boundedGate_card_le` — a bounded-fan-in gate qualifies with `b = 2^{|T|}`.

## Honest scope

A genuine fragment of the depth-reduction socket: *any* circuit whose bottom layer (reading literals) consists of
`MOD` and bounded-fan-in gates is residue/projection-searchable below brute force when the per-gate state product is
`< 2^n` — with arbitrary AC⁰/`MOD` structure above (folded into the `top`).  It does **not** prove the full
Yao–Beigel–Tarui reduction of an *arbitrary* `ACC⁰` circuit to this fragment (the deep structural step, still open).
Still the cell-count model; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0Depth3Mixed

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver
open PallLean.Paper93.DeepMath.PathB.ACC0BeigelTaruiToy

variable {n : ℕ}

/-- **The generic depth-`d` mixed-bottom searchability (proved).**  If every bottom gate `f i` is observed by some
statistic `stat i` of state count `≤ b i` (the observer *types* may differ per gate — `ZMod q` for `MOD`, a
projection for bounded fan-in), then the arbitrary top `top (f 1, …, f k)` is SAT-decided by an observer search over
`< 2^n` cells whenever `∏ b i < 2^n`.  This is the mixed-bottom fragment of the depth-reduction socket. -/
theorem depth_mixed_searchable {ι : Type*} [Fintype ι] {S : ι → Type*} [∀ i, Fintype (S i)]
    (f : ι → (Fin n → Bool) → Bool) (stat : ∀ i, (Fin n → Bool) → S i)
    (hf : ∀ i, ObservedBy (f i) (stat i)) (top : (ι → Bool) → Bool)
    (b : ι → ℕ) (hb : ∀ i, Fintype.card (S i) ≤ b i) (hregime : (∏ i, b i) < 2 ^ n) :
    ∃ g : (∀ i, S i) → Bool,
      (Satisfiable (fun x => top (fun i => f i x))
        ↔ ∃ s ∈ Finset.univ.image (fun x => fun i => stat i x), g s = true)
      ∧ (Finset.univ.image (fun x => fun i => stat i x)).card < 2 ^ n := by
  obtain ⟨g, hg⟩ := observed_top_pi f stat hf top
  refine ⟨g, observed_sat_iff g hg, ?_⟩
  calc (Finset.univ.image (fun x => fun i => stat i x)).card
      ≤ ∏ i, Fintype.card (S i) := by
        rw [← Fintype.card_pi]; exact observed_cellCount_le _
    _ ≤ ∏ i, b i := Finset.prod_le_prod' (fun i _ => hb i)
    _ < 2 ^ n := hregime

/-- **A `MOD_q` gate qualifies for the mixed fragment with `b = q` (proved).**  Its residue observer has state count
`card (ZMod q) = q`. -/
theorem modGate_card_le (G : ModGate n) [NeZero G.modulus] :
    Fintype.card (ZMod G.modulus) ≤ G.modulus :=
  le_of_eq (ZMod.card G.modulus)

/-- **A bounded-fan-in gate qualifies for the mixed fragment with `b = 2^{|T|}` (proved).**  Its projection observer
has state count `card (↥T → Bool) = 2^{|T|}`. -/
theorem boundedGate_card_le (T : Finset (Fin n)) :
    Fintype.card (↥T → Bool) ≤ 2 ^ T.card :=
  le_of_eq (proj_card T)

end PallLean.Paper93.DeepMath.PathB.ACC0Depth3Mixed

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Depth3Mixed.depth_mixed_searchable
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Depth3Mixed.modGate_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Depth3Mixed.boundedGate_card_le
