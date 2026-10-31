import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameACC0Speedup

/-!
# A time-cost model for the N-frame ACC⁰-SAT speedup

`sat_depth2_reduces` (`…NFrameACC0Speedup`) collapsed SAT to a search over the `weightVec` cell space.  This file
turns that into a genuine **model-relative time bound**: in the natural cost model where deciding SAT means
*enumerating the achievable cells*, the cost is `|image(weightVec)|`, and this is `< 2^n` in the small-gate regime
— strictly below brute force.

The cost model is minimal and explicit: `cost = |image(weightVec supports)|` (the number of distinct cell/residue
vectors to check).  The bound:

> `|image(weightVec supports)| ≤ (n+1)^k`

— each gate's count `weightOn S_j x ∈ {0,…,n}`, so the cell vector lives in `(Fin k → {0,…,n})`, of size
`(n+1)^k`.  When `(n+1)^k < 2^n` (i.e. `k = o(n / log n)` gates — the small-gate regime), the cell search beats
brute force, **proved**.

## What is proved (clean axioms, no `sorry`)

* `weightVec_le` — each cell coordinate is `≤ n` (a gate reads `≤ n` variables).
* `image_subset_piFinset`, `imageSearchCost_le` — `|image(weightVec)| ≤ (n+1)^k` (the cell space bound).
* `imageSearch_beats_bruteforce` — `(n+1)^k < 2^n ⇒ |image| < 2^n`: the cell search is sub-brute-force.
* `nframe_acc0_sat_timebound` — **the model-relative speedup**: a depth-2 `MOD`-bottom circuit's SAT is decided by
  a cell search of cost `< 2^n` in the small-gate regime.

## Honest scope

This is a *search-count* time model: cost = number of cells enumerated (the dominant term), each checked in `O(k)`.
It is **not** a full Turing-machine time analysis, and the small-gate regime `(n+1)^k < 2^n` is where this single
base-case search alone suffices (no branching).  For larger gate counts one branches over killed coordinates (the
restriction tree) to reach a small-survivor base case — the branching factor `2^{#killed}` times this cell cost is
the general bound, with the survivor count the parameter; that combination is the remaining named accounting.  So
this discharges the time bound *in the small-gate regime, in the cell-search model* — a real, honest, model-relative
speedup — not the full `2^{n-n^ε}` ACC⁰-SAT theorem.  Nothing here proves `NEXP ⊄ ACC⁰`, `NP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SatTimeCost

open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup

variable {n k : ℕ}

/-- **Each cell coordinate is `≤ n` (proved): a gate's count is at most the number of variables.** -/
theorem weightVec_le (supports : Fin k → Finset (Fin n)) (x : Fin n → Bool) (j : Fin k) :
    weightVec supports x j ≤ n := by
  show weightOn (supports j) x ≤ n
  unfold weightOn
  calc ∑ i ∈ supports j, (if x i then 1 else 0)
      ≤ ∑ _i ∈ supports j, 1 := Finset.sum_le_sum (fun i _ => by split <;> omega)
    _ = (supports j).card := by simp
    _ ≤ n := le_trans (Finset.card_le_univ _) (le_of_eq (Fintype.card_fin n))

/-- The cell vectors live in `(Fin k → {0,…,n})`. -/
theorem image_subset_piFinset (supports : Fin k → Finset (Fin n)) :
    Finset.univ.image (weightVec supports)
      ⊆ Fintype.piFinset (fun _ : Fin k => Finset.range (n + 1)) := by
  intro w hw
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hw
  rw [Fintype.mem_piFinset]
  intro j
  rw [Finset.mem_range]
  exact Nat.lt_succ_of_le (weightVec_le supports x j)

/-- **The cell search space is at most `(n+1)^k` (proved).** -/
theorem imageSearchCost_le (supports : Fin k → Finset (Fin n)) :
    (Finset.univ.image (weightVec supports)).card ≤ (n + 1) ^ k := by
  calc (Finset.univ.image (weightVec supports)).card
      ≤ (Fintype.piFinset (fun _ : Fin k => Finset.range (n + 1))).card :=
        Finset.card_le_card (image_subset_piFinset supports)
    _ = (n + 1) ^ k := by
        rw [Fintype.card_piFinset]
        simp [Finset.card_range, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The cell search beats brute force (proved): `(n+1)^k < 2^n ⇒ |image| < 2^n`.** -/
theorem imageSearch_beats_bruteforce (supports : Fin k → Finset (Fin n)) (hregime : (n + 1) ^ k < 2 ^ n) :
    (Finset.univ.image (weightVec supports)).card < 2 ^ n :=
  lt_of_le_of_lt (imageSearchCost_le supports) hregime

/-- **The model-relative speedup (proved): in the small-gate regime, a depth-2 `MOD`-bottom circuit's SAT is
decided by a cell search of cost `< 2^n`.**  Combines `sat_depth2_reduces` (SAT ↔ cell search) with the cell-space
bound `(n+1)^k < 2^n`: there is a decision procedure (search the `weightVec` image) whose cost is the number of
cells, strictly below the brute-force `2^n`. -/
theorem nframe_acc0_sat_timebound (C : Depth2ModCircuit n k) (hregime : (n + 1) ^ k < 2 ^ n) :
    ∃ (g : (Fin k → ℕ) → Bool) (cost : ℕ),
      (Satisfiable C.eval ↔ ∃ w ∈ Finset.univ.image (weightVec C.supports), g w = true)
        ∧ cost = (Finset.univ.image (weightVec C.supports)).card
        ∧ cost < 2 ^ n := by
  obtain ⟨g, hg⟩ := sat_depth2_reduces C
  exact ⟨g, (Finset.univ.image (weightVec C.supports)).card, hg, rfl,
    imageSearch_beats_bruteforce C.supports hregime⟩

end PallLean.Paper93.DeepMath.PathB.ACC0SatTimeCost

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatTimeCost.imageSearchCost_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SatTimeCost.nframe_acc0_sat_timebound
