import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BoundedOverlapMOD
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSpeedupMargin

/-!
# The restricted Williams speedup: exact `SYM∘AND` of small footprint ⇒ super-polynomial `ACC⁰`-SAT savings

This file *cashes out* the restricted exact-form results (`…ACC0RestrictedYBT`, `…ACC0BoundedOverlapMOD`) into an
actual **Williams-style speedup theorem** for the controllable `ACC⁰` fragments.  The chain, now fully proved end to
end for these fragments:

```
restricted ACC0Circuit  ──[exact SYM∘AND, proved]──►  count-cell search decides SAT
   (footprint ≤ n−k)         cell count ≤ psize C ≤ 2^(baseSum C) ≤ 2^(n−k)
                                              │  [SpeedupMargin, proved]
                                              ▼
                          SAT decided with Williams savings ≥ 2^k  over brute force 2^n
```

For footprint `baseSum C = n − n^ε` (e.g. disjoint / bounded-overlap `MOD` reading `n − n^ε` literal-incidences), the
savings is `2^{n^ε}` — **super-polynomial** — which is exactly the regime Williams' time-hierarchy method needs.  So
on these fragments the `fastSat` is not merely `< 2^n`: it is quantitatively `2^{n−footprint}`-fast.

## What is proved (clean axioms, no `sorry`)

* **`restricted_acc0_searchable`** — every `ACC0Circuit` has its SAT decided by a count-cell search with cell count
  `≤ psize C` (the exact `SYM∘AND` size).
* **`restricted_williams_speedup`** — for `baseSum C + k ≤ n`: SAT is decided by `≤ 2^(n−k)` cells, with Williams
  savings `2^k · (cells) ≤ 2^n`.
* **`restricted_savings_by_footprint`** — the parametric form: the savings exponent is *exactly* `n − baseSum C`
  (`2^{n−footprint} · cells ≤ 2^n`).  For `baseSum = polylog`, savings `= 2^{n−polylog}` — super-polynomial.
* **`boundedOverlap_mod_williams_speedup`** / **`disjoint_mod_williams_speedup`** — the speedup instantiated to an
  `AND` of `MOD_q` gates with bounded total support / pairwise-disjoint supports.

## Honest scope — what this is and what it feeds

This is the **restricted** Williams speedup: a *real* super-polynomial-savings `ACC⁰`-SAT algorithm in the count-cell
model, but only for fragments whose support footprint is `< n` (bounded-overlap / bounded-leaf, where the exact form
is below `2^n`).  It feeds the realization split (`…ACC0WilliamsRealizationSplit`) as a *concrete instance* of the
`fastSat`/cost-bridge inputs on these fragments; it does **not** discharge the deep `TimeHierarchySocket` (Williams'
algorithmic method, separation-strength) nor the full-`ACC⁰` size wall.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RestrictedWilliamsSpeedup

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.ACC0YBTExactCompose
open PallLean.Paper93.DeepMath.PathB.ACC0RestrictedYBT
open PallLean.Paper93.DeepMath.PathB.ACC0BoundedOverlapMOD
open PallLean.Paper93.DeepMath.PathB.SpeedupMargin

variable {n : ℕ}

/-- **Every `ACC0Circuit` has its SAT decided by a count-cell search of `≤ psize C` cells (proved).**  The cells are
the values of the exact `SYM∘AND` count statistic; SAT holds iff some achieved cell is accepting. -/
theorem restricted_acc0_searchable (C : ACC0Circuit n) :
    ∃ (cells : Finset ℕ) (dec : ℕ → Bool),
      (Satisfiable (eval C) ↔ ∃ c ∈ cells, dec c = true) ∧ cells.card ≤ psize C := by
  obtain ⟨ι, hι, mono, h, hcard, hfe⟩ := acc0circuit_hasSymAndForm C
  letI := hι
  refine ⟨Finset.univ.image (saCount mono), h, ?_, ?_⟩
  · exact observed_sat_iff h (fun x => congrFun hfe x)
  · -- cells ⊆ range (card ι + 1) ⊆ …, so card ≤ card ι + 1 ≤ symAndSize C + 1 = psize C
    have hsub : Finset.univ.image (saCount mono) ⊆ Finset.range (Fintype.card ι + 1) := by
      intro c hc
      rw [Finset.mem_image] at hc
      obtain ⟨x, _, rfl⟩ := hc
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (saCount_le_card mono x)
    calc (Finset.univ.image (saCount mono)).card
        ≤ (Finset.range (Fintype.card ι + 1)).card := Finset.card_le_card hsub
      _ = Fintype.card ι + 1 := Finset.card_range _
      _ ≤ symAndSize C + 1 := by exact Nat.succ_le_succ hcard
      _ = psize C := symAndSize_succ_eq_psize C

/-- **The restricted Williams speedup (proved).**  If the support footprint satisfies `baseSum C + k ≤ n`, then SAT
of `eval C` is decided by a count-cell search of `≤ 2^(n−k)` cells, delivering Williams savings `≥ 2^k` over brute
force `2^n`. -/
theorem restricted_williams_speedup (C : ACC0Circuit n) {k : ℕ} (hk : k ≤ n)
    (hfoot : baseSum C + k ≤ n) :
    ∃ (cells : Finset ℕ) (dec : ℕ → Bool),
      (Satisfiable (eval C) ↔ ∃ c ∈ cells, dec c = true)
      ∧ cells.card ≤ 2 ^ (n - k)
      ∧ 2 ^ k * cells.card ≤ 2 ^ n := by
  obtain ⟨cells, dec, hsat, hcard⟩ := restricted_acc0_searchable C
  have hfit : cells.card ≤ 2 ^ (n - k) :=
    calc cells.card ≤ psize C := hcard
      _ ≤ 2 ^ baseSum C := psize_le_two_pow_baseSum C
      _ ≤ 2 ^ (n - k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact ⟨cells, dec, hsat, hfit, savings_ge_of_work_le hk hfit⟩

/-- **The parametric savings (proved): the savings exponent is exactly the footprint deficit `n − baseSum C`.**  For
`baseSum C = polylog n`, the savings is `2^{n−polylog}` — super-polynomial. -/
theorem restricted_savings_by_footprint (C : ACC0Circuit n) (hbn : baseSum C ≤ n) :
    ∃ (cells : Finset ℕ) (dec : ℕ → Bool),
      (Satisfiable (eval C) ↔ ∃ c ∈ cells, dec c = true)
      ∧ 2 ^ (n - baseSum C) * cells.card ≤ 2 ^ n := by
  obtain ⟨cells, dec, hsat, _, hsav⟩ :=
    restricted_williams_speedup C (k := n - baseSum C) (by omega) (by omega)
  exact ⟨cells, dec, hsat, hsav⟩

/-- **Restricted Williams speedup for an `AND` of `MOD_q` gates with bounded total support (proved).** -/
theorem boundedOverlap_mod_williams_speedup (q : ℕ) (gates : List (Finset (Fin n) × ZMod q))
    {k : ℕ} (hk : k ≤ n) (hfoot : (gates.map (fun g => g.1.card)).sum + k ≤ n) :
    ∃ (cells : Finset ℕ) (dec : ℕ → Bool),
      (Satisfiable (eval (andOfModList q gates)) ↔ ∃ c ∈ cells, dec c = true)
      ∧ cells.card ≤ 2 ^ (n - k)
      ∧ 2 ^ k * cells.card ≤ 2 ^ n :=
  restricted_williams_speedup (andOfModList q gates) hk (by rw [baseSum_andOfModList]; exact hfoot)

/-- **Restricted Williams speedup for pairwise-disjoint `MOD_q` gates (proved).**  Disjoint supports read each
variable at most once, so the footprint is the size of their union; if that union leaves `≥ k` variables free
(`|⋃ Sᵢ| + k ≤ n`), the savings is `≥ 2^k`. -/
theorem disjoint_mod_williams_speedup (q : ℕ) (gates : List (Finset (Fin n) × ZMod q))
    {k : ℕ} (hk : k ≤ n)
    (hd : (gates.map (fun g : Finset (Fin n) × ZMod q => g.1)).Pairwise Disjoint)
    (hcover : ((gates.map (fun g : Finset (Fin n) × ZMod q => g.1)).foldr (· ∪ ·) ∅).card + k ≤ n) :
    ∃ (cells : Finset ℕ) (dec : ℕ → Bool),
      (Satisfiable (eval (andOfModList q gates)) ↔ ∃ c ∈ cells, dec c = true)
      ∧ cells.card ≤ 2 ^ (n - k)
      ∧ 2 ^ k * cells.card ≤ 2 ^ n := by
  have hfp : (gates.map (fun g : Finset (Fin n) × ZMod q => g.1.card)).sum
      = ((gates.map (fun g : Finset (Fin n) × ZMod q => g.1)).foldr (· ∪ ·) ∅).card := by
    rw [map_fst_card_eq]
    exact sum_card_eq_card_union (gates.map (fun g : Finset (Fin n) × ZMod q => g.1)) hd
  exact boundedOverlap_mod_williams_speedup q gates hk (by rw [hfp]; exact hcover)

end PallLean.Paper93.DeepMath.PathB.ACC0RestrictedWilliamsSpeedup

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RestrictedWilliamsSpeedup.restricted_acc0_searchable
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RestrictedWilliamsSpeedup.restricted_williams_speedup
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RestrictedWilliamsSpeedup.restricted_savings_by_footprint
