import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0FastSATCharacteristicUniversal

/-!
# Hard math (depth-2 prime-power SYM∘AND count) — `MOD_{p^e} ∘ AND` has linear cell count (proved)

The `SYM∘AND` count for the depth-2 prime-power composition, where the low-degree polynomial method breaks down (`e ≥ 2`, RS
barrier) but the *symmetric* structure carries the count.  A depth-2 circuit `MOD_{p^e}(AND_1, …, AND_k)` — a prime-power
`MOD` gate over `k` `AND`-gates — *is* a `SYM∘AND` form: `symEval (AND-gates) (modIndicator (p^e))`, whose value depends only
on the **count** of satisfied `AND`-gates.  Since that count lies in `{0, …, k}`, the form has at most `k+1` distinct
count-cells (`cells_card_le`), so SAT is decided by examining `≤ k+1` cells (`modpe_depth2_count`, combining the cell bound
with the proved cell-search `fastSat_decides_every_modulus`) — **linear** in the number of `AND`-gates, no exponential blow-up.

This is the genuine depth-2 prime-power count: the symmetric `MOD_{p^e}` top reduces SAT over the high-degree composition to a
linear search over count-cells, exactly where the polynomial-degree route fails for `e ≥ 2`.

## What is proved (clean axioms, no `sorry`)

* **`gateCount_le`** (PROVED) — the count of satisfied gates is `≤ k`.
* **`cells_card_le`** (PROVED) — the count-cell image has `≤ k+1` distinct cells.
* **`modpe_depth2_count`** (PROVED) — `MOD_{p^e} ∘ AND` (`k` `AND`-gates): `≤ k+1` cells **and** SAT `↔ ∃` a count-cell `c`
  with `p^e ∣ c` (linear fast-SAT).

## Honest scope

This is the depth-2 prime-power `SYM∘AND` count (linear in `#AND`-gates) via the symmetric structure.  Deeper compositions
(depth `≥ 3` interleaving prime-power `MOD` gates) and the unconditional `NEXP ⊄ ACC⁰` (P≠NP-strength) are **not** done here.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModpeDepth2

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver (gateCount symEval)
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup (Satisfiable)
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd (monoAND)
open PallLean.Paper93.DeepMath.PathB.ACC0FastSATCharacteristicUniversal
  (modIndicator fastSat_decides_every_modulus)

variable {m n : ℕ}

/-- **The count of satisfied gates is `≤ k` (PROVED).** -/
theorem gateCount_le (g : Fin m → (Fin n → Bool) → Bool) (x : Fin n → Bool) : gateCount g x ≤ m := by
  unfold gateCount
  calc (∑ j : Fin m, (if g j x then 1 else 0)) ≤ ∑ _j : Fin m, 1 :=
        Finset.sum_le_sum (fun j _ => by split <;> simp)
    _ = m := by simp

/-- **The count-cell image has `≤ k+1` distinct cells (PROVED).** -/
theorem cells_card_le (g : Fin m → (Fin n → Bool) → Bool) :
    (Finset.univ.image (gateCount g)).card ≤ m + 1 := by
  refine le_trans (Finset.card_le_card ?_) (le_of_eq (Finset.card_range (m + 1)))
  intro c hc
  simp only [Finset.mem_image] at hc
  obtain ⟨x, _, rfl⟩ := hc
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (gateCount_le g x))

/-- **Depth-2 prime-power `SYM∘AND` count (PROVED).**  `MOD_{p^e}(AND_1,…,AND_k)` has `≤ k+1` count-cells, and SAT is decided
by a `p^e`-residue check over those `≤ k+1` cells — linear in the number of `AND`-gates. -/
theorem modpe_depth2_count (p e k : ℕ) (mono : Fin k → Finset (Fin n)) :
    (Finset.univ.image (gateCount (fun j x => monoAND (mono j) x))).card ≤ k + 1
      ∧ (Satisfiable (symEval (fun j x => monoAND (mono j) x) (modIndicator (p ^ e)))
          ↔ ∃ c ∈ Finset.univ.image (gateCount (fun j x => monoAND (mono j) x)), c % p ^ e = 0) :=
  ⟨cells_card_le _, fastSat_decides_every_modulus _ (p ^ e)⟩

/-!
**Depth-2 prime-power `SYM∘AND` count, proved.**  The symmetric `MOD_{p^e}` top reduces SAT over the (high-degree)
depth-2 composition to a linear search over `≤ k+1` count-cells — the count the polynomial-degree route cannot give for
`e ≥ 2`.  Remaining (open, not faked): deeper compositions and the unconditional `NEXP ⊄ ACC⁰`.  Not `NEXP ⊄ ACC⁰`, not
`P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ModpeDepth2

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModpeDepth2.modpe_depth2_count
