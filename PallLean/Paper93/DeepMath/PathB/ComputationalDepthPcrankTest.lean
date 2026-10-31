import PallLean.Paper93.DeepMath.PathB.ComputationalDepthProjectedContextualRank

/-!
# Testing the existing `pcrank` on `∏Xᵢ` vs `MOD_q`: it makes BOTH low (proved)

Using the repo's existing projected/contextual rank (`ProjectedContextualRank.pcrank ≤ crank`, the number of distinct
rows of a Boolean communication matrix `M : A → B → Bool`) rather than inventing a new invariant.  Expressed across a
2-party cut (`a` = first half, `b` = second half of the inputs):

  `crank_and_le_two` — `∏Xᵢ = AND` has `crank ≤ 2`: `AND(a)∧AND(b)` has only two distinct rows
        (`fun b ↦ AND b` when `AND a`, else all-`false`).  **The sanity check `pcrank_fullProd_low` PASSES**
        (`pcrank ≤ crank ≤ 2`).
  `crank_modq_le` — `MOD_q` has `crank ≤ q`: `[∑a+∑b ≡ 0 mod q]` depends on `a` only through `∑a mod q`, so it has at
        most `q` distinct rows.  **The high-side goal `pcrank_modq_high` FAILS: `MOD_q` is *also* low** (`crank ≤ q`).

## Verdict on this candidate

`pcrank` (contextual/communication rank) makes **both** `∏Xᵢ` and `MOD_q` low — it does **not** separate them, failing
the sanity check *oppositely* to raw `spdpRank` (which made both high).  The reason: `MOD_q` (like `AND`, parity, any
symmetric-of-sum function) *factors across a 2-party cut*, so it is easy for communication even though it is hard for
`AC⁰` circuits.  Communication/contextual rank on a fixed cut is the wrong object; the repo's genuine `pcrank`
separation uses a *computation-trace* matrix and a specific NP-hard family whose A3-survival (a `proj` injective on the
hard rows yet collapsing every poly-time computation) is exactly `P ≠ NP`-strength / barriered
(`…ProjectedContextualRank`, `…SPDPFeatureProjection` docstrings).  So per the staged plan, the candidate is rejected
at step 3 (`pcrank_modq_high` is false), and the real invariant is not this fixed-cut communication rank.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PcrankTest

open PallLean.Paper93.DeepMath.PathB.RankContextualWidth
open Finset

variable {n : ℕ}

variable {n : ℕ}
def andAll (x : Fin n → Bool) : Bool := decide (∀ i, x i = true)
def wt (x : Fin n → Bool) : ℕ := (Finset.univ.filter (fun i => x i = true)).card
theorem crank_and_le_two :
    crank (fun a b : Fin n → Bool => andAll a && andAll b) ≤ 2 := by
  unfold crank
  have hcard : ({(fun b => andAll b), (fun _ : Fin n → Bool => false)} :
      Finset ((Fin n → Bool) → Bool)).card ≤ 2 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    simp
  refine le_trans (Finset.card_le_card ?_) hcard
  intro row hrow
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hrow
  obtain ⟨a, rfl⟩ := hrow
  by_cases ha : andAll a = true
  · exact Finset.mem_insert.mpr (Or.inl (by funext b; simp [ha]))
  · simp only [Bool.not_eq_true] at ha
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (by funext b; simp [ha])))
theorem crank_modq_le (q : ℕ) (hq : 1 ≤ q) :
    crank (fun a b : Fin n → Bool => decide ((wt a + wt b) % q = 0)) ≤ q := by
  unfold crank
  refine le_trans (Finset.card_le_card
    (show (univ.image (fun a b : Fin n → Bool => decide ((wt a + wt b) % q = 0)))
        ⊆ (Finset.range q).image (fun r => fun b : Fin n → Bool => decide ((r + wt b) % q = 0)) from ?_))
    (le_trans Finset.card_image_le (by rw [Finset.card_range]))
  intro row hrow
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hrow
  obtain ⟨a, rfl⟩ := hrow
  refine Finset.mem_image.mpr ⟨wt a % q, Finset.mem_range.mpr (Nat.mod_lt _ (by omega)), ?_⟩
  funext b
  have hmod : (wt a + wt b) % q = (wt a % q + wt b) % q := by
    rw [Nat.add_mod, Nat.add_mod (wt a % q) (wt b), Nat.mod_mod]
  rw [hmod]

end PallLean.Paper93.DeepMath.PathB.PcrankTest

#print axioms PallLean.Paper93.DeepMath.PathB.PcrankTest.crank_and_le_two
#print axioms PallLean.Paper93.DeepMath.PathB.PcrankTest.crank_modq_le
