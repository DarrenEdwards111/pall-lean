import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBitHierarchy

/-!
# Bit-cost hierarchy — why the `e₀` discharge is still fuel-blocked (PROVED, honest correction)

Attempting to discharge `hsim` (`bit_hierarchy_of_simulator`) for a **polynomial** `bigbound` reveals an
obstruction I earlier underestimated.  `bitEnum cost bound e n` is defined with a `Code.evaln (bound n)`
conjunct — it charges **`Code` fuel** for the output check.  This file proves `bitEnum` is therefore
*dominated by the fuel measure*:

  `bitEnum_implies_timedEnum` : `bitEnum cost bound e n = true → timedEnum bound e n = true`.

Consequence for the discharge.  `hsim` needs `bitEnum cost bigbound e₀ = diag(bitEnum cost bound)` with `e₀` a
real `Code`.  When the diagonal is `true`, `e₀` must satisfy `Code.evaln (bigbound k) e₀ k = some 1` — i.e.
halt within `bigbound k` *fuel*.  But `e₀` runs the memo interpreter, whose `Code` execution carries the
single-`Nat` table (`≥ 2^cfgRank`, `ComputationalDepthKleeneMemoBlowup`), so its `evaln` fuel is
super-polynomial.  Hence `bigbound` cannot be polynomial: **the `Code.evaln` conjunct re-imports the very fuel
blow-up the bit-cost measure was meant to avoid.**

The honest conclusion (correcting the earlier "polynomial `e₀` is a bit-cost-`O(1)` shell" framing): a
faithful *polynomial* bit-cost hierarchy cannot route the output check through `Code.evaln`.  It requires an
execution model with **addressable memory** (a RAM machine) in place of `Code.evaln` — which the Kleene `Code`
foundation fundamentally lacks (everything is one `Nat`, which blows up).  Building that RAM model is a
substantial foundational construction, not a wiring shell.  The polynomial bit-cost of the *abstract* flat DP
(`bitBounded_efficient`) is real, but it is a RAM-cost; it is not realised by any `Code`.

This is stated, not faked.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

open Nat.Partrec Nat.Partrec.Code
open PallLean.Paper93.DeepMath.PathB.ACC0TimedEnumeration (timedEnum)

namespace PallLean.Paper93.DeepMath.PathB.BitHierarchy

/-- **`bitEnum` is dominated by the fuel measure**: accepting under `bitEnum cost bound` requires accepting
under `timedEnum bound` — the `Code.evaln (bound n)` check is a conjunct of `bitEnum`. -/
theorem bitEnum_implies_timedEnum (cost : ℕ → ℕ → ℕ) (bound : ℕ → ℕ) (e n : ℕ)
    (h : bitEnum cost bound e n = true) : timedEnum bound e n = true := by
  unfold bitEnum at h
  unfold timedEnum
  simp only [Bool.and_eq_true] at h
  exact h.2

/-- The bit-cost time class (as defined, via `Code.evaln`) is contained in the fuel time class — so it does
not escape the fuel measure for the simulator half. -/
theorem inTimeBit_subset_inTime (cost : ℕ → ℕ → ℕ) (bound : ℕ → ℕ) (L : ℕ → Bool)
    (h : InTimeBit cost bound L) :
    ∃ e, ∀ n, L n = true → timedEnum bound e n = true := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, fun n hn => bitEnum_implies_timedEnum cost bound e n (he ▸ hn)⟩

end PallLean.Paper93.DeepMath.PathB.BitHierarchy

#print axioms PallLean.Paper93.DeepMath.PathB.BitHierarchy.bitEnum_implies_timedEnum
