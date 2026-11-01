-- TRIMMED SCRATCH COPY (research/gap-g3 kernel-check only; NOT part of the branch).
-- Original: codex/godmove-gap-repairs @ 21921958, PallLean/Paper93/DeepMath/PathB/ComputationalDepthCookLevinEmitClockBounds3.lean
-- Kept: the `PolyBounded` closure kit (original lines 3-70 verbatim: PB_const PB_id PB_le PB_add PB_mul),
-- the only names `ComposablePpolyDischarge` imports from this module.
-- Changed: the import (original: ...CookLevinEmitClockBounds2) is replaced by the two modules that the kit
-- needs (PvsNPSeparatingInvariant for `PolyBounded`; Mathlib.Data.List.GetD, the only external import the
-- original closure adds), and the `open` lines naming Emit-chain namespaces are removed. Everything after
-- line 70 (Emit stream-length bounds) is dropped.
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPSeparatingInvariant
import Mathlib.Data.List.GetD
-- (also the two non-Emit modules ComposablePpolyDischarge itself imports, so its environment is unchanged)
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthComposableStepCircuit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATCircuitSeparationBridge

/-!
# Cook–Levin M2 emitter — E6 step 21: THE CLOSER'S INGREDIENTS

Everything the final assembly composes from: the `PolyBounded` closure kit (constants,
identity, pointwise domination, sums, products — so the explicit `coreClock` majorant is
polynomial by construction), the three remaining stream-length bounds
(`cellEmitOut`/`triRowOut`/`headEmitOut`), the pass-bound `t`-monotonicity (so per-round
bounds lift to the grand loop's worst round), and the `run_stable` freeze lift
(`pipeline_at`: the pipeline's `HaltsBy`/`transOut` hold at ANY clock above the exact one).
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitClockBounds3

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-! ## The `PolyBounded` closure kit -/

theorem PB_const (c : ℕ) : PolyBounded (fun _ => c) :=
  ⟨c, 0, fun n => by simp⟩

theorem PB_id : PolyBounded (fun n => n) :=
  ⟨1, 1, fun n => by simp⟩

theorem PB_le {f g : ℕ → ℕ} (h : ∀ n, g n ≤ f n) (hf : PolyBounded f) :
    PolyBounded g := by
  obtain ⟨c, k, hck⟩ := hf
  exact ⟨c, k, fun n => le_trans (h n) (hck n)⟩

theorem PB_add {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded (fun n => f n + g n) := by
  obtain ⟨c1, k1, h1⟩ := hf
  obtain ⟨c2, k2, h2⟩ := hg
  refine ⟨c1 + c2, max k1 k2, fun n => ?_⟩
  show f n + g n ≤ (c1 + c2) * (n + 1) ^ max k1 k2
  have e1 : (n + 1) ^ k1 ≤ (n + 1) ^ max k1 k2 :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have e2 : (n + 1) ^ k2 ≤ (n + 1) ^ max k1 k2 :=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have := h1 n
  have := h2 n
  have m1 : c1 * (n + 1) ^ k1 ≤ c1 * (n + 1) ^ max k1 k2 := Nat.mul_le_mul_left _ e1
  have m2 : c2 * (n + 1) ^ k2 ≤ c2 * (n + 1) ^ max k1 k2 := Nat.mul_le_mul_left _ e2
  have : (c1 + c2) * (n + 1) ^ max k1 k2
      = c1 * (n + 1) ^ max k1 k2 + c2 * (n + 1) ^ max k1 k2 := by ring
  omega

theorem PB_mul {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded (fun n => f n * g n) := by
  obtain ⟨c1, k1, h1⟩ := hf
  obtain ⟨c2, k2, h2⟩ := hg
  refine ⟨c1 * c2, k1 + k2, fun n => ?_⟩
  show f n * g n ≤ c1 * c2 * (n + 1) ^ (k1 + k2)
  have := Nat.mul_le_mul (h1 n) (h2 n)
  have e : c1 * (n + 1) ^ k1 * (c2 * (n + 1) ^ k2)
      = c1 * c2 * (n + 1) ^ (k1 + k2) := by
    rw [pow_add]; ring
  omega

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitClockBounds3
