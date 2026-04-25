import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenGauge
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny

/-!
# Content-driven gauge is not the identity at `n = 2` (and beyond)

This file packages the structural fact that the **content-driven gauge**
`contentDrivenGauge T` is never equal to the identity matrix on
`Fin n` for any `n ≥ 2`, regardless of the tableau `T`.

The proof reduces directly to
`compiledGadget_ne_identity` from `CompiledGadgetNonIdentityAny.lean`,
because `contentDrivenGauge T` is by definition
`compiledGadget (contentDrivenAlpha T) n`.

We also restate the content-distinguishability of
`contentDrivenAlpha` for the zero vs all-ones tableaus, which witnesses
that the content-driven gauge is genuinely content-dependent.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- The content-driven gauge at n=2 is NOT the identity matrix (for ANY tableau). -/
theorem contentDrivenGauge_n2_ne_identity {m : ℕ} (T : SATDeciderTableau m 2) :
    contentDrivenGauge T ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  unfold contentDrivenGauge
  exact compiledGadget_ne_identity (contentDrivenAlpha T) 2 (by norm_num : 2 ≤ 2)

/-- The content-driven gauge at n=3 is NOT the identity matrix (for ANY tableau). -/
theorem contentDrivenGauge_n3_ne_identity {m : ℕ} (T : SATDeciderTableau m 3) :
    contentDrivenGauge T ≠ (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  unfold contentDrivenGauge
  exact compiledGadget_ne_identity (contentDrivenAlpha T) 3 (by norm_num : 2 ≤ 3)

/-- For any n ≥ 2, the content-driven gauge is NOT the identity. -/
theorem contentDrivenGauge_ne_identity_general {m n : ℕ} (T : SATDeciderTableau m n)
    (hn : 2 ≤ n) :
    contentDrivenGauge T ≠ (1 : Matrix (Fin n) (Fin n) ℝ) := by
  unfold contentDrivenGauge
  exact compiledGadget_ne_identity (contentDrivenAlpha T) n hn

/-- The content-driven gauge is content-dependent (different tableaus → different couplings). -/
theorem contentDrivenGauge_distinguishes_zero_allOnes (m n : ℕ) (h : 1 ≤ m * n) :
    contentDrivenAlpha (SATDeciderTableau.zero m n) ≠
    contentDrivenAlpha (SATDeciderTableau.allOnes m n) :=
  contentDrivenAlpha_distinguishes m n h

end PallLean.Paper93.DeepMath.PathB.Positroid
