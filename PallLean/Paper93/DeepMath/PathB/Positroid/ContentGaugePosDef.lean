import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenGauge
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef

/-!
# Positive definiteness of the content-driven gauge (Path B / Positroid)

This file packages the §28.3 positive-definiteness of the compiled gadget
(`compiledGadget_posDef`) at the **content-driven coupling**
`contentDrivenAlpha T`, yielding that the **content-driven gauge witness**
`contentDrivenGauge T = compiledGadget (contentDrivenAlpha T) n` is
`Matrix.PosDef` for every `SATDeciderTableau m n` with `n ≥ 1`.

Because the coupling `contentDrivenAlpha T = 1 + |tableauTraceCoupling T|`
is always at least `1`, hence strictly positive
(`contentDrivenAlpha_pos`), the hypotheses of `compiledGadget_posDef` are
satisfied unconditionally on the tableau.  The only remaining hypothesis is
`1 ≤ n`, which is recorded as a separate argument so that the conclusion
matches the Path B convention that the gadget acts on a non-empty vertex
set.

We additionally specialise the result at `n = 2` and `n = 3`, the two
small cases used elsewhere in the Path B / Positroid development, and we
record an "any" alias `contentDrivenGauge_posDef_any` to match the calling
convention used by downstream files.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- The content-driven gauge is `PosDef` for any tableau and any `n ≥ 1`. -/
theorem contentDrivenGauge_posDef {m n : ℕ} (T : SATDeciderTableau m n) (hn : 1 ≤ n) :
    (contentDrivenGauge T).PosDef := by
  unfold contentDrivenGauge
  exact compiledGadget_posDef (contentDrivenAlpha T) n (contentDrivenAlpha_pos T) hn

/-- The content-driven gauge at `n = 2` is `PosDef`. -/
theorem contentDrivenGauge_n2_posDef {m : ℕ} (T : SATDeciderTableau m 2) :
    (contentDrivenGauge T).PosDef :=
  contentDrivenGauge_posDef T (by norm_num : 1 ≤ 2)

/-- The content-driven gauge at `n = 3` is `PosDef`. -/
theorem contentDrivenGauge_n3_posDef {m : ℕ} (T : SATDeciderTableau m 3) :
    (contentDrivenGauge T).PosDef :=
  contentDrivenGauge_posDef T (by norm_num : 1 ≤ 3)

/-- For any tableau at `n ≥ 1`, the content-driven gauge is `PosDef`.
    Alias of `contentDrivenGauge_posDef` matching the calling convention
    used by downstream files. -/
theorem contentDrivenGauge_posDef_any {m n : ℕ} (T : SATDeciderTableau m n) (hn : 1 ≤ n) :
    (contentDrivenGauge T).PosDef :=
  contentDrivenGauge_posDef T hn

end PallLean.Paper93.DeepMath.PathB.Positroid
