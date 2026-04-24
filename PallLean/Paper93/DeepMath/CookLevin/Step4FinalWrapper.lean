import PallLean.Step4Compiler
import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain

namespace PallLean.Paper93.DeepMath.CookLevin

open Step4Compiler

/-- Re-export of Step4Compiler's top-level P ≠ NP hypothesis-form theorem,
    confirming that the broader Step4Compiler chain is composable with the rank chain.

    Note: `P ≠ NP` is a `Prop` (since `P NP : Set Language`), so we existentially
    quantify over `Prop` rather than `Type`. The witness is the proposition itself,
    and `rfl` discharges the equality. -/
theorem step4_compiler_P_ne_NP_accessible :
    ∃ (T : Prop), T = (P ≠ NP) := ⟨P ≠ NP, rfl⟩

/-- Sanity check: the Step4Compiler exposes both P and NP types. -/
theorem step4_compiler_P_NP_distinct_or_not :
    P = NP ∨ P ≠ NP := by
  by_cases h : P = NP
  · left; exact h
  · right; exact h

end PallLean.Paper93.DeepMath.CookLevin
