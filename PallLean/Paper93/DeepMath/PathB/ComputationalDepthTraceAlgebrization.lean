import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTraceRelativization

/-!
# A measure-level non-language-invariance fact: `traceInv` is not language-invariant

**Scope, stated honestly up front.**  This file proves a *measure-level* fact — `traceInv` is not
determined by the decided language — and connects it, informally, to algebrization.  It is **not** a
genuine algebrization-barrier evasion.  Algebrization (Aaronson–Wigderson) is about proof techniques
that hold relative to a low-degree extension `Ã` of an oracle; escaping it requires exhibiting a
technique that fails against some such extension, which needs the full oracle/low-degree-extension
machine model — entirely absent here.  What is proved is only that one measure reads more than the
language and any language-determined view of it.

The content: a *relativizing* view sees a machine through its decided language; an *algebrizing*
view additionally sees the extension `Ã`, but `Ã` is a deterministic function of the language, so
both are **functions of the decided language**.  A measure determined by the decided language alone
(`LanguageInvariant`) is invisible to both.  `traceInv` is not language-invariant: the two machines
of `TraceRelativization` decide the **same** language yet have different `traceInv`
(`traceInv_not_languageInvariant`).  So `traceInv` reads the actual computation, strictly more than
any function of the language.  Read this as "the measure is not language-invariant," not "the schema
evades algebrization."

**Three measure-level non-invariance facts, not three barrier evasions.**  Machine-dependence
(`TraceRelativization`), non-largeness (`NaturalProofs`), and non-language-invariance (here) are
each a necessary condition for a language-determined / density-based barrier not to apply — a
suggestive record that the schema's measures are not invariant in the ways the classical barriers
exploit, but weaker than genuine evasion of the relativization / natural-proofs / algebrization
barriers, each of which is a statement in a model this development does not build.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TraceAlgebrization

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.TraceMeasureSchema
open PallLean.Paper93.DeepMath.PathB.TraceRelativization (traceInv_machine_dependent)

/-- A machine-indexed quantity is **language-invariant** if it is determined by the decided
language: any two machines deciding the same language receive the same value.  Both relativizing
and algebrizing techniques induce language-invariant measures — the low-degree extension is a
function of the language, so it adds nothing beyond it. -/
def LanguageInvariant (F : Machine → (ℕ → ℕ)) : Prop :=
  ∀ (M₁ M₂ : Machine) (L : List Bool → Bool) (T₁ T₂ : ℕ → ℕ),
    Decides M₁ L T₁ → Decides M₂ L T₂ → F M₁ = F M₂

/-- **`traceInv` is not language-invariant.**  Two machines deciding the same language have
different `traceInv traceSize`, so the measure is not determined by the decided language — it
reads the actual computation, strictly more than the language or any function of it (including
the low-degree extension).  (This is machine-dependence at the measure level, not a proof that
the schema evades the algebrization barrier.) -/
theorem traceInv_not_languageInvariant : ¬ LanguageInvariant (traceInv traceSize) := by
  obtain ⟨M₁, M₂, L, T₁, T₂, hD1, hD2, hne⟩ := traceInv_machine_dependent
  intro hinv
  exact hne (congrFun (hinv M₁ M₂ L T₁ T₂ hD1 hD2) 1)

/-- **The common-core statement.**  Any language-invariant measure agrees on the two same-language
witness machines; `traceInv traceSize` does not — so no language-determined barrier
(relativization or algebrization) can characterize it. -/
theorem no_languageInvariant_captures_traceInv :
    ∀ F : Machine → (ℕ → ℕ), LanguageInvariant F →
      ∃ (M₁ M₂ : Machine) (L : List Bool → Bool) (T₁ T₂ : ℕ → ℕ),
        Decides M₁ L T₁ ∧ Decides M₂ L T₂ ∧ F M₁ = F M₂
          ∧ traceInv traceSize M₁ 1 ≠ traceInv traceSize M₂ 1 := by
  intro F hF
  obtain ⟨M₁, M₂, L, T₁, T₂, hD1, hD2, hne⟩ := traceInv_machine_dependent
  exact ⟨M₁, M₂, L, T₁, T₂, hD1, hD2, hF M₁ M₂ L T₁ T₂ hD1 hD2, hne⟩

end PallLean.Paper93.DeepMath.PathB.TraceAlgebrization
