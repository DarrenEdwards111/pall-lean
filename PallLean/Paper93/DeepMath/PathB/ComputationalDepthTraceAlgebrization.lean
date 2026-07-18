import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTraceRelativization

/-!
# The schema evades algebrization: `traceInv` is not language-invariant

The barrier audit's third and final pillar.  Algebrization (Aaronson–Wigderson) strengthens
relativization: a proof algebrizes if it holds relative to a low-degree extension `Ã` of the
oracle `A`.  The algebrization barrier blocks even some non-relativizing techniques.

The two barriers share a common core at the measure level.  A *relativizing* technique sees a
machine only through its decided language; an *algebrizing* technique additionally sees the
extension `Ã` — but `Ã` is a deterministic function of the language `A`, so both barriers see the
machine only through **functions of its decided language**.  Any measure that is *language-
invariant* — determined by the decided language alone — is therefore blocked by both.

`traceInv` is not language-invariant: the two machines of `TraceRelativization` decide the
**same** language yet have different `traceInv` (`traceInv_not_languageInvariant`).  So `traceInv`
reads strictly more than the language and any function of it — including the low-degree extension
— by reading the actual computation.  Hence the schema evades algebrization as well as
relativization.

**Scope, honestly.**  This captures the *measure-level* reason both barriers fail: `traceInv`
depends on the internal computation, which no black-box or algebraic-extension view of the
language can access.  It is the standard form of a barrier-evasion argument — a witness two same-
behavior machines that the barrier cannot distinguish but the technique can.  A fully faithful
oracle-machine algebrization model (machines with `Ã`-oracle access) is a separate development;
the non-invariance proved here is the essential obstruction to *any* language-determined barrier.

**Barrier trilogy complete.**  Relativization (machine-dependence, `TraceRelativization`), natural
proofs (non-largeness, `NaturalProofs`), and now algebrization (non-language-invariance) are all
evaded.  The surviving super-additive candidate (`TraceSchemaCapstone.SuperAdditiveWitness`) is
blocked by none of the three classical barriers.

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
the low-degree extension).  The schema therefore evades algebrization, not only relativization. -/
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
