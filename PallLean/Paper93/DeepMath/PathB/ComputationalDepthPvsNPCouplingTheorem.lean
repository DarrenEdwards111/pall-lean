import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPGodMoveFoolingAudit

/-!
# The coupling theorem for the one-cut (bounded-width) machine class

`…GodMoveFoolingAudit` proved that injective extraction of an appended sheet says **nothing** about decision
hardness: a compiler can carry `2^n` labels beside a computation whose decision is constant.  So a fooling
lower bound is only meaningful when the extracted identity minor is a **sufficient statistic for the actual
decision** — the thing the decision reads — not a side channel.

This file supplies the missing coupling theorem for the genuinely restricted **one-cut / one-way-communication
/ bounded-width** class (`LayeredBoundaryDecider`):

* `SufficientStatistic T f` — `T` determines the decision `f` on every suffix.
* `mid_sufficient` — **the coupling**: the boundary state of a one-cut decider is a sufficient statistic for
  its decision (the decision literally factors through it; there is no side channel).
* `sufficient_card_ge_fooling` — the coupling lower bound is **intrinsic to the decision function**: *every*
  sufficient statistic needs at least `|fooling set|` values.
* `coupled_card_ge_fooling` / `equalitySAT_coupled_lower_bound` — hence a one-cut decider for the equality-CNF
  SAT family needs `2^n` boundary states, and the bound is on its **actual resource**.

The loophole is closed constructively: `sheet_injectivity_gives_no_decision_bound` shows the appended sheet's
extraction is injective while the decision's *own* sufficient statistic (`run`) collapses to one value, so
`sufficient_card_ge_fooling` correctly bounds the run (resource `1`), never the irrelevant sheet.

## Honest scope

A genuine coupling theorem for the **bounded-width one-cut model**.  It transfers the fooling bound to the
machine's real decision resource *only because that model has no side channel* — the decision is a function of
the single boundary state.  It does **not** extend to general `P`-time machines (which have workspace, multiple
passes, and adaptive access — genuine side channels), and it is **not** `SAT ∉ P` or `P ≠ NP`.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPCouplingTheorem

open PallLean.Paper93.DeepMath.PathB.PvsNPBoundaryFoolingWidthLB
open PallLean.Paper93.DeepMath.PathB.PvsNPSATBoundaryFoolingWidthLB
open PallLean.Paper93.DeepMath.PathB.PvsNPGodMoveFoolingAudit
open SATDepthMachine

/-! ## Sufficient statistics and the coupling -/

/-- `T` is a **sufficient statistic** for the decision family `f` if equal `T`-values force equal decisions on
every suffix.  This is exactly "the decision reads only `T`" — no side channel. -/
def SufficientStatistic {p q : Nat} {S : Type*} (T : (Fin p → Bool) → S)
    (f : (Fin p → Bool) → (Fin q → Bool) → Bool) : Prop :=
  ∀ a₁ a₂, T a₁ = T a₂ → ∀ b, f a₁ b = f a₂ b

/-- **The coupling.**  The boundary state of a one-cut decider is a sufficient statistic for its own decision:
`D.eval` factors through `D.mid` by construction, so nothing decision-relevant escapes it. -/
theorem mid_sufficient {p q : Nat} (D : LayeredBoundaryDecider p q) :
    SufficientStatistic D.mid D.eval := by
  intro a₁ a₂ h b
  simp only [LayeredBoundaryDecider.eval, h]

/-- **The coupling lower bound (intrinsic).**  Any sufficient statistic for `f` is injective on any fooling
set of `f`. -/
theorem sufficient_injOn_fooling {p q : Nat} {S : Type*} {T : (Fin p → Bool) → S}
    {f : (Fin p → Bool) → (Fin q → Bool) → Bool}
    (hT : SufficientStatistic T f) {Sset : Finset (Fin p → Bool)} (hfool : Fooling f Sset) :
    Set.InjOn T (↑Sset) := by
  intro a₁ h₁ a₂ h₂ hTeq
  by_contra hne
  obtain ⟨b, hb⟩ := hfool a₁ h₁ a₂ h₂ hne
  exact hb (hT a₁ a₂ hTeq b)

/-- Hence **every** sufficient statistic needs at least `|fooling set|` values — a lower bound that depends
only on the decision function, not on any representation. -/
theorem sufficient_card_ge_fooling {p q : Nat} {S : Type*} [Fintype S]
    {T : (Fin p → Bool) → S} {f : (Fin p → Bool) → (Fin q → Bool) → Bool}
    (hT : SufficientStatistic T f) {Sset : Finset (Fin p → Bool)} (hfool : Fooling f Sset) :
    Sset.card ≤ Fintype.card S := by
  calc Sset.card ≤ (Finset.univ : Finset S).card :=
        Finset.card_le_card_of_injOn T (fun _ _ => Finset.mem_univ _)
          (sufficient_injOn_fooling hT hfool)
    _ = Fintype.card S := Finset.card_univ

/-- **The machine's actual boundary is bounded.**  A one-cut decider computing `f` has at least `|fooling set|`
boundary states — its real resource, because `mid` is sufficient. -/
theorem coupled_card_ge_fooling {p q : Nat} (D : LayeredBoundaryDecider p q)
    {f : (Fin p → Bool) → (Fin q → Bool) → Bool} (hf : ∀ a b, D.eval a b = f a b)
    {Sset : Finset (Fin p → Bool)} (hfool : Fooling f Sset) :
    Sset.card ≤ @Fintype.card D.State D.fintype := by
  letI := D.fintype
  have hTsuff : SufficientStatistic D.mid f := by
    intro a₁ a₂ h b
    rw [← hf a₁ b, ← hf a₂ b]
    exact mid_sufficient D a₁ a₂ h b
  exact sufficient_card_ge_fooling hTsuff hfool

/-! ## Application: the equality-CNF SAT family, coupled to the real resource -/

/-- **Coupled SAT lower bound.**  Any one-cut decider correct on the concrete `equalityCNF` family needs `2^n`
boundary states, and by `mid_sufficient` the bound is on its actual decision-carrying resource, not a sheet. -/
theorem equalitySAT_coupled_lower_bound (n : Nat) (D : LayeredBoundaryDecider n n)
    (hSAT : ComputesEqualitySAT D) :
    2 ^ n ≤ @Fintype.card D.State D.fintype := by
  have hf : ∀ a b, D.eval a b = EQ n a b := computes_EQ_of_computesEqualitySAT D hSAT
  have h := coupled_card_ge_fooling D hf (fooling_EQ n)
  rwa [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h

/-! ## The loophole is closed: the sheet is not the decision's sufficient statistic -/

/-- For an appended-sheet compilation, the **run** — not the sheet — is a sufficient statistic for the
decision: the decision reads only the run component. -/
theorem run_sufficient {Input Run Sheet : Type} (C : AppendedSheetCompilation Input Run Sheet)
    (observe : Run → Bool) :
    ∀ x y, C.run x = C.run y → C.decision observe x = C.decision observe y := by
  intro x y h
  simp only [AppendedSheetCompilation.decision, AppendedSheetCompilation.compiled, h]

/-- **The countermodel, resolved.**  In the identity-sheet compilation the extracted sheet is injective
(`2^n` labels), yet the decision's *own* sufficient statistic (the run) sends every input to the same value.
So the coupling bound `sufficient_card_ge_fooling`, applied to the statistic the decision actually reads,
gives the honest resource `1` — the injective sheet is irrelevant.  Extraction hardness only bounds the
decision when the extracted map **is** a sufficient statistic, which the one-cut boundary always is
(`mid_sufficient`) and an appended sheet need not be. -/
theorem sheet_injectivity_gives_no_decision_bound (n : Nat) :
    Function.Injective
      (fun x => (identitySheetConstantDecision n).extract
        ((identitySheetConstantDecision n).compiled x)) ∧
    (∀ x y : Fin n → Bool,
      (identitySheetConstantDecision n).run x = (identitySheetConstantDecision n).run y) :=
  ⟨identitySheet_extract_injective n, fun _ _ => rfl⟩

end PallLean.Paper93.DeepMath.PathB.PvsNPCouplingTheorem

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPCouplingTheorem.mid_sufficient
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPCouplingTheorem.sufficient_card_ge_fooling
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPCouplingTheorem.equalitySAT_coupled_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPCouplingTheorem.sheet_injectivity_gives_no_decision_bound
