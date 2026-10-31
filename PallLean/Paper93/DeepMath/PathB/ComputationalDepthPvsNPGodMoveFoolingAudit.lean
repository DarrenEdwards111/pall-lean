import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPSATBoundaryFoolingWidthLB

/-!
# God-Move identity-minor audit: genuine semantic shape versus appended sheets

The Desktop `p vs np1` manuscript's Global God-Move and the constructed SAT boundary theorem share a real
combinatorial skeleton:

```text
row choices × suffix tests → equality/identity minor → boundary/rank lower bound.
```

This file separates two logically different ways that skeleton can arise.

1. `equalityCNF a b` is **semantic**: the SAT decision itself is the equality-matrix entry.  The existing
   fooling theorem therefore gives an exponential one-cut width lower bound.
2. An `AppendedSheetCompilation` may carry an arbitrary high-information sheet beside a computation while the
   final decision reads only the computation component.  Projection recovers the sheet perfectly, but this says
   nothing about decision hardness.  `identitySheetConstantDecision` is the explicit countermodel.

Thus an identity minor extracted from a compiled representation is useful for a decision lower bound only after
one proves a *causal/semantic coupling theorem*: the selected minor entries must be actual decision behaviours
under suffix completions, not an independently appended payload.

## Honest scope

This is an audit theorem, not `P ≠ NP`.  It formalizes both the valid God-Move shape and the exact dead-padding
failure mode of an acceptance-independent verifier sheet.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPGodMoveFoolingAudit

open PallLean.Paper93.DeepMath.PathB.PvsNPBoundaryFoolingWidthLB
open PallLean.Paper93.DeepMath.PathB.PvsNPSATBoundaryFoolingWidthLB
open SATDepthMachine

/-! ## A generic independently appended sheet -/

/-- A compilation that places an auxiliary sheet beside the actual run state.  No coupling is assumed. -/
structure AppendedSheetCompilation (Input Run Sheet : Type) where
  run : Input → Run
  sheet : Input → Sheet

namespace AppendedSheetCompilation

/-- The compiled representation is the actual run paired with the auxiliary sheet. -/
def compiled {Input Run Sheet : Type} (C : AppendedSheetCompilation Input Run Sheet)
    (x : Input) : Run × Sheet :=
  (C.run x, C.sheet x)

/-- The manuscript-style projection onto the appended sheet. -/
def extract {Input Run Sheet : Type} (_C : AppendedSheetCompilation Input Run Sheet) :
    Run × Sheet → Sheet :=
  Prod.snd

/-- Extraction is exact for every appended sheet, regardless of what the computation does. -/
theorem extract_compiled {Input Run Sheet : Type} (C : AppendedSheetCompilation Input Run Sheet)
    (x : Input) : C.extract (C.compiled x) = C.sheet x :=
  rfl

/-- A final observer that reads only the actual run component. -/
def decision {Input Run Sheet : Type} (C : AppendedSheetCompilation Input Run Sheet)
    (observe : Run → Bool) (x : Input) : Bool :=
  observe (C.compiled x).1

/-- The decision is definitionally independent of the appended sheet. -/
theorem decision_eq_run {Input Run Sheet : Type} (C : AppendedSheetCompilation Input Run Sheet)
    (observe : Run → Bool) (x : Input) : C.decision observe x = observe (C.run x) :=
  rfl

/-- Replacing the whole sheet by an arbitrary new payload leaves every decision unchanged. -/
theorem decision_invariant_under_sheet_replacement
    {Input Run Sheet₁ Sheet₂ : Type}
    (C : AppendedSheetCompilation Input Run Sheet₁) (newSheet : Input → Sheet₂)
    (observe : Run → Bool) (x : Input) :
    C.decision observe x =
      (AppendedSheetCompilation.mk C.run newSheet).decision observe x :=
  rfl

end AppendedSheetCompilation

/-! ## Explicit dead-padding countermodel -/

/-- A compilation with a one-state actual run and the entire input copied into the auxiliary sheet. -/
def identitySheetConstantDecision (n : Nat) :
    AppendedSheetCompilation (Fin n → Bool) Unit (Fin n → Bool) where
  run := fun _ => ()
  sheet := id

/-- The projected sheet retains all `2^n` labels injectively. -/
theorem identitySheet_extract_injective (n : Nat) :
    Function.Injective (fun x =>
      (identitySheetConstantDecision n).extract
        ((identitySheetConstantDecision n).compiled x)) := by
  intro a b h
  exact h

/-- Nevertheless the actual decision is constantly false. -/
theorem identitySheet_decision_false (n : Nat) (x : Fin n → Bool) :
    (identitySheetConstantDecision n).decision (fun _ => false) x = false :=
  rfl

/-- For nonempty inputs, exact extraction of all labels does not make the constant decision injective. -/
theorem identitySheet_decision_not_injective (n : Nat) (hn : 0 < n) :
    ¬ Function.Injective
      (fun x => (identitySheetConstantDecision n).decision (fun _ => false) x) := by
  intro hinj
  let i : Fin n := ⟨0, hn⟩
  let a : Fin n → Bool := fun _ => false
  let b : Fin n → Bool := fun j => decide (j = i)
  have hab : a ≠ b := by
    intro h
    have hi := congrFun h i
    simp [a, b] at hi
  apply hab
  apply hinj
  rfl

/-! ## The genuine semantic God-Move shape for actual SAT -/

/-- The concrete SAT family itself realizes the equality/identity matrix. -/
theorem semantic_GodMove_entry {n : Nat} (a b : Fin n → Bool) :
    Satisfiable (equalityCNF a b) ↔ EQ n a b = true := by
  rw [equalityCNF_satisfiable_iff]
  simp [EQ]

/-- Every pair of distinct rows in the SAT matrix is separated by a real suffix formula. -/
theorem semantic_GodMove_fooling (n : Nat) :
    Fooling (fun (a : Fin n → Bool) (b : Fin n → Bool) => scanEquality a b) Finset.univ := by
  intro a₁ _ a₂ _ hne
  refine ⟨a₁, ?_⟩
  change scanEquality a₁ a₁ ≠ scanEquality a₂ a₁
  rw [scanEquality_eq_EQ, scanEquality_eq_EQ]
  simp [EQ, Ne.symm hne]

/-- **Genuine God-Move width consequence.**  When the extracted identity entries are the actual SAT decisions,
the constructed fooling argument forces `2^n` boundary states. -/
theorem semantic_GodMove_boundary_lower_bound (n : Nat)
    (D : LayeredBoundaryDecider n n) (hSAT : ComputesEqualitySAT D) :
    2 ^ n ≤ @Fintype.card D.State D.fintype :=
  card_ge_two_pow_of_computes_equalitySAT n D hSAT

/-! ## Calibration statement -/

/-- Exact projection of an injective sheet and a constant final decision coexist.  Therefore no theorem may infer
decision hardness from `extract_compiled = sheet` plus sheet injectivity alone. -/
theorem exact_injective_extraction_with_trivial_decision (n : Nat) :
    Function.Injective (fun x =>
      (identitySheetConstantDecision n).extract
        ((identitySheetConstantDecision n).compiled x)) ∧
      (∀ x, (identitySheetConstantDecision n).decision (fun _ => false) x = false) := by
  exact ⟨identitySheet_extract_injective n, identitySheet_decision_false n⟩

end PallLean.Paper93.DeepMath.PathB.PvsNPGodMoveFoolingAudit

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPGodMoveFoolingAudit.identitySheet_extract_injective
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPGodMoveFoolingAudit.identitySheet_decision_not_injective
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPGodMoveFoolingAudit.semantic_GodMove_boundary_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPGodMoveFoolingAudit.exact_injective_extraction_with_trivial_decision
