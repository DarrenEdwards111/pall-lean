import PallLean.GlobalGodMoveGauge
import PallLean.PaperFaithfulCompilation

/-!
# Instrumented sheet extraction vs semantic force

This module records the distinction that matters for the Book-1 / Theorem-207
route.

The paper machinery can expose an extractable coupled sheet from an
instrumented presentation.  That is not yet the same as proving that the
original classical DTM run was semantically forced to realize the God-Move
boundary.  The extra content is an essentiality theorem: deleting the sheet, or
treating it as a static add-on, must change the acceptance semantics.

The definitions below make that separation explicit.  They do not add any new
axiom or closure claim.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine PaperFaithfulSeparation MultilinearSPDP

namespace InstrumentedSheetAudit

/-! ## The static ΠΦ template

The paper-faithful `ΠΦ` extraction theorem is a genuine algebraic fact:
if the `v`-part is killed by `ΠΦ`, then the `u`-sheet is extracted.  This
section packages that fact while deliberately keeping acceptance semantics
separate.
-/

/-- A static sheet add-on in the paper's `u/v` split: a coupled sheet `Q` and a
remainder `R` that is killed by `ΠΦ`. -/
structure StaticSheetAddOn (σ : PaperFaithfulCompilation.UVSplit) : Type where
  Q : PaperFaithfulCompilation.CoupledSheetPoly σ
  R : PaperFaithfulCompilation.PMnPoly σ
  killedByPiPhi : PaperFaithfulCompilation.piPhi σ R = 0

namespace StaticSheetAddOn

/-- The instrumented/static sheet is extracted by `ΠΦ`.  This is exactly the
paper's algebraic extraction template, and it uses no acceptance semantics. -/
theorem extracts
    {σ : PaperFaithfulCompilation.UVSplit}
    (S : StaticSheetAddOn σ) :
    PaperFaithfulCompilation.piPhi σ
        (PaperFaithfulCompilation.CoupledSheetPoly.embed σ S.Q + S.R) =
      PaperFaithfulCompilation.CoupledSheetPoly.embed σ S.Q :=
  PaperFaithfulCompilation.piPhi_embed_add_kill σ S.Q S.R S.killedByPiPhi

/-- Extraction remains true for every external acceptance predicate `A`; the
predicate is intentionally unused.  This is the formal audit point: algebraic
extractability alone is independent of semantic essentiality. -/
theorem extracts_independent_of_acceptance
    {σ : PaperFaithfulCompilation.UVSplit}
    (S : StaticSheetAddOn σ)
    (_A : PaperFaithfulCompilation.PMnPoly σ -> Prop) :
    PaperFaithfulCompilation.piPhi σ
        (PaperFaithfulCompilation.CoupledSheetPoly.embed σ S.Q + S.R) =
      PaperFaithfulCompilation.CoupledSheetPoly.embed σ S.Q :=
  S.extracts

end StaticSheetAddOn

/-- A minimal semantic essentiality predicate for a static sheet presentation:
with respect to an acceptance predicate `A`, the full instrumented polynomial
is accepted but the remainder obtained by deleting the sheet is not.

This is intentionally separate from `StaticSheetAddOn.extracts`.  It is the
kind of extra theorem needed before an extracted sheet can be read as a
boundary forced by the computation rather than a static add-on. -/
def StaticSheetEssentialForAcceptance
    {σ : PaperFaithfulCompilation.UVSplit}
    (A : PaperFaithfulCompilation.PMnPoly σ -> Prop)
    (S : StaticSheetAddOn σ) : Prop :=
  A (PaperFaithfulCompilation.CoupledSheetPoly.embed σ S.Q + S.R) ∧
    ¬ A S.R

/-- Static semantic force is extraction plus essentiality. -/
structure StaticSheetSemanticForce
    (σ : PaperFaithfulCompilation.UVSplit) : Type where
  addOn : StaticSheetAddOn σ
  accepts : PaperFaithfulCompilation.PMnPoly σ -> Prop
  essential : StaticSheetEssentialForAcceptance accepts addOn

/-- Semantic force forgets to plain instrumented extraction, but not conversely.
The converse would require the missing essentiality theorem. -/
def staticSheetSemanticForce_forgets_to_addOn
    {σ : PaperFaithfulCompilation.UVSplit}
    (F : StaticSheetSemanticForce σ) :
    StaticSheetAddOn σ :=
  F.addOn

/-! ## Theorem 207 surface

At the Route-B level, the paper gives an instrumented extraction shape.  The
stronger classical force claim must additionally prove that the extracted sheet
is acceptance-essential for the original run semantics.
-/

/-- The instrumented Theorem-207 sheet package: an extracted coupled sheet, rank
monotonicity of the extraction, and the NP-side sheet lower bound.  This is the
paper's extractable-sheet layer; it is not yet a semantic force theorem. -/
structure InstrumentedTheorem207Sheet
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Type where
  extraction :
    GlobalGodMoveGauge.Theorem207Extraction M n hn hn2 htb hns
  rankMonotone :
    GlobalGodMoveGauge.Theorem207ExtractionRankMonotone
      M n hn hn2 htb hns extraction
  npLower :
    GlobalGodMoveGauge.Theorem207NPSideLowerBound
      M n hn hn2 htb hns extraction

namespace InstrumentedTheorem207Sheet

/-- The coupled sheet in an instrumented Theorem-207 presentation has the
paper's NP-side lower bound. -/
theorem sheet_np_lower
    {M : DTM} {n : ℕ} {hn : n ≥ 2 ^ 804} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (S : InstrumentedTheorem207Sheet M n hn hn2 htb hns) :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) S.extraction.coupledSheet :=
  S.npLower.sheet_np_side_lower_bound

/-- The extraction map is rank non-increasing on the instrumented presentation.
-/
theorem extraction_rank_le_compiled
    {M : DTM} {n : ℕ} {hn : n ≥ 2 ^ 804} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (S : InstrumentedTheorem207Sheet M n hn hn2 htb hns) :
    mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) S.extraction.coupledSheet ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) S.extraction.paperCompiledPoly :=
  S.rankMonotone.extraction_rank_monotone

end InstrumentedTheorem207Sheet

/-- Essentiality for a Theorem-207 sheet.  The predicate `Accepts` is left
explicit because this is exactly the semantics that the classical-run proof
must supply.  The condition says the paper-compiled object is accepted while
the extracted sheet by itself is not enough to stand in for that computation.

This is deliberately not derivable from `InstrumentedTheorem207Sheet`; it is
the missing semantic theorem. -/
def Theorem207SheetEssentialForAcceptance
    {M : DTM} {n : ℕ} {hn : n ≥ 2 ^ 804} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (Accepts :
      MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ ->
        Prop)
    (S : InstrumentedTheorem207Sheet M n hn hn2 htb hns) : Prop :=
  Accepts S.extraction.paperCompiledPoly ∧
    ¬ Accepts S.extraction.coupledSheet

/-- The precise strong theorem shape: a classical run has a God-Move boundary
only when the instrumented extraction is accompanied by an acceptance
essentiality proof. -/
structure Theorem207ClassicalSemanticForce
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Type where
  instrumented :
    InstrumentedTheorem207Sheet M n hn hn2 htb hns
  Accepts :
    MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ ->
      Prop
  essential :
    Theorem207SheetEssentialForAcceptance Accepts instrumented

/-- Classical semantic force implies an instrumented sheet.  This is the easy
forgetful direction. -/
def theorem207ClassicalSemanticForce_forgets_to_instrumented
    {M : DTM} {n : ℕ} {hn : n ≥ 2 ^ 804} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (F : Theorem207ClassicalSemanticForce M n hn hn2 htb hns) :
    InstrumentedTheorem207Sheet M n hn hn2 htb hns :=
  F.instrumented

/-- Instrumented extraction plus essentiality is exactly the classical semantic
force package.  This theorem is intentionally tautological: it identifies the
single missing proof obligation as `Theorem207SheetEssentialForAcceptance`. -/
theorem theorem207ClassicalSemanticForce_iff_instrumented_and_essential
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    Nonempty (Theorem207ClassicalSemanticForce M n hn hn2 htb hns) ↔
      ∃ (S : InstrumentedTheorem207Sheet M n hn hn2 htb hns),
        ∃ Accepts :
          MvPolynomial
            (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ ->
            Prop,
          Theorem207SheetEssentialForAcceptance Accepts S := by
  constructor
  · intro h
    rcases h with ⟨F⟩
    exact ⟨F.instrumented, F.Accepts, F.essential⟩
  · rintro ⟨S, Accepts, hEss⟩
    exact ⟨{
      instrumented := S
      Accepts := Accepts
      essential := hEss
    }⟩

/-- A full legacy `Theorem207Witness` supplies the instrumented sheet layer.
It does not by itself supply `Theorem207SheetEssentialForAcceptance`. -/
noncomputable def instrumentedSheet_of_theorem207Witness
    {M : DTM} {n : ℕ} {hn : n ≥ 2 ^ 804} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (W : GlobalGodMoveGauge.Theorem207Witness M n hn hn2 htb hns) :
    InstrumentedTheorem207Sheet M n hn hn2 htb hns where
  extraction :=
    GlobalGodMoveGauge.theorem207Extraction_of_witness M n hn hn2 htb hns W
  rankMonotone :=
    GlobalGodMoveGauge.theorem207ExtractionRankMonotone_of_witness
      M n hn hn2 htb hns W
  npLower :=
    GlobalGodMoveGauge.theorem207NPSideLowerBound_of_witness
      M n hn hn2 htb hns W

end InstrumentedSheetAudit

end PallLean.Paper93.DeepMath.PathB
