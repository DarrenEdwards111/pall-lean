import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATCutLemma
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATTwoGadget

/-!
# The six-sign substrate, the master refinement, and the case-A kills

Brick 3b-i of the `+2` campaign.  The six-fold sign completion of the two-gadget
codec word, with everything the collision case analysis consumes:

* **`sixUpd` / `word_sixUpd` / `SATFamily_sixUpd` (proved)** — the completion, its
  word identity at every `N ≥ 46`, and its value `AllEq₃(s₁s₂s₃) && AllEq₃(s₄s₅s₆)`;
* **`sixUpd_at*` / `sixUpd_upd*` (proved)** — slot evaluations and slot updates;
* **`sign12_dep6` … `sign45_dep6` (proved)** — all six sign positions are genuine
  dependencies;
* **`refine_sixUpd` (proved)** — THE MASTER REFINEMENT: if every changed slot has
  all its var gates below `u`, equal `u`-values force equal outputs (the cut lemma
  applied at the root);
* **`killA_g0` / `killA_g1` (proved)** — a gadget whose three sign gates all avoid
  `u` kills the near-floor circuit outright (`extractG` count spec + tree split
  vs the codec's `AllEqual₃`).

Bricks 3b-ii/iii add the B1 prefix kill, the B2/B3 refinement kills, and the
case-tree capstone `cbudget (SATFamily N) ≥ 2·deps + 1`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.SATFamilyDenseFloor

/-- Fin-literal disequality from value disequality. -/
theorem fne {N a b : ℕ} (ha : a < N) (hb : b < N) (h : a ≠ b) :
    (⟨a, ha⟩ : Fin N) ≠ ⟨b, hb⟩ := by
  intro he
  rw [Fin.mk.injEq] at he
  exact h he

/-! ### The six-sign completion and its word identity -/

/-- The six-fold sign completion of the two-gadget base word. -/
def sixUpd (N : ℕ) (h12 : 12 < N) (h18 : 18 < N) (h24 : 24 < N) (h31 : 31 < N)
    (h38 : 38 < N) (h45 : 45 < N) (s₁ s₂ s₃ s₄ s₅ s₆ : Bool) : Fin N → Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (zBase2 N) ⟨12, h12⟩ s₁) ⟨18, h18⟩ s₂)
    ⟨24, h24⟩ s₃) ⟨31, h31⟩ s₄) ⟨38, h38⟩ s₅) ⟨45, h45⟩ s₆

/-- **The six-sign word identity (proved)**. -/
theorem word_sixUpd (N : ℕ) (hN : 46 ≤ N) (h12 : 12 < N) (h18 : 18 < N)
    (h24 : 24 < N) (h31 : 31 < N) (h38 : 38 < N) (h45 : 45 < N)
    (s₁ s₂ s₃ s₄ s₅ s₆ : Bool) :
    wordOfFin (sixUpd N h12 h18 h24 h31 h38 h45 s₁ s₂ s₃ s₄ s₅ s₆)
      = encodeFormula' (se2 s₁ s₂ s₃ s₄ s₅ s₆) ++ List.replicate (N - 46) false := by
  rw [se2_concrete]
  apply List.ext_getElem
  · simp only [wordOfFin_length, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]
    omega
  · intro k h1 h2
    have hkN : k < N := by rw [wordOfFin_length] at h1; exact h1
    rw [wordOfFin_getElem _ k h1 hkN]
    by_cases hk46 : k < 46
    · interval_cases k <;> rfl
    · push_neg at hk46
      show (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (zBase2 N) ⟨12, h12⟩ s₁) ⟨18, h18⟩ s₂)
        ⟨24, h24⟩ s₃) ⟨31, h31⟩ s₄) ⟨38, h38⟩ s₅) ⟨45, h45⟩ s₆) ⟨k, hkN⟩ = _
      rw [Function.update_of_ne (fne hkN h45 (by omega)),
        Function.update_of_ne (fne hkN h38 (by omega)),
        Function.update_of_ne (fne hkN h31 (by omega)),
        Function.update_of_ne (fne hkN h24 (by omega)),
        Function.update_of_ne (fne hkN h18 (by omega)),
        Function.update_of_ne (fne hkN h12 (by omega))]
      have hzb : zBase2 N ⟨k, hkN⟩ = false := by
        show sBase2.getD k false = false
        have hlen : sBase2.length ≤ k := by
          simp only [sBase2, List.length_cons, List.length_nil]
          omega
        rw [List.getD_eq_default _ _ hlen]
      rw [hzb]
      have hlen46 : ([true, true, true, true, true, true, false,
          true, false, false, false, false, s₁,
          true, false, false, false, false, s₂,
          true, false, false, false, false, s₃,
          true, false, false, false, true, false, s₄,
          true, false, false, false, true, false, s₅,
          true, false, false, false, true, false, s₆] : List Bool).length ≤ k := by
        simp only [List.length_cons, List.length_nil]
        omega
      rw [List.getElem_append_right hlen46]
      rw [List.getElem_replicate]

/-- **The six-sign value (proved)**: the codec realizes `AEm 2` on the completion. -/
theorem SATFamily_sixUpd (N : ℕ) (hN : 46 ≤ N) (h12 : 12 < N) (h18 : 18 < N)
    (h24 : 24 < N) (h31 : 31 < N) (h38 : 38 < N) (h45 : 45 < N)
    (s₁ s₂ s₃ s₄ s₅ s₆ : Bool) :
    SATFamily N (sixUpd N h12 h18 h24 h31 h38 h45 s₁ s₂ s₃ s₄ s₅ s₆)
      = (allEq3 s₁ s₂ s₃ && allEq3 s₄ s₅ s₆) := by
  rw [SATFamily_apply, word_sixUpd N hN h12 h18 h24 h31 h38 h45 s₁ s₂ s₃ s₄ s₅ s₆,
    SATLang_se2_append]

/-! ### Slot evaluations -/

section SlotEval

variable {N : ℕ} (h12 : 12 < N) (h18 : 18 < N) (h24 : 24 < N) (h31 : 31 < N)
  (h38 : 38 < N) (h45 : 45 < N) (s₁ s₂ s₃ s₄ s₅ s₆ : Bool)

theorem sixUpd_at12 :
    sixUpd N h12 h18 h24 h31 h38 h45 s₁ s₂ s₃ s₄ s₅ s₆ ⟨12, h12⟩ = s₁ := by
  show (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (zBase2 N) ⟨12, h12⟩ s₁) ⟨18, h18⟩ s₂)
    ⟨24, h24⟩ s₃) ⟨31, h31⟩ s₄) ⟨38, h38⟩ s₅) ⟨45, h45⟩ s₆) ⟨12, h12⟩ = s₁
  rw [Function.update_of_ne (fne h12 h45 (by omega)),
    Function.update_of_ne (fne h12 h38 (by omega)),
    Function.update_of_ne (fne h12 h31 (by omega)),
    Function.update_of_ne (fne h12 h24 (by omega)),
    Function.update_of_ne (fne h12 h18 (by omega)), Function.update_self]

theorem sixUpd_at18 :
    sixUpd N h12 h18 h24 h31 h38 h45 s₁ s₂ s₃ s₄ s₅ s₆ ⟨18, h18⟩ = s₂ := by
  show (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (zBase2 N) ⟨12, h12⟩ s₁) ⟨18, h18⟩ s₂)
    ⟨24, h24⟩ s₃) ⟨31, h31⟩ s₄) ⟨38, h38⟩ s₅) ⟨45, h45⟩ s₆) ⟨18, h18⟩ = s₂
  rw [Function.update_of_ne (fne h18 h45 (by omega)),
    Function.update_of_ne (fne h18 h38 (by omega)),
    Function.update_of_ne (fne h18 h31 (by omega)),
    Function.update_of_ne (fne h18 h24 (by omega)), Function.update_self]

theorem sixUpd_at24 :
    sixUpd N h12 h18 h24 h31 h38 h45 s₁ s₂ s₃ s₄ s₅ s₆ ⟨24, h24⟩ = s₃ := by
  show (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (zBase2 N) ⟨12, h12⟩ s₁) ⟨18, h18⟩ s₂)
    ⟨24, h24⟩ s₃) ⟨31, h31⟩ s₄) ⟨38, h38⟩ s₅) ⟨45, h45⟩ s₆) ⟨24, h24⟩ = s₃
  rw [Function.update_of_ne (fne h24 h45 (by omega)),
    Function.update_of_ne (fne h24 h38 (by omega)),
    Function.update_of_ne (fne h24 h31 (by omega)), Function.update_self]

theorem sixUpd_at31 :
    sixUpd N h12 h18 h24 h31 h38 h45 s₁ s₂ s₃ s₄ s₅ s₆ ⟨31, h31⟩ = s₄ := by
  show (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (zBase2 N) ⟨12, h12⟩ s₁) ⟨18, h18⟩ s₂)
    ⟨24, h24⟩ s₃) ⟨31, h31⟩ s₄) ⟨38, h38⟩ s₅) ⟨45, h45⟩ s₆) ⟨31, h31⟩ = s₄
  rw [Function.update_of_ne (fne h31 h45 (by omega)),
    Function.update_of_ne (fne h31 h38 (by omega)), Function.update_self]

theorem sixUpd_at38 :
    sixUpd N h12 h18 h24 h31 h38 h45 s₁ s₂ s₃ s₄ s₅ s₆ ⟨38, h38⟩ = s₅ := by
  show (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (zBase2 N) ⟨12, h12⟩ s₁) ⟨18, h18⟩ s₂)
    ⟨24, h24⟩ s₃) ⟨31, h31⟩ s₄) ⟨38, h38⟩ s₅) ⟨45, h45⟩ s₆) ⟨38, h38⟩ = s₅
  rw [Function.update_of_ne (fne h38 h45 (by omega)), Function.update_self]

theorem sixUpd_at45 :
    sixUpd N h12 h18 h24 h31 h38 h45 s₁ s₂ s₃ s₄ s₅ s₆ ⟨45, h45⟩ = s₆ := by
  show (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (zBase2 N) ⟨12, h12⟩ s₁) ⟨18, h18⟩ s₂)
    ⟨24, h24⟩ s₃) ⟨31, h31⟩ s₄) ⟨38, h38⟩ s₅) ⟨45, h45⟩ s₆) ⟨45, h45⟩ = s₆
  rw [Function.update_self]

theorem sixUpd_at_other (i : Fin N) (hi12 : i ≠ ⟨12, h12⟩) (hi18 : i ≠ ⟨18, h18⟩)
    (hi24 : i ≠ ⟨24, h24⟩) (hi31 : i ≠ ⟨31, h31⟩) (hi38 : i ≠ ⟨38, h38⟩)
    (hi45 : i ≠ ⟨45, h45⟩) :
    sixUpd N h12 h18 h24 h31 h38 h45 s₁ s₂ s₃ s₄ s₅ s₆ i = zBase2 N i := by
  show (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (zBase2 N) ⟨12, h12⟩ s₁) ⟨18, h18⟩ s₂)
    ⟨24, h24⟩ s₃) ⟨31, h31⟩ s₄) ⟨38, h38⟩ s₅) ⟨45, h45⟩ s₆) i = zBase2 N i
  rw [Function.update_of_ne hi45, Function.update_of_ne hi38,
    Function.update_of_ne hi31, Function.update_of_ne hi24,
    Function.update_of_ne hi18, Function.update_of_ne hi12]

end SlotEval

/-! ### Slot updates -/

section SlotUpd

variable {N : ℕ} (h12 : 12 < N) (h18 : 18 < N) (h24 : 24 < N) (h31 : 31 < N)
  (h38 : 38 < N) (h45 : 45 < N) (s₁ s₂ s₃ s₄ s₅ s₆ b : Bool)

theorem sixUpd_upd1 :
    Function.update (sixUpd N h12 h18 h24 h31 h38 h45 s₁ s₂ s₃ s₄ s₅ s₆) ⟨12, h12⟩ b
      = sixUpd N h12 h18 h24 h31 h38 h45 b s₂ s₃ s₄ s₅ s₆ := by
  show Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (zBase2 N) ⟨12, h12⟩ s₁)
      ⟨18, h18⟩ s₂) ⟨24, h24⟩ s₃) ⟨31, h31⟩ s₄) ⟨38, h38⟩ s₅) ⟨45, h45⟩ s₆)
      ⟨12, h12⟩ b = _
  rw [Function.update_comm (fne h45 h12 (by omega)),
    Function.update_comm (fne h38 h12 (by omega)),
    Function.update_comm (fne h31 h12 (by omega)),
    Function.update_comm (fne h24 h12 (by omega)),
    Function.update_comm (fne h18 h12 (by omega)), Function.update_idem]
  rfl

theorem sixUpd_upd2 :
    Function.update (sixUpd N h12 h18 h24 h31 h38 h45 s₁ s₂ s₃ s₄ s₅ s₆) ⟨18, h18⟩ b
      = sixUpd N h12 h18 h24 h31 h38 h45 s₁ b s₃ s₄ s₅ s₆ := by
  show Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (zBase2 N) ⟨12, h12⟩ s₁)
      ⟨18, h18⟩ s₂) ⟨24, h24⟩ s₃) ⟨31, h31⟩ s₄) ⟨38, h38⟩ s₅) ⟨45, h45⟩ s₆)
      ⟨18, h18⟩ b = _
  rw [Function.update_comm (fne h45 h18 (by omega)),
    Function.update_comm (fne h38 h18 (by omega)),
    Function.update_comm (fne h31 h18 (by omega)),
    Function.update_comm (fne h24 h18 (by omega)), Function.update_idem]
  rfl

theorem sixUpd_upd3 :
    Function.update (sixUpd N h12 h18 h24 h31 h38 h45 s₁ s₂ s₃ s₄ s₅ s₆) ⟨24, h24⟩ b
      = sixUpd N h12 h18 h24 h31 h38 h45 s₁ s₂ b s₄ s₅ s₆ := by
  show Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (zBase2 N) ⟨12, h12⟩ s₁)
      ⟨18, h18⟩ s₂) ⟨24, h24⟩ s₃) ⟨31, h31⟩ s₄) ⟨38, h38⟩ s₅) ⟨45, h45⟩ s₆)
      ⟨24, h24⟩ b = _
  rw [Function.update_comm (fne h45 h24 (by omega)),
    Function.update_comm (fne h38 h24 (by omega)),
    Function.update_comm (fne h31 h24 (by omega)), Function.update_idem]
  rfl

theorem sixUpd_upd4 :
    Function.update (sixUpd N h12 h18 h24 h31 h38 h45 s₁ s₂ s₃ s₄ s₅ s₆) ⟨31, h31⟩ b
      = sixUpd N h12 h18 h24 h31 h38 h45 s₁ s₂ s₃ b s₅ s₆ := by
  show Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (zBase2 N) ⟨12, h12⟩ s₁)
      ⟨18, h18⟩ s₂) ⟨24, h24⟩ s₃) ⟨31, h31⟩ s₄) ⟨38, h38⟩ s₅) ⟨45, h45⟩ s₆)
      ⟨31, h31⟩ b = _
  rw [Function.update_comm (fne h45 h31 (by omega)),
    Function.update_comm (fne h38 h31 (by omega)), Function.update_idem]
  rfl

theorem sixUpd_upd5 :
    Function.update (sixUpd N h12 h18 h24 h31 h38 h45 s₁ s₂ s₃ s₄ s₅ s₆) ⟨38, h38⟩ b
      = sixUpd N h12 h18 h24 h31 h38 h45 s₁ s₂ s₃ s₄ b s₆ := by
  show Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (zBase2 N) ⟨12, h12⟩ s₁)
      ⟨18, h18⟩ s₂) ⟨24, h24⟩ s₃) ⟨31, h31⟩ s₄) ⟨38, h38⟩ s₅) ⟨45, h45⟩ s₆)
      ⟨38, h38⟩ b = _
  rw [Function.update_comm (fne h45 h38 (by omega)), Function.update_idem]
  rfl

theorem sixUpd_upd6 :
    Function.update (sixUpd N h12 h18 h24 h31 h38 h45 s₁ s₂ s₃ s₄ s₅ s₆) ⟨45, h45⟩ b
      = sixUpd N h12 h18 h24 h31 h38 h45 s₁ s₂ s₃ s₄ s₅ b := by
  show Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (zBase2 N) ⟨12, h12⟩ s₁)
      ⟨18, h18⟩ s₂) ⟨24, h24⟩ s₃) ⟨31, h31⟩ s₄) ⟨38, h38⟩ s₅) ⟨45, h45⟩ s₆)
      ⟨45, h45⟩ b = _
  rw [Function.update_idem]
  rfl

end SlotUpd

/-! ### The six sign dependencies -/

section SignDeps

variable (N : ℕ) (hN : 46 ≤ N) (h12 : 12 < N) (h18 : 18 < N) (h24 : 24 < N)
  (h31 : 31 < N) (h38 : 38 < N) (h45 : 45 < N)

include hN h12 h18 h24 h31 h38 h45

theorem sign12_dep6 : (⟨12, h12⟩ : Fin N) ∈ depSet (SATFamily N) := by
  rw [mem_depSet]
  refine ⟨sixUpd N h12 h18 h24 h31 h38 h45 true true true true true true, false, ?_⟩
  rw [sixUpd_upd1,
    SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 false true true true true true,
    SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true true true true true true]
  decide

theorem sign18_dep6 : (⟨18, h18⟩ : Fin N) ∈ depSet (SATFamily N) := by
  rw [mem_depSet]
  refine ⟨sixUpd N h12 h18 h24 h31 h38 h45 true true true true true true, false, ?_⟩
  rw [sixUpd_upd2,
    SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true false true true true true,
    SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true true true true true true]
  decide

theorem sign24_dep6 : (⟨24, h24⟩ : Fin N) ∈ depSet (SATFamily N) := by
  rw [mem_depSet]
  refine ⟨sixUpd N h12 h18 h24 h31 h38 h45 true true true true true true, false, ?_⟩
  rw [sixUpd_upd3,
    SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true true false true true true,
    SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true true true true true true]
  decide

theorem sign31_dep6 : (⟨31, h31⟩ : Fin N) ∈ depSet (SATFamily N) := by
  rw [mem_depSet]
  refine ⟨sixUpd N h12 h18 h24 h31 h38 h45 true true true true true true, false, ?_⟩
  rw [sixUpd_upd4,
    SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true true true false true true,
    SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true true true true true true]
  decide

theorem sign38_dep6 : (⟨38, h38⟩ : Fin N) ∈ depSet (SATFamily N) := by
  rw [mem_depSet]
  refine ⟨sixUpd N h12 h18 h24 h31 h38 h45 true true true true true true, false, ?_⟩
  rw [sixUpd_upd5,
    SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true true true true false true,
    SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true true true true true true]
  decide

theorem sign45_dep6 : (⟨45, h45⟩ : Fin N) ∈ depSet (SATFamily N) := by
  rw [mem_depSet]
  refine ⟨sixUpd N h12 h18 h24 h31 h38 h45 true true true true true true, false, ?_⟩
  rw [sixUpd_upd6,
    SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true true true true true false,
    SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true true true true true true]
  decide

end SignDeps

/-! ### THE MASTER REFINEMENT -/

/-- **The master refinement (proved)**: if every changed slot has all its var gates
below `u`, equal `u`-values force equal outputs. -/
theorem refine_sixUpd (N : ℕ) (h12 : 12 < N) (h18 : 18 < N) (h24 : 24 < N)
    (h31 : 31 < N) (h38 : 38 < N) (h45 : 45 < N)
    (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    {u : ℕ} (hR : reconvR c = {u})
    (s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆ : Bool)
    (hb1 : s₁ = t₁ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨12, h12⟩ : Fin N) → Reach c u q)
    (hb2 : s₂ = t₂ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨18, h18⟩ : Fin N) → Reach c u q)
    (hb3 : s₃ = t₃ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨24, h24⟩ : Fin N) → Reach c u q)
    (hb4 : s₄ = t₄ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨31, h31⟩ : Fin N) → Reach c u q)
    (hb5 : s₅ = t₅ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨38, h38⟩ : Fin N) → Reach c u q)
    (hb6 : s₆ = t₆ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨45, h45⟩ : Fin N) → Reach c u q)
    (hwu : wire c (sixUpd N h12 h18 h24 h31 h38 h45 s₁ s₂ s₃ s₄ s₅ s₆) u
      = wire c (sixUpd N h12 h18 h24 h31 h38 h45 t₁ t₂ t₃ t₄ t₅ t₆) u) :
    SATFamily N (sixUpd N h12 h18 h24 h31 h38 h45 s₁ s₂ s₃ s₄ s₅ s₆)
      = SATFamily N (sixUpd N h12 h18 h24 h31 h38 h45 t₁ t₂ t₃ t₄ t₅ t₆) := by
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_singleton_self u
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have hult : u < c.length := (mem_cone.mp huc).1
  have hroot_nb : ¬ Reach c u (c.length - 1) := by
    intro hr
    have h1 := reach_le hr
    exact hune (by omega)
  have hagree : ∀ i : Fin N,
      (∃ q, q ∈ cone c ∧ c.getD q (.cst false) = CGate.var i ∧ ¬ Reach c u q) →
      sixUpd N h12 h18 h24 h31 h38 h45 s₁ s₂ s₃ s₄ s₅ s₆ i
        = sixUpd N h12 h18 h24 h31 h38 h45 t₁ t₂ t₃ t₄ t₅ t₆ i := by
    intro i hex
    obtain ⟨q, hqc, hqg, hqnb⟩ := hex
    by_cases e1 : i = ⟨12, h12⟩
    · subst e1
      rw [sixUpd_at12, sixUpd_at12]
      rcases hb1 with he | hall
      · exact he
      · exact absurd (hall q hqc hqg) hqnb
    by_cases e2 : i = ⟨18, h18⟩
    · subst e2
      rw [sixUpd_at18, sixUpd_at18]
      rcases hb2 with he | hall
      · exact he
      · exact absurd (hall q hqc hqg) hqnb
    by_cases e3 : i = ⟨24, h24⟩
    · subst e3
      rw [sixUpd_at24, sixUpd_at24]
      rcases hb3 with he | hall
      · exact he
      · exact absurd (hall q hqc hqg) hqnb
    by_cases e4 : i = ⟨31, h31⟩
    · subst e4
      rw [sixUpd_at31, sixUpd_at31]
      rcases hb4 with he | hall
      · exact he
      · exact absurd (hall q hqc hqg) hqnb
    by_cases e5 : i = ⟨38, h38⟩
    · subst e5
      rw [sixUpd_at38, sixUpd_at38]
      rcases hb5 with he | hall
      · exact he
      · exact absurd (hall q hqc hqg) hqnb
    by_cases e6 : i = ⟨45, h45⟩
    · subst e6
      rw [sixUpd_at45, sixUpd_at45]
      rcases hb6 with he | hall
      · exact he
      · exact absurd (hall q hqc hqg) hqnb
    rw [sixUpd_at_other h12 h18 h24 h31 h38 h45 _ _ _ _ _ _ i e1 e2 e3 e4 e5 e6,
      sixUpd_at_other h12 h18 h24 h31 h38 h45 _ _ _ _ _ _ i e1 e2 e3 e4 e5 e6]
  have hcut := cut_agree c u hs hR ((mem_cone.mp huc).2)
    (sixUpd N h12 h18 h24 h31 h38 h45 s₁ s₂ s₃ s₄ s₅ s₆)
    (sixUpd N h12 h18 h24 h31 h38 h45 t₁ t₂ t₃ t₄ t₅ t₆) hwu hagree
    (c.length - 1) (mem_cone.mpr ⟨by omega, InCone.root⟩) hroot_nb
  rw [← hcomp (sixUpd N h12 h18 h24 h31 h38 h45 s₁ s₂ s₃ s₄ s₅ s₆),
    ← hcomp (sixUpd N h12 h18 h24 h31 h38 h45 t₁ t₂ t₃ t₄ t₅ t₆),
    output_eq_wire, output_eq_wire]
  exact hcut

/-! ### The case-A kills: a gadget fully avoiding `u` -/

/-- **Kill A, gadget 0 (proved)**: if all three `x₀`-sign gates avoid `u`, the
near-floor circuit is impossible. -/
theorem killA_g0 (N : ℕ) (hN : 46 ≤ N) (h12 : 12 < N) (h18 : 18 < N) (h24 : 24 < N)
    (h31 : 31 < N) (h38 : 38 < N) (h45 : 45 < N)
    (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    (hlen : c.length ≤ 2 * (depSet (SATFamily N)).card)
    {u : ℕ} (hR : reconvR c = {u})
    {q12 q18 q24 : ℕ}
    (hq12c : q12 ∈ cone c) (hq12g : c.getD q12 (.cst false) = CGate.var ⟨12, h12⟩)
    (hnb12 : ¬ Reach c u q12)
    (hq18c : q18 ∈ cone c) (hq18g : c.getD q18 (.cst false) = CGate.var ⟨18, h18⟩)
    (hnb18 : ¬ Reach c u q18)
    (hq24c : q24 ∈ cone c) (hq24g : c.getD q24 (.cst false) = CGate.var ⟨24, h24⟩)
    (hnb24 : ¬ Reach c u q24) : False := by
  have hWd := (spare_bound (SATFamily N) c hcomp hs hlen).2.1
  have huniq := unique_var_gate (SATFamily N) c hcomp hs (le_of_eq hWd)
  have hd12 := sign12_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd18 := sign18_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd24 := sign24_dep6 N hN h12 h18 h24 h31 h38 h45
  have hroot : c.length - 1 ∈ cone c := mem_cone.mpr ⟨by omega, InCone.root⟩
  have hRv : ∀ q₀ : ℕ, ¬ Reach c u q₀ → ∀ u' ∈ reconvR c, ¬ Reach c u' q₀ := by
    intro q₀ hnb u' hu'
    rw [hR] at hu'
    rw [Finset.mem_singleton.mp hu']
    exact hnb
  have hcnt12 := (extractG_cnt_spec c hs ⟨12, h12⟩ q12 hq12c hq12g
      (fun q hq hg => huniq ⟨12, h12⟩ hd12 q hq q12 hq12c hg hq12g)
      (hRv q12 hnb12) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq12c).2)
  have hcnt18 := (extractG_cnt_spec c hs ⟨18, h18⟩ q18 hq18c hq18g
      (fun q hq hg => huniq ⟨18, h18⟩ hd18 q hq q18 hq18c hg hq18g)
      (hRv q18 hnb18) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq18c).2)
  have hcnt24 := (extractG_cnt_spec c hs ⟨24, h24⟩ q24 hq24c hq24g
      (fun q hq hg => huniq ⟨24, h24⟩ hd24 q hq q24 hq24c hg hq24g)
      (hRv q24 hnb24) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq24c).2)
  have hsp := gtree_split_cnt (extractG c c.length (c.length - 1))
    ⟨12, h12⟩ ⟨18, h18⟩ ⟨24, h24⟩
    (fne h12 h18 (by omega)) (fne h12 h24 (by omega)) (fne h18 h24 (by omega))
    (sixUpd N h12 h18 h24 h31 h38 h45 true true true true true true)
    hcnt12 hcnt18 hcnt24
  have heval : ∀ y, (extractG c c.length (c.length - 1)).eval y = SATFamily N y := by
    intro y
    rw [extractG_eval c c.length (c.length - 1) (by omega) (by omega) y]
    exact hcomp y
  have heq : (fun a b g => (extractG c c.length (c.length - 1)).eval
      (Function.update (Function.update (Function.update
        (sixUpd N h12 h18 h24 h31 h38 h45 true true true true true true)
        ⟨12, h12⟩ a) ⟨18, h18⟩ b) ⟨24, h24⟩ g)) = allEq3 := by
    funext a b g
    rw [sixUpd_upd1, sixUpd_upd2, sixUpd_upd3, heval,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 a b g true true true,
      show allEq3 true true true = true from rfl, Bool.and_true]
  rw [heq] at hsp
  rcases hsp with h | h | h
  · exact allEq3_no_split_a h
  · exact allEq3_no_split_b h
  · exact allEq3_no_split_c h

/-- **Kill A, gadget 1 (proved)**: if all three `x₁`-sign gates avoid `u`, the
near-floor circuit is impossible. -/
theorem killA_g1 (N : ℕ) (hN : 46 ≤ N) (h12 : 12 < N) (h18 : 18 < N) (h24 : 24 < N)
    (h31 : 31 < N) (h38 : 38 < N) (h45 : 45 < N)
    (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    (hlen : c.length ≤ 2 * (depSet (SATFamily N)).card)
    {u : ℕ} (hR : reconvR c = {u})
    {q31 q38 q45 : ℕ}
    (hq31c : q31 ∈ cone c) (hq31g : c.getD q31 (.cst false) = CGate.var ⟨31, h31⟩)
    (hnb31 : ¬ Reach c u q31)
    (hq38c : q38 ∈ cone c) (hq38g : c.getD q38 (.cst false) = CGate.var ⟨38, h38⟩)
    (hnb38 : ¬ Reach c u q38)
    (hq45c : q45 ∈ cone c) (hq45g : c.getD q45 (.cst false) = CGate.var ⟨45, h45⟩)
    (hnb45 : ¬ Reach c u q45) : False := by
  have hWd := (spare_bound (SATFamily N) c hcomp hs hlen).2.1
  have huniq := unique_var_gate (SATFamily N) c hcomp hs (le_of_eq hWd)
  have hd31 := sign31_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd38 := sign38_dep6 N hN h12 h18 h24 h31 h38 h45
  have hd45 := sign45_dep6 N hN h12 h18 h24 h31 h38 h45
  have hroot : c.length - 1 ∈ cone c := mem_cone.mpr ⟨by omega, InCone.root⟩
  have hRv : ∀ q₀ : ℕ, ¬ Reach c u q₀ → ∀ u' ∈ reconvR c, ¬ Reach c u' q₀ := by
    intro q₀ hnb u' hu'
    rw [hR] at hu'
    rw [Finset.mem_singleton.mp hu']
    exact hnb
  have hcnt31 := (extractG_cnt_spec c hs ⟨31, h31⟩ q31 hq31c hq31g
      (fun q hq hg => huniq ⟨31, h31⟩ hd31 q hq q31 hq31c hg hq31g)
      (hRv q31 hnb31) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq31c).2)
  have hcnt38 := (extractG_cnt_spec c hs ⟨38, h38⟩ q38 hq38c hq38g
      (fun q hq hg => huniq ⟨38, h38⟩ hd38 q hq q38 hq38c hg hq38g)
      (hRv q38 hnb38) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq38c).2)
  have hcnt45 := (extractG_cnt_spec c hs ⟨45, h45⟩ q45 hq45c hq45g
      (fun q hq hg => huniq ⟨45, h45⟩ hd45 q hq q45 hq45c hg hq45g)
      (hRv q45 hnb45) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq45c).2)
  have hsp := gtree_split_cnt (extractG c c.length (c.length - 1))
    ⟨31, h31⟩ ⟨38, h38⟩ ⟨45, h45⟩
    (fne h31 h38 (by omega)) (fne h31 h45 (by omega)) (fne h38 h45 (by omega))
    (sixUpd N h12 h18 h24 h31 h38 h45 true true true true true true)
    hcnt31 hcnt38 hcnt45
  have heval : ∀ y, (extractG c c.length (c.length - 1)).eval y = SATFamily N y := by
    intro y
    rw [extractG_eval c c.length (c.length - 1) (by omega) (by omega) y]
    exact hcomp y
  have heq : (fun a b g => (extractG c c.length (c.length - 1)).eval
      (Function.update (Function.update (Function.update
        (sixUpd N h12 h18 h24 h31 h38 h45 true true true true true true)
        ⟨31, h31⟩ a) ⟨38, h38⟩ b) ⟨45, h45⟩ g)) = allEq3 := by
    funext a b g
    rw [sixUpd_upd4, sixUpd_upd5, sixUpd_upd6, heval,
      SATFamily_sixUpd N hN h12 h18 h24 h31 h38 h45 true true true a b g,
      show allEq3 true true true = true from rfl, Bool.true_and]
  rw [heq] at hsp
  rcases hsp with h | h | h
  · exact allEq3_no_split_a h
  · exact allEq3_no_split_b h
  · exact allEq3_no_split_c h

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.word_sixUpd
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.refine_sixUpd
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.killA_g0
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.killA_g1
