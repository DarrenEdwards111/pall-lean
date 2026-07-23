import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATSpare2

/-!
# The nine-sign substrate: slot machinery and the master refinement at three gadgets

Brick 3 of the multi-wire campaign — `SATSixSub` scaled to the three-gadget word.

* **`nineUpd` / `word_nineUpd` / `SATFamily_nineUpd` (proved)** — the nine-fold
  sign completion, its word identity at every `N ≥ 73`, and its value
  `AllEq₃ && AllEq₃ && AllEq₃`;
* **`nineUpd_at15 … at72` / `nineUpd_at_other` / `nineUpd_upd1 … upd9` (proved)** —
  slot evaluations and slot updates;
* **`sign15_dep9 … sign72_dep9` (proved)** — all nine sign positions are genuine
  dependencies;
* **`refine_nineUpd` (proved)** — the master refinement at a single reconvergence
  wire, nine-slot version.

The `+3` kills build on this.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.SATFamilyDenseFloor

/-- The nine-fold sign completion of the three-gadget base word. -/
def nineUpd (N : ℕ) (h15 : 15 < N) (h21 : 21 < N) (h27 : 27 < N) (h34 : 34 < N)
    (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N) (h64 : 64 < N) (h72 : 72 < N)
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ : Bool) : Fin N → Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
    (Function.update (zBase3 N) ⟨15, h15⟩ s₁) ⟨21, h21⟩ s₂) ⟨27, h27⟩ s₃)
    ⟨34, h34⟩ s₄) ⟨41, h41⟩ s₅) ⟨48, h48⟩ s₆) ⟨56, h56⟩ s₇) ⟨64, h64⟩ s₈)
    ⟨72, h72⟩ s₉

/-- **The nine-sign word identity (proved)**. -/
theorem word_nineUpd (N : ℕ) (hN : 73 ≤ N) (h15 : 15 < N) (h21 : 21 < N)
    (h27 : 27 < N) (h34 : 34 < N) (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N)
    (h64 : 64 < N) (h72 : 72 < N) (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ : Bool) :
    wordOfFin (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉)
      = encodeFormula' (se3 s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉)
        ++ List.replicate (N - 73) false := by
  rw [se3_concrete]
  apply List.ext_getElem
  · simp only [wordOfFin_length, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]
    omega
  · intro k h1 h2
    have hkN : k < N := by rw [wordOfFin_length] at h1; exact h1
    rw [wordOfFin_getElem _ k h1 hkN]
    by_cases hk73 : k < 73
    · interval_cases k <;> rfl
    · push_neg at hk73
      show (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update
        (Function.update (zBase3 N) ⟨15, h15⟩ s₁) ⟨21, h21⟩ s₂) ⟨27, h27⟩ s₃)
        ⟨34, h34⟩ s₄) ⟨41, h41⟩ s₅) ⟨48, h48⟩ s₆) ⟨56, h56⟩ s₇) ⟨64, h64⟩ s₈)
        ⟨72, h72⟩ s₉) ⟨k, hkN⟩ = _
      rw [Function.update_of_ne (fne hkN h72 (by omega)),
        Function.update_of_ne (fne hkN h64 (by omega)),
        Function.update_of_ne (fne hkN h56 (by omega)),
        Function.update_of_ne (fne hkN h48 (by omega)),
        Function.update_of_ne (fne hkN h41 (by omega)),
        Function.update_of_ne (fne hkN h34 (by omega)),
        Function.update_of_ne (fne hkN h27 (by omega)),
        Function.update_of_ne (fne hkN h21 (by omega)),
        Function.update_of_ne (fne hkN h15 (by omega))]
      have hzb : zBase3 N ⟨k, hkN⟩ = false := by
        show sBase3.getD k false = false
        have hlen : sBase3.length ≤ k := by
          rw [sBase3_length]
          omega
        rw [List.getD_eq_default _ _ hlen]
      rw [hzb]
      have hlen73 : ([true, true, true, true, true, true, true, true, true, false,
          true, false, false, false, false, s₁,
          true, false, false, false, false, s₂,
          true, false, false, false, false, s₃,
          true, false, false, false, true, false, s₄,
          true, false, false, false, true, false, s₅,
          true, false, false, false, true, false, s₆,
          true, false, false, false, true, true, false, s₇,
          true, false, false, false, true, true, false, s₈,
          true, false, false, false, true, true, false, s₉] : List Bool).length ≤ k := by
        simp only [List.length_cons, List.length_nil]
        omega
      rw [List.getElem_append_right hlen73]
      rw [List.getElem_replicate]

/-- **The nine-sign value (proved)**: the codec realizes `AEm 3` on the completion. -/
theorem SATFamily_nineUpd (N : ℕ) (hN : 73 ≤ N) (h15 : 15 < N) (h21 : 21 < N)
    (h27 : 27 < N) (h34 : 34 < N) (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N)
    (h64 : 64 < N) (h72 : 72 < N) (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ : Bool) :
    SATFamily N (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉)
      = (allEq3 s₁ s₂ s₃ && allEq3 s₄ s₅ s₆ && allEq3 s₇ s₈ s₉) := by
  rw [SATFamily_apply,
    word_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉,
    SATLang_se3_append]

/-! ### Slot evaluations -/

section SlotEval9

variable {N : ℕ} (h15 : 15 < N) (h21 : 21 < N) (h27 : 27 < N) (h34 : 34 < N)
  (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N) (h64 : 64 < N) (h72 : 72 < N)
  (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ : Bool)

theorem nineUpd_at15 :
    nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ ⟨15, h15⟩ = s₁ := by
  show (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
    (Function.update (zBase3 N) ⟨15, h15⟩ s₁) ⟨21, h21⟩ s₂) ⟨27, h27⟩ s₃)
    ⟨34, h34⟩ s₄) ⟨41, h41⟩ s₅) ⟨48, h48⟩ s₆) ⟨56, h56⟩ s₇) ⟨64, h64⟩ s₈)
    ⟨72, h72⟩ s₉) ⟨15, h15⟩ = s₁
  rw [Function.update_of_ne (fne h15 h72 (by omega)),
    Function.update_of_ne (fne h15 h64 (by omega)),
    Function.update_of_ne (fne h15 h56 (by omega)),
    Function.update_of_ne (fne h15 h48 (by omega)),
    Function.update_of_ne (fne h15 h41 (by omega)),
    Function.update_of_ne (fne h15 h34 (by omega)),
    Function.update_of_ne (fne h15 h27 (by omega)),
    Function.update_of_ne (fne h15 h21 (by omega)), Function.update_self]

theorem nineUpd_at21 :
    nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ ⟨21, h21⟩ = s₂ := by
  show (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
    (Function.update (zBase3 N) ⟨15, h15⟩ s₁) ⟨21, h21⟩ s₂) ⟨27, h27⟩ s₃)
    ⟨34, h34⟩ s₄) ⟨41, h41⟩ s₅) ⟨48, h48⟩ s₆) ⟨56, h56⟩ s₇) ⟨64, h64⟩ s₈)
    ⟨72, h72⟩ s₉) ⟨21, h21⟩ = s₂
  rw [Function.update_of_ne (fne h21 h72 (by omega)),
    Function.update_of_ne (fne h21 h64 (by omega)),
    Function.update_of_ne (fne h21 h56 (by omega)),
    Function.update_of_ne (fne h21 h48 (by omega)),
    Function.update_of_ne (fne h21 h41 (by omega)),
    Function.update_of_ne (fne h21 h34 (by omega)),
    Function.update_of_ne (fne h21 h27 (by omega)), Function.update_self]

theorem nineUpd_at27 :
    nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ ⟨27, h27⟩ = s₃ := by
  show (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
    (Function.update (zBase3 N) ⟨15, h15⟩ s₁) ⟨21, h21⟩ s₂) ⟨27, h27⟩ s₃)
    ⟨34, h34⟩ s₄) ⟨41, h41⟩ s₅) ⟨48, h48⟩ s₆) ⟨56, h56⟩ s₇) ⟨64, h64⟩ s₈)
    ⟨72, h72⟩ s₉) ⟨27, h27⟩ = s₃
  rw [Function.update_of_ne (fne h27 h72 (by omega)),
    Function.update_of_ne (fne h27 h64 (by omega)),
    Function.update_of_ne (fne h27 h56 (by omega)),
    Function.update_of_ne (fne h27 h48 (by omega)),
    Function.update_of_ne (fne h27 h41 (by omega)),
    Function.update_of_ne (fne h27 h34 (by omega)), Function.update_self]

theorem nineUpd_at34 :
    nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ ⟨34, h34⟩ = s₄ := by
  show (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
    (Function.update (zBase3 N) ⟨15, h15⟩ s₁) ⟨21, h21⟩ s₂) ⟨27, h27⟩ s₃)
    ⟨34, h34⟩ s₄) ⟨41, h41⟩ s₅) ⟨48, h48⟩ s₆) ⟨56, h56⟩ s₇) ⟨64, h64⟩ s₈)
    ⟨72, h72⟩ s₉) ⟨34, h34⟩ = s₄
  rw [Function.update_of_ne (fne h34 h72 (by omega)),
    Function.update_of_ne (fne h34 h64 (by omega)),
    Function.update_of_ne (fne h34 h56 (by omega)),
    Function.update_of_ne (fne h34 h48 (by omega)),
    Function.update_of_ne (fne h34 h41 (by omega)), Function.update_self]

theorem nineUpd_at41 :
    nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ ⟨41, h41⟩ = s₅ := by
  show (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
    (Function.update (zBase3 N) ⟨15, h15⟩ s₁) ⟨21, h21⟩ s₂) ⟨27, h27⟩ s₃)
    ⟨34, h34⟩ s₄) ⟨41, h41⟩ s₅) ⟨48, h48⟩ s₆) ⟨56, h56⟩ s₇) ⟨64, h64⟩ s₈)
    ⟨72, h72⟩ s₉) ⟨41, h41⟩ = s₅
  rw [Function.update_of_ne (fne h41 h72 (by omega)),
    Function.update_of_ne (fne h41 h64 (by omega)),
    Function.update_of_ne (fne h41 h56 (by omega)),
    Function.update_of_ne (fne h41 h48 (by omega)), Function.update_self]

theorem nineUpd_at48 :
    nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ ⟨48, h48⟩ = s₆ := by
  show (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
    (Function.update (zBase3 N) ⟨15, h15⟩ s₁) ⟨21, h21⟩ s₂) ⟨27, h27⟩ s₃)
    ⟨34, h34⟩ s₄) ⟨41, h41⟩ s₅) ⟨48, h48⟩ s₆) ⟨56, h56⟩ s₇) ⟨64, h64⟩ s₈)
    ⟨72, h72⟩ s₉) ⟨48, h48⟩ = s₆
  rw [Function.update_of_ne (fne h48 h72 (by omega)),
    Function.update_of_ne (fne h48 h64 (by omega)),
    Function.update_of_ne (fne h48 h56 (by omega)), Function.update_self]

theorem nineUpd_at56 :
    nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ ⟨56, h56⟩ = s₇ := by
  show (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
    (Function.update (zBase3 N) ⟨15, h15⟩ s₁) ⟨21, h21⟩ s₂) ⟨27, h27⟩ s₃)
    ⟨34, h34⟩ s₄) ⟨41, h41⟩ s₅) ⟨48, h48⟩ s₆) ⟨56, h56⟩ s₇) ⟨64, h64⟩ s₈)
    ⟨72, h72⟩ s₉) ⟨56, h56⟩ = s₇
  rw [Function.update_of_ne (fne h56 h72 (by omega)),
    Function.update_of_ne (fne h56 h64 (by omega)), Function.update_self]

theorem nineUpd_at64 :
    nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ ⟨64, h64⟩ = s₈ := by
  show (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
    (Function.update (zBase3 N) ⟨15, h15⟩ s₁) ⟨21, h21⟩ s₂) ⟨27, h27⟩ s₃)
    ⟨34, h34⟩ s₄) ⟨41, h41⟩ s₅) ⟨48, h48⟩ s₆) ⟨56, h56⟩ s₇) ⟨64, h64⟩ s₈)
    ⟨72, h72⟩ s₉) ⟨64, h64⟩ = s₈
  rw [Function.update_of_ne (fne h64 h72 (by omega)), Function.update_self]

theorem nineUpd_at72 :
    nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ ⟨72, h72⟩ = s₉ := by
  show (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
    (Function.update (zBase3 N) ⟨15, h15⟩ s₁) ⟨21, h21⟩ s₂) ⟨27, h27⟩ s₃)
    ⟨34, h34⟩ s₄) ⟨41, h41⟩ s₅) ⟨48, h48⟩ s₆) ⟨56, h56⟩ s₇) ⟨64, h64⟩ s₈)
    ⟨72, h72⟩ s₉) ⟨72, h72⟩ = s₉
  rw [Function.update_self]

theorem nineUpd_at_other (i : Fin N) (hi15 : i ≠ ⟨15, h15⟩) (hi21 : i ≠ ⟨21, h21⟩)
    (hi27 : i ≠ ⟨27, h27⟩) (hi34 : i ≠ ⟨34, h34⟩) (hi41 : i ≠ ⟨41, h41⟩)
    (hi48 : i ≠ ⟨48, h48⟩) (hi56 : i ≠ ⟨56, h56⟩) (hi64 : i ≠ ⟨64, h64⟩)
    (hi72 : i ≠ ⟨72, h72⟩) :
    nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ i
      = zBase3 N i := by
  show (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
    (Function.update (zBase3 N) ⟨15, h15⟩ s₁) ⟨21, h21⟩ s₂) ⟨27, h27⟩ s₃)
    ⟨34, h34⟩ s₄) ⟨41, h41⟩ s₅) ⟨48, h48⟩ s₆) ⟨56, h56⟩ s₇) ⟨64, h64⟩ s₈)
    ⟨72, h72⟩ s₉) i = zBase3 N i
  rw [Function.update_of_ne hi72, Function.update_of_ne hi64,
    Function.update_of_ne hi56, Function.update_of_ne hi48,
    Function.update_of_ne hi41, Function.update_of_ne hi34,
    Function.update_of_ne hi27, Function.update_of_ne hi21,
    Function.update_of_ne hi15]

end SlotEval9

/-! ### Slot updates -/

section SlotUpd9

variable {N : ℕ} (h15 : 15 < N) (h21 : 21 < N) (h27 : 27 < N) (h34 : 34 < N)
  (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N) (h64 : 64 < N) (h72 : 72 < N)
  (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ b : Bool)

theorem nineUpd_upd1 :
    Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉) ⟨15, h15⟩ b
      = nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 b s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ := by
  show Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (zBase3 N) ⟨15, h15⟩ s₁) ⟨21, h21⟩ s₂)
    ⟨27, h27⟩ s₃) ⟨34, h34⟩ s₄) ⟨41, h41⟩ s₅) ⟨48, h48⟩ s₆) ⟨56, h56⟩ s₇)
    ⟨64, h64⟩ s₈) ⟨72, h72⟩ s₉) ⟨15, h15⟩ b = _
  rw [Function.update_comm (fne h72 h15 (by omega)),
    Function.update_comm (fne h64 h15 (by omega)),
    Function.update_comm (fne h56 h15 (by omega)),
    Function.update_comm (fne h48 h15 (by omega)),
    Function.update_comm (fne h41 h15 (by omega)),
    Function.update_comm (fne h34 h15 (by omega)),
    Function.update_comm (fne h27 h15 (by omega)),
    Function.update_comm (fne h21 h15 (by omega)), Function.update_idem]
  rfl

theorem nineUpd_upd2 :
    Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉) ⟨21, h21⟩ b
      = nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ b s₃ s₄ s₅ s₆ s₇ s₈ s₉ := by
  show Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (zBase3 N) ⟨15, h15⟩ s₁) ⟨21, h21⟩ s₂)
    ⟨27, h27⟩ s₃) ⟨34, h34⟩ s₄) ⟨41, h41⟩ s₅) ⟨48, h48⟩ s₆) ⟨56, h56⟩ s₇)
    ⟨64, h64⟩ s₈) ⟨72, h72⟩ s₉) ⟨21, h21⟩ b = _
  rw [Function.update_comm (fne h72 h21 (by omega)),
    Function.update_comm (fne h64 h21 (by omega)),
    Function.update_comm (fne h56 h21 (by omega)),
    Function.update_comm (fne h48 h21 (by omega)),
    Function.update_comm (fne h41 h21 (by omega)),
    Function.update_comm (fne h34 h21 (by omega)),
    Function.update_comm (fne h27 h21 (by omega)), Function.update_idem]
  rfl

theorem nineUpd_upd3 :
    Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉) ⟨27, h27⟩ b
      = nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ b s₄ s₅ s₆ s₇ s₈ s₉ := by
  show Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (zBase3 N) ⟨15, h15⟩ s₁) ⟨21, h21⟩ s₂)
    ⟨27, h27⟩ s₃) ⟨34, h34⟩ s₄) ⟨41, h41⟩ s₅) ⟨48, h48⟩ s₆) ⟨56, h56⟩ s₇)
    ⟨64, h64⟩ s₈) ⟨72, h72⟩ s₉) ⟨27, h27⟩ b = _
  rw [Function.update_comm (fne h72 h27 (by omega)),
    Function.update_comm (fne h64 h27 (by omega)),
    Function.update_comm (fne h56 h27 (by omega)),
    Function.update_comm (fne h48 h27 (by omega)),
    Function.update_comm (fne h41 h27 (by omega)),
    Function.update_comm (fne h34 h27 (by omega)), Function.update_idem]
  rfl

theorem nineUpd_upd4 :
    Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉) ⟨34, h34⟩ b
      = nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ s₃ b s₅ s₆ s₇ s₈ s₉ := by
  show Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (zBase3 N) ⟨15, h15⟩ s₁) ⟨21, h21⟩ s₂)
    ⟨27, h27⟩ s₃) ⟨34, h34⟩ s₄) ⟨41, h41⟩ s₅) ⟨48, h48⟩ s₆) ⟨56, h56⟩ s₇)
    ⟨64, h64⟩ s₈) ⟨72, h72⟩ s₉) ⟨34, h34⟩ b = _
  rw [Function.update_comm (fne h72 h34 (by omega)),
    Function.update_comm (fne h64 h34 (by omega)),
    Function.update_comm (fne h56 h34 (by omega)),
    Function.update_comm (fne h48 h34 (by omega)),
    Function.update_comm (fne h41 h34 (by omega)), Function.update_idem]
  rfl

theorem nineUpd_upd5 :
    Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉) ⟨41, h41⟩ b
      = nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ s₃ s₄ b s₆ s₇ s₈ s₉ := by
  show Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (zBase3 N) ⟨15, h15⟩ s₁) ⟨21, h21⟩ s₂)
    ⟨27, h27⟩ s₃) ⟨34, h34⟩ s₄) ⟨41, h41⟩ s₅) ⟨48, h48⟩ s₆) ⟨56, h56⟩ s₇)
    ⟨64, h64⟩ s₈) ⟨72, h72⟩ s₉) ⟨41, h41⟩ b = _
  rw [Function.update_comm (fne h72 h41 (by omega)),
    Function.update_comm (fne h64 h41 (by omega)),
    Function.update_comm (fne h56 h41 (by omega)),
    Function.update_comm (fne h48 h41 (by omega)), Function.update_idem]
  rfl

theorem nineUpd_upd6 :
    Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉) ⟨48, h48⟩ b
      = nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ s₃ s₄ s₅ b s₇ s₈ s₉ := by
  show Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (zBase3 N) ⟨15, h15⟩ s₁) ⟨21, h21⟩ s₂)
    ⟨27, h27⟩ s₃) ⟨34, h34⟩ s₄) ⟨41, h41⟩ s₅) ⟨48, h48⟩ s₆) ⟨56, h56⟩ s₇)
    ⟨64, h64⟩ s₈) ⟨72, h72⟩ s₉) ⟨48, h48⟩ b = _
  rw [Function.update_comm (fne h72 h48 (by omega)),
    Function.update_comm (fne h64 h48 (by omega)),
    Function.update_comm (fne h56 h48 (by omega)), Function.update_idem]
  rfl

theorem nineUpd_upd7 :
    Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉) ⟨56, h56⟩ b
      = nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ s₃ s₄ s₅ s₆ b s₈ s₉ := by
  show Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (zBase3 N) ⟨15, h15⟩ s₁) ⟨21, h21⟩ s₂)
    ⟨27, h27⟩ s₃) ⟨34, h34⟩ s₄) ⟨41, h41⟩ s₅) ⟨48, h48⟩ s₆) ⟨56, h56⟩ s₇)
    ⟨64, h64⟩ s₈) ⟨72, h72⟩ s₉) ⟨56, h56⟩ b = _
  rw [Function.update_comm (fne h72 h56 (by omega)),
    Function.update_comm (fne h64 h56 (by omega)), Function.update_idem]
  rfl

theorem nineUpd_upd8 :
    Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉) ⟨64, h64⟩ b
      = nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ s₃ s₄ s₅ s₆ s₇ b s₉ := by
  show Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (zBase3 N) ⟨15, h15⟩ s₁) ⟨21, h21⟩ s₂)
    ⟨27, h27⟩ s₃) ⟨34, h34⟩ s₄) ⟨41, h41⟩ s₅) ⟨48, h48⟩ s₆) ⟨56, h56⟩ s₇)
    ⟨64, h64⟩ s₈) ⟨72, h72⟩ s₉) ⟨64, h64⟩ b = _
  rw [Function.update_comm (fne h72 h64 (by omega)), Function.update_idem]
  rfl

theorem nineUpd_upd9 :
    Function.update (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉) ⟨72, h72⟩ b
      = nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ b := by
  show Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (zBase3 N) ⟨15, h15⟩ s₁) ⟨21, h21⟩ s₂)
    ⟨27, h27⟩ s₃) ⟨34, h34⟩ s₄) ⟨41, h41⟩ s₅) ⟨48, h48⟩ s₆) ⟨56, h56⟩ s₇)
    ⟨64, h64⟩ s₈) ⟨72, h72⟩ s₉) ⟨72, h72⟩ b = _
  rw [Function.update_idem]
  rfl

end SlotUpd9

/-! ### The nine sign dependencies -/

section SignDeps9

variable (N : ℕ) (hN : 73 ≤ N) (h15 : 15 < N) (h21 : 21 < N) (h27 : 27 < N)
  (h34 : 34 < N) (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N) (h64 : 64 < N)
  (h72 : 72 < N)

include hN h15 h21 h27 h34 h41 h48 h56 h64 h72

theorem sign15_dep9 : (⟨15, h15⟩ : Fin N) ∈ depSet (SATFamily N) := by
  rw [mem_depSet]
  refine ⟨nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
    true true true true true true true true true, false, ?_⟩
  rw [nineUpd_upd1,
    SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
      false true true true true true true true true,
    SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true true true true]
  decide

theorem sign21_dep9 : (⟨21, h21⟩ : Fin N) ∈ depSet (SATFamily N) := by
  rw [mem_depSet]
  refine ⟨nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
    true true true true true true true true true, false, ?_⟩
  rw [nineUpd_upd2,
    SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
      true false true true true true true true true,
    SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true true true true]
  decide

theorem sign27_dep9 : (⟨27, h27⟩ : Fin N) ∈ depSet (SATFamily N) := by
  rw [mem_depSet]
  refine ⟨nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
    true true true true true true true true true, false, ?_⟩
  rw [nineUpd_upd3,
    SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true false true true true true true true,
    SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true true true true]
  decide

theorem sign34_dep9 : (⟨34, h34⟩ : Fin N) ∈ depSet (SATFamily N) := by
  rw [mem_depSet]
  refine ⟨nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
    true true true true true true true true true, false, ?_⟩
  rw [nineUpd_upd4,
    SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true false true true true true true,
    SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true true true true]
  decide

theorem sign41_dep9 : (⟨41, h41⟩ : Fin N) ∈ depSet (SATFamily N) := by
  rw [mem_depSet]
  refine ⟨nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
    true true true true true true true true true, false, ?_⟩
  rw [nineUpd_upd5,
    SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true false true true true true,
    SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true true true true]
  decide

theorem sign48_dep9 : (⟨48, h48⟩ : Fin N) ∈ depSet (SATFamily N) := by
  rw [mem_depSet]
  refine ⟨nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
    true true true true true true true true true, false, ?_⟩
  rw [nineUpd_upd6,
    SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true false true true true,
    SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true true true true]
  decide

theorem sign56_dep9 : (⟨56, h56⟩ : Fin N) ∈ depSet (SATFamily N) := by
  rw [mem_depSet]
  refine ⟨nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
    true true true true true true true true true, false, ?_⟩
  rw [nineUpd_upd7,
    SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true false true true,
    SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true true true true]
  decide

theorem sign64_dep9 : (⟨64, h64⟩ : Fin N) ∈ depSet (SATFamily N) := by
  rw [mem_depSet]
  refine ⟨nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
    true true true true true true true true true, false, ?_⟩
  rw [nineUpd_upd8,
    SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true true false true,
    SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true true true true]
  decide

theorem sign72_dep9 : (⟨72, h72⟩ : Fin N) ∈ depSet (SATFamily N) := by
  rw [mem_depSet]
  refine ⟨nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
    true true true true true true true true true, false, ?_⟩
  rw [nineUpd_upd9,
    SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true true true false,
    SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true true true true]
  decide

end SignDeps9

/-! ### THE MASTER REFINEMENT (nine slots, single reconvergence wire) -/

/-- **The nine-slot master refinement (proved)**. -/
theorem refine_nineUpd (N : ℕ) (h15 : 15 < N) (h21 : 21 < N) (h27 : 27 < N)
    (h34 : 34 < N) (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N) (h64 : 64 < N)
    (h72 : 72 < N)
    (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    {u : ℕ} (hR : reconvR c = {u})
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ : Bool)
    (hb1 : s₁ = t₁ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨15, h15⟩ : Fin N) → Reach c u q)
    (hb2 : s₂ = t₂ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨21, h21⟩ : Fin N) → Reach c u q)
    (hb3 : s₃ = t₃ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨27, h27⟩ : Fin N) → Reach c u q)
    (hb4 : s₄ = t₄ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨34, h34⟩ : Fin N) → Reach c u q)
    (hb5 : s₅ = t₅ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨41, h41⟩ : Fin N) → Reach c u q)
    (hb6 : s₆ = t₆ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨48, h48⟩ : Fin N) → Reach c u q)
    (hb7 : s₇ = t₇ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨56, h56⟩ : Fin N) → Reach c u q)
    (hb8 : s₈ = t₈ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨64, h64⟩ : Fin N) → Reach c u q)
    (hb9 : s₉ = t₉ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨72, h72⟩ : Fin N) → Reach c u q)
    (hwu : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉) u
      = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉) u) :
    SATFamily N (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉)
      = SATFamily N (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉) := by
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_singleton_self u
  obtain ⟨hune, huc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp humem).1
  have hult : u < c.length := (mem_cone.mp huc).1
  have hroot_nb : ¬ Reach c u (c.length - 1) := by
    intro hr
    have h1 := reach_le hr
    exact hune (by omega)
  have hagree : ∀ i : Fin N,
      (∃ q, q ∈ cone c ∧ c.getD q (.cst false) = CGate.var i ∧ ¬ Reach c u q) →
      nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ i
        = nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ i := by
    intro i hex
    obtain ⟨q, hqc, hqg, hqnb⟩ := hex
    by_cases e1 : i = ⟨15, h15⟩
    · subst e1
      rw [nineUpd_at15, nineUpd_at15]
      rcases hb1 with he | hall
      · exact he
      · exact absurd (hall q hqc hqg) hqnb
    by_cases e2 : i = ⟨21, h21⟩
    · subst e2
      rw [nineUpd_at21, nineUpd_at21]
      rcases hb2 with he | hall
      · exact he
      · exact absurd (hall q hqc hqg) hqnb
    by_cases e3 : i = ⟨27, h27⟩
    · subst e3
      rw [nineUpd_at27, nineUpd_at27]
      rcases hb3 with he | hall
      · exact he
      · exact absurd (hall q hqc hqg) hqnb
    by_cases e4 : i = ⟨34, h34⟩
    · subst e4
      rw [nineUpd_at34, nineUpd_at34]
      rcases hb4 with he | hall
      · exact he
      · exact absurd (hall q hqc hqg) hqnb
    by_cases e5 : i = ⟨41, h41⟩
    · subst e5
      rw [nineUpd_at41, nineUpd_at41]
      rcases hb5 with he | hall
      · exact he
      · exact absurd (hall q hqc hqg) hqnb
    by_cases e6 : i = ⟨48, h48⟩
    · subst e6
      rw [nineUpd_at48, nineUpd_at48]
      rcases hb6 with he | hall
      · exact he
      · exact absurd (hall q hqc hqg) hqnb
    by_cases e7 : i = ⟨56, h56⟩
    · subst e7
      rw [nineUpd_at56, nineUpd_at56]
      rcases hb7 with he | hall
      · exact he
      · exact absurd (hall q hqc hqg) hqnb
    by_cases e8 : i = ⟨64, h64⟩
    · subst e8
      rw [nineUpd_at64, nineUpd_at64]
      rcases hb8 with he | hall
      · exact he
      · exact absurd (hall q hqc hqg) hqnb
    by_cases e9 : i = ⟨72, h72⟩
    · subst e9
      rw [nineUpd_at72, nineUpd_at72]
      rcases hb9 with he | hall
      · exact he
      · exact absurd (hall q hqc hqg) hqnb
    rw [nineUpd_at_other h15 h21 h27 h34 h41 h48 h56 h64 h72 _ _ _ _ _ _ _ _ _
        i e1 e2 e3 e4 e5 e6 e7 e8 e9,
      nineUpd_at_other h15 h21 h27 h34 h41 h48 h56 h64 h72 _ _ _ _ _ _ _ _ _
        i e1 e2 e3 e4 e5 e6 e7 e8 e9]
  have hcut := cut_agree c u hs hR ((mem_cone.mp huc).2)
    (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉)
    (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉)
    hwu hagree (c.length - 1) (mem_cone.mpr ⟨by omega, InCone.root⟩) hroot_nb
  rw [← hcomp (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉),
    ← hcomp (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉),
    output_eq_wire, output_eq_wire]
  exact hcut

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.word_nineUpd
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.SATFamily_nineUpd
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.refine_nineUpd
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sign72_dep9
