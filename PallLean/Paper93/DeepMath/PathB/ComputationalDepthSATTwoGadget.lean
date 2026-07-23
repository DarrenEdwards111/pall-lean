import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATAboveFloor
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthROTCountSplit

/-!
# Two disjoint gadgets in the codec: the `+2` substrate and the tree-excess `≥ 8`

Brick 1 of the `+2`-above-floor campaign on `SATFamily`.  The two-gadget formula
`(x₀^{s₁})∧(x₀^{s₂})∧(x₀^{s₃})∧(x₁^{u₁})∧(x₁^{u₂})∧(x₁^{u₃})` embeds TWO disjoint
`AllEqual₃` gadgets in one 46-bit codec word (signs at `12,18,24` and `31,38,45`):

* **`SATLang_se2_append` (proved)** — padding-transparent satisfiability:
  `AllEqual₃(s) && AllEqual₃(u)` (the codec realizes `AEm 2`);
* **`word2_g0` / `word2_g1` (proved)** — per-gadget triple-update word identities
  at every length `N ≥ 46`, the other gadget held satisfied;
* **`triple_allEq3_cnt` (proved, general)** — any read-once-with-multiplicity tree
  whose triple-restriction is `AllEqual₃` carries total leaf-count `≥ 4` on the
  triple (each variable occurs, and `1/1/1` would split — `rot_split_cnt`);
* **`SATFamily2_leaf_excess` (proved)** — hence any `ROT` computing a SAT slice of
  length `≥ 46` has total count `≥ 8` on the six sign coordinates: **each gadget
  independently forces `+1` excess over read-once — `+2` in the tree measure.**

## Honest scope

The `+2` here is in the TREE (leaf-count) measure, per-gadget and disjoint — the
certificate the DAG campaign needs, not yet the DAG bound.  Lifting `+2` to
`cbudget` requires the floor+1 extraction and the one-spare-unit collision
analysis (the AEm campaign's kill-chain, re-instantiated on the codec) — that is
the open remainder, recorded, not claimed.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.SATFamilyDenseFloor

/-! ### The two-gadget formula and its encoding -/

/-- The two-gadget formula: three signed unit clauses on `x₀`, three on `x₁`. -/
def se2 (s₁ s₂ s₃ u₁ u₂ u₃ : Bool) : Formula :=
  [[((0 : ℕ), s₁)], [((0 : ℕ), s₂)], [((0 : ℕ), s₃)],
   [((1 : ℕ), u₁)], [((1 : ℕ), u₂)], [((1 : ℕ), u₃)]]

theorem encodeVar'_one : encodeVar' 1 = [false, false, true, false] := by
  have h := encodeVar'_coords 0 0 1 (by omega)
  rw [show 3 * Nat.pair 0 0 + 1 = 1 from rfl] at h
  rw [h]
  rfl

theorem se2_concrete (a b c d e f : Bool) : encodeFormula' (se2 a b c d e f)
    = [true, true, true, true, true, true, false,
       true, false, false, false, false, a,
       true, false, false, false, false, b,
       true, false, false, false, false, c,
       true, false, false, false, true, false, d,
       true, false, false, false, true, false, e,
       true, false, false, false, true, false, f] := by
  show encodeNat 6 ++ (List.map encodeClause' (se2 a b c d e f)).flatten = _
  simp only [se2, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    encodeClause', encodeLit', List.append_nil, encodeVar'_zero, encodeVar'_one]
  rfl

/-- Variable-general unit-clause conflict. -/
theorem unsat_of_conflict_at (v : ℕ) (φ : Formula) (h1 : [(v, true)] ∈ φ)
    (h0 : [(v, false)] ∈ φ) : ¬ Satisfiable φ := by
  rintro ⟨a, ha⟩
  rw [evalFormula, List.all_eq_true] at ha
  have ht := ha _ h1
  have hf := ha _ h0
  simp only [evalClause, List.any_cons, List.any_nil, evalLit, Bool.or_false,
    beq_iff_eq] at ht hf
  rw [ht] at hf
  simp at hf

/-- **Padding-transparent two-gadget satisfiability (proved)**: the codec realizes
`AEm 2` — agreement per gadget, independently. -/
theorem SATLang_se2_append (t₁ t₂ t₃ u₁ u₂ u₃ : Bool) (rest : List Bool) :
    SATLang (encodeFormula' (se2 t₁ t₂ t₃ u₁ u₂ u₃) ++ rest)
      = (allEq3 t₁ t₂ t₃ && allEq3 u₁ u₂ u₃) := by
  cases t₁ <;> cases t₂ <;> cases t₃ <;> cases u₁ <;> cases u₂ <;> cases u₃ <;>
    first
      | (rw [SATLang_append_sat _ _
          ⟨fun n => if n = 0 then false else false, by decide⟩]; rfl)
      | (rw [SATLang_append_sat _ _
          ⟨fun n => if n = 0 then false else true, by decide⟩]; rfl)
      | (rw [SATLang_append_sat _ _
          ⟨fun n => if n = 0 then true else false, by decide⟩]; rfl)
      | (rw [SATLang_append_sat _ _
          ⟨fun n => if n = 0 then true else true, by decide⟩]; rfl)
      | (rw [SATLang_append_unsat _ _
          (unsat_of_conflict_at 0 _ (by decide) (by decide))]; rfl)
      | (rw [SATLang_append_unsat _ _
          (unsat_of_conflict_at 1 _ (by decide) (by decide))]; rfl)

/-! ### The padded base completion and the per-gadget word identities -/

/-- The all-true-signs two-gadget word. -/
def sBase2 : List Bool :=
  [true, true, true, true, true, true, false,
   true, false, false, false, false, true,
   true, false, false, false, false, true,
   true, false, false, false, false, true,
   true, false, false, false, true, false, true,
   true, false, false, false, true, false, true,
   true, false, false, false, true, false, true]

/-- The padded two-gadget base completion. -/
def zBase2 (N : ℕ) : Fin N → Bool := fun k => sBase2.getD k.val false

/-- **Gadget-0 word identity (proved)**: updating the three `x₀`-signs, gadget 1
held satisfied. -/
theorem word2_g0 (N : ℕ) (hN : 46 ≤ N) (h12 : 12 < N) (h18 : 18 < N) (h24 : 24 < N)
    (a b c : Bool) :
    wordOfFin (Function.update (Function.update (Function.update (zBase2 N)
        ⟨12, h12⟩ a) ⟨18, h18⟩ b) ⟨24, h24⟩ c)
      = encodeFormula' (se2 a b c true true true) ++ List.replicate (N - 46) false := by
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
      have hne24 : (⟨k, hkN⟩ : Fin N) ≠ ⟨24, h24⟩ := by
        intro he; rw [Fin.mk.injEq] at he; omega
      have hne18 : (⟨k, hkN⟩ : Fin N) ≠ ⟨18, h18⟩ := by
        intro he; rw [Fin.mk.injEq] at he; omega
      have hne12 : (⟨k, hkN⟩ : Fin N) ≠ ⟨12, h12⟩ := by
        intro he; rw [Fin.mk.injEq] at he; omega
      rw [Function.update_of_ne hne24, Function.update_of_ne hne18,
        Function.update_of_ne hne12]
      have hzb : zBase2 N ⟨k, hkN⟩ = false := by
        show sBase2.getD k false = false
        have hlen : sBase2.length ≤ k := by
          simp only [sBase2, List.length_cons, List.length_nil]
          omega
        rw [List.getD_eq_default _ _ hlen]
      rw [hzb]
      have hlen46 : ([true, true, true, true, true, true, false,
          true, false, false, false, false, a,
          true, false, false, false, false, b,
          true, false, false, false, false, c,
          true, false, false, false, true, false, true,
          true, false, false, false, true, false, true,
          true, false, false, false, true, false, true] : List Bool).length ≤ k := by
        simp only [List.length_cons, List.length_nil]
        omega
      rw [List.getElem_append_right hlen46]
      rw [List.getElem_replicate]

/-- **Gadget-1 word identity (proved)**: updating the three `x₁`-signs, gadget 0
held satisfied. -/
theorem word2_g1 (N : ℕ) (hN : 46 ≤ N) (h31 : 31 < N) (h38 : 38 < N) (h45 : 45 < N)
    (d e f : Bool) :
    wordOfFin (Function.update (Function.update (Function.update (zBase2 N)
        ⟨31, h31⟩ d) ⟨38, h38⟩ e) ⟨45, h45⟩ f)
      = encodeFormula' (se2 true true true d e f) ++ List.replicate (N - 46) false := by
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
      have hne45 : (⟨k, hkN⟩ : Fin N) ≠ ⟨45, h45⟩ := by
        intro he; rw [Fin.mk.injEq] at he; omega
      have hne38 : (⟨k, hkN⟩ : Fin N) ≠ ⟨38, h38⟩ := by
        intro he; rw [Fin.mk.injEq] at he; omega
      have hne31 : (⟨k, hkN⟩ : Fin N) ≠ ⟨31, h31⟩ := by
        intro he; rw [Fin.mk.injEq] at he; omega
      rw [Function.update_of_ne hne45, Function.update_of_ne hne38,
        Function.update_of_ne hne31]
      have hzb : zBase2 N ⟨k, hkN⟩ = false := by
        show sBase2.getD k false = false
        have hlen : sBase2.length ≤ k := by
          simp only [sBase2, List.length_cons, List.length_nil]
          omega
        rw [List.getD_eq_default _ _ hlen]
      rw [hzb]
      have hlen46 : ([true, true, true, true, true, true, false,
          true, false, false, false, false, true,
          true, false, false, false, false, true,
          true, false, false, false, false, true,
          true, false, false, false, true, false, d,
          true, false, false, false, true, false, e,
          true, false, false, false, true, false, f] : List Bool).length ≤ k := by
        simp only [List.length_cons, List.length_nil]
        omega
      rw [List.getElem_append_right hlen46]
      rw [List.getElem_replicate]

/-! ### The general count bound and the two-gadget tree excess -/

/-- **The per-triple count bound (proved, general)**: any `ROT` whose
triple-restriction is `AllEqual₃` carries total count `≥ 4` on the triple —
each variable occurs (blindness would contradict dependence), and `1/1/1` would
split (`rot_split_cnt` vs `allEq3_no_split`). -/
theorem triple_allEq3_cnt {n : ℕ} (t : ROT n) (i₁ i₂ i₃ : Fin n)
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃) (z : Fin n → Bool)
    (heq : (fun a b c => t.eval (Function.update (Function.update
      (Function.update z i₁ a) i₂ b) i₃ c)) = allEq3) :
    4 ≤ t.cnt i₁ + t.cnt i₂ + t.cnt i₃ := by
  have hF : ∀ a b c, t.eval (Function.update (Function.update
      (Function.update z i₁ a) i₂ b) i₃ c) = allEq3 a b c :=
    fun a b c => congrFun (congrFun (congrFun heq a) b) c
  have hc1 : 1 ≤ t.cnt i₁ := by
    by_contra h
    push_neg at h
    have hnl := cnt_zero_not_leaf t i₁ (by omega)
    have hcomm : ∀ v : Bool, Function.update (Function.update
        (Function.update z i₁ v) i₂ true) i₃ true
        = Function.update (Function.update
          (Function.update z i₂ true) i₃ true) i₁ v := by
      intro v
      rw [Function.update_comm h12, Function.update_comm h13]
    have e1 : t.eval (Function.update (Function.update
        (Function.update z i₁ true) i₂ true) i₃ true)
        = t.eval (Function.update (Function.update
          (Function.update z i₁ false) i₂ true) i₃ true) := by
      rw [hcomm true, hcomm false, ROT.eval_update_of_not_leaf t i₁ hnl,
        ROT.eval_update_of_not_leaf t i₁ hnl]
    rw [hF, hF] at e1
    exact absurd e1 (by decide)
  have hc2 : 1 ≤ t.cnt i₂ := by
    by_contra h
    push_neg at h
    have hnl := cnt_zero_not_leaf t i₂ (by omega)
    have hcomm : ∀ v : Bool, Function.update (Function.update
        (Function.update z i₁ true) i₂ v) i₃ true
        = Function.update (Function.update
          (Function.update z i₁ true) i₃ true) i₂ v := by
      intro v
      rw [Function.update_comm h23]
    have e1 : t.eval (Function.update (Function.update
        (Function.update z i₁ true) i₂ true) i₃ true)
        = t.eval (Function.update (Function.update
          (Function.update z i₁ true) i₂ false) i₃ true) := by
      rw [hcomm true, hcomm false, ROT.eval_update_of_not_leaf t i₂ hnl,
        ROT.eval_update_of_not_leaf t i₂ hnl]
    rw [hF, hF] at e1
    exact absurd e1 (by decide)
  have hc3 : 1 ≤ t.cnt i₃ := by
    by_contra h
    push_neg at h
    have hnl := cnt_zero_not_leaf t i₃ (by omega)
    have e1 : t.eval (Function.update (Function.update
        (Function.update z i₁ true) i₂ true) i₃ true)
        = t.eval (Function.update (Function.update
          (Function.update z i₁ true) i₂ true) i₃ false) := by
      rw [ROT.eval_update_of_not_leaf t i₃ hnl, ROT.eval_update_of_not_leaf t i₃ hnl]
    rw [hF, hF] at e1
    exact absurd e1 (by decide)
  have hnot : ¬ (t.cnt i₁ = 1 ∧ t.cnt i₂ = 1 ∧ t.cnt i₃ = 1) := by
    rintro ⟨e1, e2, e3⟩
    have hsp := rot_split_cnt t i₁ i₂ i₃ h12 h13 h23 z e1 e2 e3
    rw [heq] at hsp
    rcases hsp with h | h | h
    · exact allEq3_no_split_a h
    · exact allEq3_no_split_b h
    · exact allEq3_no_split_c h
  omega

/-- **THE TWO-GADGET TREE EXCESS (proved)**: any read-once-with-multiplicity tree
computing a SAT slice of length `≥ 46` carries total count `≥ 8` on the six sign
coordinates — each embedded gadget independently forces `+1` over read-once. -/
theorem SATFamily2_leaf_excess (N : ℕ) (hN : 46 ≤ N) (t : ROT N)
    (hev : t.eval = SATFamily N) :
    8 ≤ t.cnt ⟨12, by omega⟩ + t.cnt ⟨18, by omega⟩ + t.cnt ⟨24, by omega⟩
      + t.cnt ⟨31, by omega⟩ + t.cnt ⟨38, by omega⟩ + t.cnt ⟨45, by omega⟩ := by
  have h12 : (12 : ℕ) < N := by omega
  have h18 : (18 : ℕ) < N := by omega
  have h24 : (24 : ℕ) < N := by omega
  have h31 : (31 : ℕ) < N := by omega
  have h38 : (38 : ℕ) < N := by omega
  have h45 : (45 : ℕ) < N := by omega
  have hg0 : (fun a b c => t.eval (Function.update (Function.update
      (Function.update (zBase2 N) ⟨12, h12⟩ a) ⟨18, h18⟩ b) ⟨24, h24⟩ c))
      = allEq3 := by
    funext a b c
    rw [hev]
    show SATFamily N _ = allEq3 a b c
    rw [SATFamily_apply, word2_g0 N hN h12 h18 h24 a b c, SATLang_se2_append]
    rw [show allEq3 true true true = true from rfl, Bool.and_true]
  have hg1 : (fun d e f => t.eval (Function.update (Function.update
      (Function.update (zBase2 N) ⟨31, h31⟩ d) ⟨38, h38⟩ e) ⟨45, h45⟩ f))
      = allEq3 := by
    funext d e f
    rw [hev]
    show SATFamily N _ = allEq3 d e f
    rw [SATFamily_apply, word2_g1 N hN h31 h38 h45 d e f, SATLang_se2_append]
    rw [show allEq3 true true true = true from rfl, Bool.true_and]
  have hA := triple_allEq3_cnt t ⟨12, h12⟩ ⟨18, h18⟩ ⟨24, h24⟩
    (by intro he; rw [Fin.mk.injEq] at he; omega)
    (by intro he; rw [Fin.mk.injEq] at he; omega)
    (by intro he; rw [Fin.mk.injEq] at he; omega) (zBase2 N) hg0
  have hB := triple_allEq3_cnt t ⟨31, h31⟩ ⟨38, h38⟩ ⟨45, h45⟩
    (by intro he; rw [Fin.mk.injEq] at he; omega)
    (by intro he; rw [Fin.mk.injEq] at he; omega)
    (by intro he; rw [Fin.mk.injEq] at he; omega) (zBase2 N) hg1
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.SATLang_se2_append
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.triple_allEq3_cnt
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.SATFamily2_leaf_excess
