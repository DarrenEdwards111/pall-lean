import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CircuitReprP
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung4CircuitReal

/-!
# Bridge (model translation) — `ACC0Circuit → BoolCircuitSyntax`, eval-preserving (proved)

A faithful translation from this development's `ACC0Circuit` model (`…ACC0CircuitModel`) to the tree's `BoolCircuitSyntax`
model (`…Rung4CircuitReal`, the model of the `Layer3/Layer4` Razborov–Smolensky bounds): binary `and`/`or` become two-element
`andGate`/`orGate` lists, and a `mod p S t` gate becomes a `modGate p t.val` over the input list of its support `S`.  On
`AC⁰[p]` (`ModpOnly`) circuits the translation preserves the Boolean output (`toBoolSyntax_eval`) and the `IsAC0pSyntax`
predicate (`toBoolSyntax_isAC0p`).

This is the genuine **model-bridge artifact** connecting the two circuit formalizations in the repo.

## Honest scope (IMPORTANT)

This is *only* the eval/AC0p-preserving model translation (for `ModpOnly` circuits, `p ≠ 0`).  It does **NOT** by itself
discharge any `MOD_q` lower bound: `Layer4.mod_q_indicators_false` is a *joint* statement about all `q` residue indicators
with a *subcircuit-count (size)* bound, whereas this development proves single-`MOD_q` *degree* bounds.  Using Layer4 to
obtain unconditional `MOD_q ∉ AC⁰[p]` would additionally require a residue-family construction and a size bound — a separate
major step, **not** done here and **not** faked.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ToBoolSyntax

open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP (ModpOnly)
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation (weightOn modQStatOn)

variable {n : ℕ}

/-- Translate an `ACC0Circuit` into a `BoolCircuitSyntax`. -/
noncomputable def toBoolSyntax : ACC0Circuit n → BoolCircuitSyntax n
  | .const b => .const b
  | .var i => .input i
  | .not c => .not (toBoolSyntax c)
  | .and a b => .andGate [toBoolSyntax a, toBoolSyntax b]
  | .or a b => .orGate [toBoolSyntax a, toBoolSyntax b]
  | .mod q S t => .modGate q t.val (S.toList.map (fun i => .input i))

/-- The count of accepting input-subcircuits of the support `S` is the Hamming weight over `S`. -/
theorem count_support_eq_weight (S : Finset (Fin n)) (x : Fin n → Bool) :
    (((S.toList.map (fun i => (BoolCircuitSyntax.input i : BoolCircuitSyntax n))).map
        (fun C => BoolCircuitSyntax.eval C x)).filter id).length = weightOn S x := by
  rw [List.map_map]
  simp only [Function.comp_def, BoolCircuitSyntax.eval]
  rw [weightOn, ← Finset.sum_map_toList S (fun i => if x i then 1 else 0)]
  generalize S.toList = l
  induction l with
  | nil => simp
  | cons a t ih =>
      cases h : x a
      · simp [h, ih]
      · simp [h, ih]; omega

/-- **The translation preserves the Boolean output on `AC⁰[p]` circuits (PROVED).** -/
theorem toBoolSyntax_eval (p : ℕ) [NeZero p] (C : ACC0Circuit n) (x : Fin n → Bool) :
    ModpOnly p C → BoolCircuitSyntax.eval (toBoolSyntax C) x = ACC0CircuitModel.eval C x := by
  induction C with
  | const b => intro _; simp [toBoolSyntax, BoolCircuitSyntax.eval, ACC0CircuitModel.eval]
  | var i => intro _; simp [toBoolSyntax, BoolCircuitSyntax.eval, ACC0CircuitModel.eval]
  | not c ih =>
      intro h; simp only [ModpOnly] at h
      simp only [toBoolSyntax, BoolCircuitSyntax.eval, ACC0CircuitModel.eval]; rw [ih h]
  | and a b iha ihb =>
      intro h; simp only [ModpOnly] at h
      simp only [toBoolSyntax, BoolCircuitSyntax.eval, ACC0CircuitModel.eval, List.map_cons,
        List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
      rw [iha h.1, ihb h.2]
  | or a b iha ihb =>
      intro h; simp only [ModpOnly] at h
      simp only [toBoolSyntax, BoolCircuitSyntax.eval, ACC0CircuitModel.eval, List.map_cons,
        List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]
      rw [iha h.1, ihb h.2]
  | mod q S t =>
      intro h; simp only [ModpOnly] at h; subst q
      simp only [toBoolSyntax, BoolCircuitSyntax.eval, ACC0CircuitModel.eval, modQStatOn]
      rw [count_support_eq_weight S x]
      have key : ((weightOn S x : ZMod p) = t) ↔ weightOn S x ≡ t.val [MOD p] := by
        conv_lhs => rw [show t = ((t.val : ℕ) : ZMod p) from (ZMod.natCast_zmod_val t).symm]
        exact ZMod.natCast_eq_natCast_iff _ _ _
      exact decide_eq_decide.mpr key.symm

/-- **The translation preserves `IsAC0pSyntax` on `AC⁰[p]` circuits (PROVED).** -/
theorem toBoolSyntax_isAC0p (p : ℕ) (C : ACC0Circuit n) :
    ModpOnly p C → BoolCircuitSyntax.IsAC0pSyntax p (toBoolSyntax C) := by
  induction C with
  | const b => intro _; simp [toBoolSyntax, BoolCircuitSyntax.IsAC0pSyntax]
  | var i => intro _; simp [toBoolSyntax, BoolCircuitSyntax.IsAC0pSyntax]
  | not c ih =>
      intro h; simp only [ModpOnly] at h
      simp only [toBoolSyntax, BoolCircuitSyntax.IsAC0pSyntax]; exact ih h
  | and a b iha ihb =>
      intro h; simp only [ModpOnly] at h
      simp only [toBoolSyntax, BoolCircuitSyntax.IsAC0pSyntax]
      intro C hC
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      rcases hC with hC | hC <;> subst hC
      · exact iha h.1
      · exact ihb h.2
  | or a b iha ihb =>
      intro h; simp only [ModpOnly] at h
      simp only [toBoolSyntax, BoolCircuitSyntax.IsAC0pSyntax]
      intro C hC
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      rcases hC with hC | hC <;> subst hC
      · exact iha h.1
      · exact ihb h.2
  | mod q S t =>
      intro h; simp only [ModpOnly] at h
      simp only [toBoolSyntax, BoolCircuitSyntax.IsAC0pSyntax]
      refine ⟨h, fun C hC => ?_⟩
      simp only [List.mem_map] at hC
      obtain ⟨i, _, rfl⟩ := hC
      simp [BoolCircuitSyntax.IsAC0pSyntax]

/-!
**The model translation, proved.**  `ACC0Circuit → BoolCircuitSyntax` is eval-preserving (`toBoolSyntax_eval`) and AC0p-
preserving (`toBoolSyntax_isAC0p`) on `AC⁰[p]` circuits — a faithful bridge between the two circuit formalizations.  It does
**not** discharge any `MOD_q` bound (Layer4 needs the residue family + size bound, not done/faked here).  Not `NEXP ⊄ ACC⁰`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ToBoolSyntax

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ToBoolSyntax.toBoolSyntax_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ToBoolSyntax.toBoolSyntax_isAC0p
