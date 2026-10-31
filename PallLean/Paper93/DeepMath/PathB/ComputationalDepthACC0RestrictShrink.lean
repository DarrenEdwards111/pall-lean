import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DedupShrink

/-!
# Syntactic restriction and shrinkage of the deduplicated boundary

This file builds the **syntactic restriction** primitive `subst1 C i v` (substitute the boolean `v` for variable `i`
throughout the `ACC0Circuit` `C`) and proves it shrinks the deduplicated boundary of `…ACC0DedupShrink`.  It is the
restriction half of "shrinkage under restriction": fixing a variable removes it from the deduplicated `var`-leaf
support, and a `MOD` gate whose support contains `i` has its target shifted by the fixed contribution and its support
shrunk to `S.erase i` — so the residue boundary is unchanged in size and the variable boundary strictly drops.

## What is proved (clean axioms, no `sorry`)

* `subst1` — the syntactic restriction; on a `MOD` gate `mod q S t ↦ mod q (S.erase i) (t - c)` where
  `c = [i ∈ S] · v` is the fixed contribution to the residue.
* `weightOn_update` — the support-count splits across the fixed coordinate (`∑` lemma).
* `eval_subst1` — **`eval (subst1 C i v) x = eval C (Function.update x i v)`** (induction on `C`): the syntactic
  restriction matches the semantic one.
* `varSupp_subst1_subset` / `modOcc_subst1_le` / `ModsPos_subst1` — the deduplicated `var`-support drops to
  `(varSupp C).erase i`, the `MOD`-residue product does not grow, positive moduli are preserved.
* `varSupp_subst1_card_lt` — **restricting a *read* variable (`i ∈ varSupp C`) strictly shrinks the deduplicated
  boundary**: `|varSupp (subst1 C i v)| < |varSupp C|`.
* `sat_branch_subst1` — **`Satisfiable (eval C) ↔ Satisfiable (eval (subst1 C i false)) ∨ Satisfiable (eval (subst1 C i true))`**:
  SAT branches over the two restrictions of any variable.

## Honest scope

This is the *restriction algebra* that a shrinkage argument needs, with the deduplicated boundary proved monotone and
strictly decreasing on read variables.  It is **not** a switching lemma: one branch on a variable splits the work in
two but halves each boundary, so a single restriction gives no asymptotic gain by itself (`2 · modOcc · 2^{|vs|-1} =
modOcc · 2^{|vs|}`).  The asymptotic collapse — that a *random* restriction kills an `AC⁰` subtree to a constant with
high probability — is the deep switching content, still open here.  Still the cell/observer model; nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RestrictShrink

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ExtractObserver
open PallLean.Paper93.DeepMath.PathB.ACC0DedupShrink

variable {n : ℕ}

/-- **Syntactic restriction**: substitute the boolean `v` for variable `i` throughout the circuit.  On a `MOD q` gate
the fixed coordinate is removed from the support and its contribution `[i ∈ S] · v` subtracted from the target, so the
restricted gate computes the same residue test on the remaining variables. -/
def subst1 : ACC0Circuit n → Fin n → Bool → ACC0Circuit n
  | .const c, _, _ => .const c
  | .var j, i, v => if j = i then .const v else .var j
  | .not c, i, v => .not (subst1 c i v)
  | .and a b, i, v => .and (subst1 a i v) (subst1 b i v)
  | .or a b, i, v => .or (subst1 a i v) (subst1 b i v)
  | .mod q S t, i, v => .mod q (S.erase i) (t - (if i ∈ S then (if v then 1 else 0) else 0))

/-- **The support count splits across the fixed coordinate (proved).** -/
theorem weightOn_update (S : Finset (Fin n)) (x : Fin n → Bool) (i : Fin n) (v : Bool) :
    weightOn S (Function.update x i v) =
      weightOn (S.erase i) x + (if i ∈ S then (if v then 1 else 0) else 0) := by
  unfold weightOn
  by_cases hi : i ∈ S
  · rw [if_pos hi,
      ← Finset.add_sum_erase S (fun j => if Function.update x i v j then 1 else 0) hi,
      Function.update_self, add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  · rw [if_neg hi, add_zero, Finset.erase_eq_of_notMem hi]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Function.update_of_ne (by rintro rfl; exact hi hj)]

/-- **The syntactic restriction matches the semantic one (proved, induction on `C`).** -/
theorem eval_subst1 (i : Fin n) (v : Bool) :
    ∀ (C : ACC0Circuit n) (x : Fin n → Bool),
      eval (subst1 C i v) x = eval C (Function.update x i v) := by
  intro C
  induction C with
  | const c => intro x; rfl
  | var j =>
      intro x
      show eval (if j = i then .const v else .var j) x = eval (.var j) (Function.update x i v)
      by_cases hji : j = i
      · rw [if_pos hji, hji]; simp [eval, Function.update_self]
      · rw [if_neg hji]; simp [eval, Function.update_of_ne hji]
  | not c ih => intro x; simp only [subst1, eval, ih x]
  | and a b iha ihb => intro x; simp only [subst1, eval, iha x, ihb x]
  | or a b iha ihb => intro x; simp only [subst1, eval, iha x, ihb x]
  | mod q S t =>
      intro x
      have hstat : modQStatOn S q (Function.update x i v)
          = modQStatOn (S.erase i) q x + (if i ∈ S then (if v then (1 : ZMod q) else 0) else 0) := by
        unfold modQStatOn
        rw [weightOn_update, Nat.cast_add]
        congr 1
        simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      simp only [subst1, eval]
      rw [hstat]
      exact decide_eq_decide.mpr eq_sub_iff_add_eq

/-- **The deduplicated `var`-support drops to `(varSupp C).erase i` under restriction (proved).** -/
theorem varSupp_subst1_subset (i : Fin n) (v : Bool) :
    ∀ (C : ACC0Circuit n), varSupp (subst1 C i v) ⊆ (varSupp C).erase i := by
  intro C
  induction C with
  | const c => simp [subst1, varSupp]
  | var j =>
      by_cases hji : j = i
      · subst hji; simp [subst1, varSupp]
      · simp only [subst1, varSupp, if_neg hji]
        intro z hz
        rw [Finset.mem_singleton] at hz
        subst hz
        rw [Finset.mem_erase]
        exact ⟨hji, Finset.mem_singleton_self z⟩
  | not c ih => simpa [subst1, varSupp] using ih
  | and a b iha ihb =>
      simp only [subst1, varSupp]
      calc varSupp (subst1 a i v) ∪ varSupp (subst1 b i v)
          ⊆ (varSupp a).erase i ∪ (varSupp b).erase i := Finset.union_subset_union iha ihb
        _ = (varSupp a ∪ varSupp b).erase i := (Finset.erase_union_distrib _ _ _).symm
  | or a b iha ihb =>
      simp only [subst1, varSupp]
      calc varSupp (subst1 a i v) ∪ varSupp (subst1 b i v)
          ⊆ (varSupp a).erase i ∪ (varSupp b).erase i := Finset.union_subset_union iha ihb
        _ = (varSupp a ∪ varSupp b).erase i := (Finset.erase_union_distrib _ _ _).symm
  | mod q S t => simp [subst1, varSupp]

/-- **The `MOD`-residue product does not grow under restriction (proved).** -/
theorem modOcc_subst1_le (i : Fin n) (v : Bool) :
    ∀ (C : ACC0Circuit n), modOcc (subst1 C i v) ≤ modOcc C := by
  intro C
  induction C with
  | const c => simp [subst1, modOcc]
  | var j => by_cases hji : j = i <;> simp [subst1, modOcc, hji]
  | not c ih => simpa [subst1, modOcc] using ih
  | and a b iha ihb => simp only [subst1, modOcc]; exact Nat.mul_le_mul iha ihb
  | or a b iha ihb => simp only [subst1, modOcc]; exact Nat.mul_le_mul iha ihb
  | mod q S t => simp [subst1, modOcc]

/-- **Positive `MOD` moduli are preserved under restriction (proved).** -/
theorem ModsPos_subst1 (i : Fin n) (v : Bool) :
    ∀ (C : ACC0Circuit n), ModsPos C → ModsPos (subst1 C i v) := by
  intro C
  induction C with
  | const c => intro _; trivial
  | var j => intro _; by_cases hji : j = i <;> simp [subst1, ModsPos, hji]
  | not c ih => intro h; exact ih h
  | and a b iha ihb => intro h; exact ⟨iha h.1, ihb h.2⟩
  | or a b iha ihb => intro h; exact ⟨iha h.1, ihb h.2⟩
  | mod q S t => intro h; exact h

/-- **Restricting a *read* variable strictly shrinks the deduplicated boundary (proved).** -/
theorem varSupp_subst1_card_lt (C : ACC0Circuit n) (i : Fin n) (v : Bool) (h : i ∈ varSupp C) :
    (varSupp (subst1 C i v)).card < (varSupp C).card :=
  calc (varSupp (subst1 C i v)).card
      ≤ ((varSupp C).erase i).card := Finset.card_le_card (varSupp_subst1_subset i v C)
    _ = (varSupp C).card - 1 := Finset.card_erase_of_mem h
    _ < (varSupp C).card := Nat.sub_lt (Finset.card_pos.mpr ⟨i, h⟩) one_pos

/-- **SAT branches over the two restrictions of any variable (proved).**  The branch-and-restrict primitive at the
syntax level: each branch is a strictly smaller circuit (by `varSupp_subst1_card_lt` when `i` is read). -/
theorem sat_branch_subst1 (C : ACC0Circuit n) (i : Fin n) :
    Satisfiable (eval C) ↔
      Satisfiable (eval (subst1 C i false)) ∨ Satisfiable (eval (subst1 C i true)) := by
  unfold Satisfiable
  constructor
  · rintro ⟨x, hx⟩
    have hkey : eval (subst1 C i (x i)) x = true := by
      rw [eval_subst1 i (x i) C x, Function.update_eq_self]; exact hx
    cases hxi : x i with
    | false => rw [hxi] at hkey; exact Or.inl ⟨x, hkey⟩
    | true => rw [hxi] at hkey; exact Or.inr ⟨x, hkey⟩
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · exact ⟨Function.update x i false, by rw [← eval_subst1 i false C x]; exact hx⟩
    · exact ⟨Function.update x i true, by rw [← eval_subst1 i true C x]; exact hx⟩

end PallLean.Paper93.DeepMath.PathB.ACC0RestrictShrink

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RestrictShrink.eval_subst1
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RestrictShrink.varSupp_subst1_card_lt
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RestrictShrink.sat_branch_subst1
