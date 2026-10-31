import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CircuitReprP

/-!
# Bridge (residue-family construction) — `pinTrue` arity-extension, eval-correct (proved)

The residue-family construction underlying the single-`MOD_q` ⇒ family reduction.  The `q` residue indicators
`[weight ≡ j mod q]` are *shifts* of one another: padding an input `x : Fin n → Bool` with `k` extra `true` bits raises its
Hamming weight by exactly `k` (`weight_extend`), so `[weight(x,1ᵏ) ≡ 0] = [weight(x) ≡ −k]`.  The circuit realising this
padding is `pinTrue : ACC0Circuit (n+k) → ACC0Circuit n`, which fixes the last `k` inputs to `true`; it satisfies
`eval (pinTrue C) x = eval C (x ⧺ 1ᵏ)` (`pinTrue_eval`), preserves `AC⁰[p]` (`pinTrue_modpOnly`), and does not increase
depth (`pinTrue_depth`).  Hence from a single residue-`0` `AC⁰[p]` circuit at arity `n+k` one builds a residue-`(−k mod q)`
`AC⁰[p]` circuit at arity `n` (`pinTrue_residue_shift`) — the family-from-one operation.

## What is proved (clean axioms, no `sorry`)

* **`weight_extend`** (PROVED) — `weight(x ⧺ 1ᵏ) = weight(x) + k`.
* **`pinTrue`** + **`pinTrue_eval`** (PROVED) — the input-pinning circuit op, eval-correct (incl. the `mod`-gate
  support-reindex + target-shift).
* **`pinTrue_modpOnly`** (PROVED) — preserves `ModpOnly`.
* **`pinTrue_depth`** (PROVED) — `depth (pinTrue C) ≤ depth C`.
* **`pinTrue_residue_shift`** (PROVED) — a residue-`0` circuit at arity `n+k`, pinned, computes `[weight(x) + k ≡ 0 mod q]`.

## Honest scope

This is the residue-family **construction operation** (eval / AC⁰[p] / depth correct).  Assembling it into the full
single-`MOD_q ∉ AC⁰[p]` for *all* `n` via `modq_indicators_false_acc0` additionally needs the **subcircuit-count (size)
bound through `pinTrue`** (and a uniform residue-`0` family across arities `n .. n+q−1`) — the quantitative step, **not** done
here and **not** faked.  Williams cash-out still open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ResidueFamily

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit depth)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP (ModpOnly)
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation (weightOn modQStatOn)

variable {n k : ℕ}

/-- Pad an input with `k` extra `true` bits. -/
def extend (x : Fin n → Bool) : Fin (n + k) → Bool := Fin.append x (fun _ => true)

@[simp] theorem extend_castAdd (x : Fin n → Bool) (i : Fin n) :
    extend (k := k) x (Fin.castAdd k i) = x i := by simp [extend, Fin.append_left]

@[simp] theorem extend_natAdd (x : Fin n → Bool) (i : Fin k) :
    extend (k := k) x (Fin.natAdd n i) = true := by simp [extend, Fin.append_right]

/-- Evaluation of a padded input below the boundary. -/
theorem extend_lt (x : Fin n → Bool) (i : Fin (n + k)) (h : (i : ℕ) < n) :
    extend x i = x (Fin.castLT i h) := by
  conv_lhs => rw [show i = Fin.castAdd k (Fin.castLT i h) from by ext; simp]
  rw [extend_castAdd]

/-- Evaluation of a padded input at or above the boundary is `true`. -/
theorem extend_ge (x : Fin n → Bool) (i : Fin (n + k)) (h : ¬ (i : ℕ) < n) :
    extend x i = true := by
  obtain ⟨j, rfl⟩ : ∃ j : Fin k, i = Fin.natAdd n j :=
    ⟨⟨(i : ℕ) - n, by omega⟩, by ext; simp [Fin.natAdd]; omega⟩
  exact extend_natAdd x j

/-- **Padding raises the Hamming weight by `k` (PROVED).** -/
theorem weight_extend (x : Fin n → Bool) :
    (Finset.univ.filter (fun i : Fin (n + k) => extend x i = true)).card
      = (Finset.univ.filter (fun i : Fin n => x i = true)).card + k := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_add]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => by rw [extend_castAdd])
  · simp

/-- The support indices `< n`, reindexed into `Fin n` (the low part of `S`). -/
noncomputable def lowSupport (S : Finset (Fin (n + k))) : Finset (Fin n) :=
  S.preimage (Fin.castAdd k) ((Fin.castAdd_injective n k).injOn)

/-- The count of support indices `≥ n` (the high part of `S`, all pinned to `true`). -/
def highCard (S : Finset (Fin (n + k))) : ℕ := (S.filter (fun i : Fin (n + k) => ¬ (i : ℕ) < n)).card

/-- **Weight split: padding turns the support count over `S` into the low-part weight plus the high count (PROVED).** -/
theorem weightOn_extend_split (S : Finset (Fin (n + k))) (x : Fin n → Bool) :
    weightOn S (extend x) = weightOn (lowSupport S) x + highCard S := by
  classical
  rw [weightOn, ← Finset.sum_filter_add_sum_filter_not S (fun i : Fin (n + k) => (i : ℕ) < n)]
  have hhigh : (∑ i ∈ S.filter (fun i : Fin (n + k) => ¬ (i : ℕ) < n), if extend x i then 1 else 0)
      = highCard S := by
    rw [highCard, Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    simp only [Finset.mem_filter] at hi
    simp [extend_ge x i hi.2]
  have hlow : (∑ i ∈ S.filter (fun i : Fin (n + k) => (i : ℕ) < n), if extend x i then 1 else 0)
      = weightOn (lowSupport S) x := by
    rw [weightOn]
    refine Finset.sum_bij'
      (fun i hi => Fin.castLT i (by simp only [Finset.mem_filter] at hi; exact hi.2))
      (fun j _ => Fin.castAdd k j) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_filter] at hi
      simp only [lowSupport, Finset.mem_preimage]
      rw [show Fin.castAdd k (Fin.castLT i hi.2) = i from by ext; simp]
      exact hi.1
    · intro j hj; simp only [lowSupport, Finset.mem_preimage] at hj
      simp only [Finset.mem_filter]
      exact ⟨hj, by simp [Fin.castAdd, Fin.castLE]⟩
    · intro i hi; ext; simp [Fin.castAdd, Fin.castLE, Fin.castLT]
    · intro j _; ext; simp [Fin.castAdd, Fin.castLE, Fin.castLT]
    · intro i hi; simp only [Finset.mem_filter] at hi; rw [extend_lt x i hi.2]
  rw [hlow, hhigh]

/-- The input-pinning / arity-extension circuit operation: fix the last `k` inputs to `true`. -/
noncomputable def pinTrue : ACC0Circuit (n + k) → ACC0Circuit n
  | .const b => .const b
  | .var i => if h : (i : ℕ) < n then .var (Fin.castLT i h) else .const true
  | .not c => .not (pinTrue c)
  | .and a b => .and (pinTrue a) (pinTrue b)
  | .or a b => .or (pinTrue a) (pinTrue b)
  | .mod q S t => .mod q (lowSupport S) (t - ((highCard S : ℕ) : ZMod q))

/-- **`pinTrue` is eval-correct: it computes `C` on the padded input (PROVED).** -/
theorem pinTrue_eval (C : ACC0Circuit (n + k)) (x : Fin n → Bool) :
    ACC0CircuitModel.eval (pinTrue C) x = ACC0CircuitModel.eval C (extend x) := by
  induction C with
  | const b => rfl
  | var i =>
      simp only [pinTrue]
      by_cases h : (i : ℕ) < n
      · rw [dif_pos h]; exact (extend_lt x i h).symm
      · rw [dif_neg h]; exact (extend_ge x i h).symm
  | not c ih => simp only [pinTrue, ACC0CircuitModel.eval, ih]
  | and a b iha ihb => simp only [pinTrue, ACC0CircuitModel.eval, iha, ihb]
  | or a b iha ihb => simp only [pinTrue, ACC0CircuitModel.eval, iha, ihb]
  | mod q S t =>
      simp only [pinTrue, ACC0CircuitModel.eval, modQStatOn]
      apply decide_eq_decide.mpr
      rw [weightOn_extend_split S x]
      push_cast
      exact eq_sub_iff_add_eq

/-- **`pinTrue` preserves `AC⁰[p]` (PROVED).** -/
theorem pinTrue_modpOnly (p : ℕ) (C : ACC0Circuit (n + k)) (h : ModpOnly p C) :
    ModpOnly p (pinTrue C) := by
  induction C with
  | const b => trivial
  | var i => simp only [pinTrue]; by_cases hh : (i : ℕ) < n <;> simp [hh, ModpOnly]
  | not c ih => exact ih (by simpa [ModpOnly] using h)
  | and a b iha ihb => simp only [ModpOnly] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | or a b iha ihb => simp only [ModpOnly] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | mod q S t => simpa [pinTrue, ModpOnly] using h

/-- **`pinTrue` does not increase depth (PROVED).** -/
theorem pinTrue_depth (C : ACC0Circuit (n + k)) : depth (pinTrue C) ≤ depth C := by
  induction C with
  | const b => simp [pinTrue, depth]
  | var i => simp only [pinTrue]; by_cases hh : (i : ℕ) < n <;> simp [hh, depth]
  | not c ih => simp only [pinTrue, depth]; omega
  | and a b iha ihb => simp only [pinTrue, depth]; omega
  | or a b iha ihb => simp only [pinTrue, depth]; omega
  | mod q S t => simp [pinTrue, depth]

/-- **Residue shift: a residue-`0` circuit at arity `n+k`, pinned, computes `[weight(x) + k ≡ 0 mod q]` (PROVED).**
This is the family-from-one operation: from one residue indicator, `pinTrue` produces the others. -/
theorem pinTrue_residue_shift (q : ℕ) (C : ACC0Circuit (n + k)) (x : Fin n → Bool)
    (hC : ∀ y : Fin (n + k) → Bool,
      ACC0CircuitModel.eval C y = decide ((Finset.univ.filter (fun i => y i = true)).card % q = 0)) :
    ACC0CircuitModel.eval (pinTrue C) x
      = decide (((Finset.univ.filter (fun i => x i = true)).card + k) % q = 0) := by
  rw [pinTrue_eval, hC, weight_extend]

/-!
**The residue-family construction operation, proved.**  `pinTrue` is the eval/AC⁰[p]/depth-correct circuit realising input
padding; `weight_extend` is the residue shift `weight(x,1ᵏ) = weight(x)+k`.  Together they build any residue indicator from a
single one.  Remaining (open, not faked): the subcircuit-count (size) bound through `pinTrue` + uniform-family assembly to
close `modq_indicators_false_acc0` into single-`MOD_q ∉ AC⁰[p]` for all `n`; and the Williams cash-out.  Not `NEXP ⊄ ACC⁰`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ResidueFamily

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ResidueFamily.pinTrue_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ResidueFamily.pinTrue_residue_shift
