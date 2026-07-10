import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPGenericCNFCodec
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPParityInterfaceDischarge

/-!
# Flatten-and-compose: the generic-encoding SAT lower bound (gap i, final step)

This file flattens the four structured incidence functions of the general decoder (`decodeCNF`) into a single
`Fin N → Bool` circuit input, realises the parity bit-pattern as a concrete `AC⁰` depth-`≤1`
`BoolCircuitSyntax n` family, and composes with the capstone (bricks 2–5) to obtain:

> **No small `AC⁰[p]` circuit decides SAT for all `decodeFlat p`** (an unconditional, super-polynomial lower
> bound on a *general* SAT decider, with the parity family reached through a local encoding).

## Honest scope

Gap (i) final step.  `decodeFlat` covers arbitrary bounded CNFs (its four extractors read arbitrary
incidences), so "the decider is correct on every `decodeFlat p`" is a genuine `SAT ∈ AC⁰[p]` hypothesis.
`sorry`-free.  It is an unconditional restricted result (`SAT`-family `∉` small-`AC⁰[p]`), NOT general
`SAT ∉ AC⁰[p]` (the reduction only produces easy/linear instances) and NOT `P ≠ NP`.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPGenericCNFComposition

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.PvsNPGenericCNFCodec
open SATDepthMachine

/-! ## The `j`-indexed parity incidence and its per-bit circuit -/

/-- The parity incidence at clause index `j`, variable `v`, sign `s`. -/
def pInc {n : Nat} (x : Fin n → Bool) (j : Nat) (v : Fin (n + 1)) (s : Bool) : Bool :=
  if j = 0 then bvHead n v s
  else if j = 2 * n + 1 then bvTail n v s
  else if (j - 1) % 2 = 0 then bvBlock1 x ((j - 1) / 2) v s
  else bvBlock2 x ((j - 1) / 2) v s

/-- The circuit computing `pInc · j v s` (with `j, v, s` fixed).  Always a `const`, `input`, or
`not (input _)` — hence `AC⁰`, depth `≤ 1`. -/
def pCirc (n : Nat) (j : Nat) (v : Fin (n + 1)) (s : Bool) : BoolCircuitSyntax n :=
  if j = 0 then .const (bvHead n v s)
  else if j = 2 * n + 1 then .const (bvTail n v s)
  else
    if (j - 1) % 2 = 0 then
      if (decide (v.val = (j - 1) / 2 + 1) && s) then .const true
      else if h : v.val = (j - 1) / 2 ∧ (j - 1) / 2 < n then
        (if s then .input ⟨(j - 1) / 2, h.2⟩ else .not (.input ⟨(j - 1) / 2, h.2⟩))
      else .const false
    else
      if (decide (v.val = (j - 1) / 2 + 1) && !s) then .const true
      else if h : v.val = (j - 1) / 2 ∧ (j - 1) / 2 < n then
        (if s then .not (.input ⟨(j - 1) / 2, h.2⟩) else .input ⟨(j - 1) / 2, h.2⟩)
      else .const false

/-- **`pCirc` computes `pInc`** (for a valid clause index `j < 2n+2`). -/
theorem pCirc_eval {n : Nat} (x : Fin n → Bool) (j : Nat) (hj : j < 2 * n + 2)
    (v : Fin (n + 1)) (s : Bool) :
    (pCirc n j v s).eval x = pInc x j v s := by
  unfold pCirc pInc
  split
  · simp [BoolCircuitSyntax.eval]
  · split
    · simp [BoolCircuitSyntax.eval]
    · rename_i hj0 hjn
      have hkn : (j - 1) / 2 < n := by omega
      set k := (j - 1) / 2 with hk
      have hxk : (List.ofFn x).getD k false = x ⟨k, hkn⟩ := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp [hkn]
      split
      · -- block1
        unfold bvBlock1
        split
        · rename_i hcond
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
          simp [BoolCircuitSyntax.eval, hcond.1, hcond.2]
        · split
          · rename_i _ h
            obtain ⟨hv, hk2⟩ := h
            have hxk2 : (List.ofFn x).getD k false = x ⟨k, hk2⟩ := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hk2, Option.getD_some]
            have h1 : ¬ v.val = k + 1 := by omega
            rw [hxk2]
            rcases s <;> simp [BoolCircuitSyntax.eval, hv, h1, Bool.true_beq, Bool.false_beq, hk]
          · rename_i hcond h
            simp only [not_and_or, not_lt] at h
            rcases h with hv | hkn2
            · simp only [BoolCircuitSyntax.eval]
              rcases s <;> simp_all [Bool.and_eq_true, decide_eq_true_eq]
            · omega
      · -- block2
        unfold bvBlock2
        split
        · rename_i hcond
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hcond
          simp [BoolCircuitSyntax.eval, hcond.1, hcond.2]
        · split
          · rename_i _ h
            obtain ⟨hv, hk2⟩ := h
            have hxk2 : (List.ofFn x).getD k false = x ⟨k, hk2⟩ := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hk2, Option.getD_some]
            have h1 : ¬ v.val = k + 1 := by omega
            rw [hxk2]
            rcases s <;> simp [BoolCircuitSyntax.eval, hv, h1, Bool.true_beq, Bool.false_beq, hk]
          · rename_i hcond h
            simp only [not_and_or, not_lt] at h
            rcases h with hv | hkn2
            · simp only [BoolCircuitSyntax.eval]
              rcases s <;> simp_all [Bool.and_eq_true, decide_eq_true_eq]
            · omega

/-- **`pCirc` is `AC⁰`.** -/
theorem pCirc_ac0 (n : Nat) (j : Nat) (v : Fin (n + 1)) (s : Bool) :
    (pCirc n j v s).IsAC0Syntax := by
  unfold pCirc
  repeat' split
  all_goals first
    | exact True.intro
    | (intro c hc; simp at hc)
    | simp [BoolCircuitSyntax.IsAC0Syntax]

/-- **`pCirc` has depth `≤ 1`.** -/
theorem pCirc_depth_le (n : Nat) (j : Nat) (v : Fin (n + 1)) (s : Bool) :
    (pCirc n j v s).depth ≤ 1 := by
  unfold pCirc
  repeat' split
  all_goals simp [BoolCircuitSyntax.depth]

end PallLean.Paper93.DeepMath.PathB.PvsNPGenericCNFComposition

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPGenericCNFComposition.pCirc_eval
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPGenericCNFComposition.pCirc_ac0
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPGenericCNFComposition.pCirc_depth_le
