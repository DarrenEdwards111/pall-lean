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
open PallLean.Paper93.DeepMath.PathB.PvsNPParityToSAT

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

/-- Every local parity-incidence circuit has at most two nodes. -/
theorem pCirc_size_le (n : Nat) (j : Nat) (v : Fin (n + 1)) (s : Bool) :
    (pCirc n j v s).size ≤ 2 := by
  unfold pCirc
  repeat' split
  all_goals simp [BoolCircuitSyntax.size]

/-! ## Flattening the incidence into a single `Fin N` circuit input -/

/-- The flat incidence index: (clause, variable, sign). -/
abbrev Idx (n : Nat) : Type := Fin (2 * n + 2) × Fin (n + 1) × Bool

/-- The flattening bijection to `Fin N`. -/
noncomputable def e (n : Nat) : Idx n ≃ Fin (Fintype.card (Idx n)) := Fintype.equivFin (Idx n)

/-- The flat input arity. -/
def Nbits (n : Nat) : Nat := Fintype.card (Idx n)

/-- The `AC⁰` depth-`≤1` circuit family realising the parity bit-pattern. -/
noncomputable def bvFamily {n : Nat} (k : Fin (Nbits n)) : BoolCircuitSyntax n :=
  pCirc n ((e n).symm k).1.val ((e n).symm k).2.1 ((e n).symm k).2.2

/-- Every member of the flattened local encoding family has size at most two. -/
theorem bvFamily_size {n : Nat} (k : Fin (Nbits n)) :
    (bvFamily k).size ≤ 2 := by
  exact pCirc_size_le n ((e n).symm k).1.val ((e n).symm k).2.1 ((e n).symm k).2.2

/-- The parity flat bit-pattern. -/
noncomputable def bv {n : Nat} (x : Fin n → Bool) (k : Fin (Nbits n)) : Bool :=
  pInc x ((e n).symm k).1.val ((e n).symm k).2.1 ((e n).symm k).2.2

theorem bvFamily_eval {n : Nat} (x : Fin n → Bool) (k : Fin (Nbits n)) :
    (bvFamily k).eval x = bv x k :=
  pCirc_eval x _ ((e n).symm k).1.isLt _ _

theorem bvFamily_ac0 {n : Nat} (k : Fin (Nbits n)) : (bvFamily k).IsAC0Syntax :=
  pCirc_ac0 n _ _ _

theorem bvFamily_depth {n : Nat} (k : Fin (Nbits n)) : (bvFamily k).depth ≤ 1 :=
  pCirc_depth_le n _ _ _

/-! ## The flat general decoder and its correctness on the parity bit-pattern -/

/-- The general bounded-CNF decoder over a single `Fin N → Bool` input. -/
noncomputable def decodeFlat {n : Nat} (b : Fin (Nbits n) → Bool) : CNF :=
  decodeCNF n
    (fun v s => b (e n (⟨0, by omega⟩, v, s)))
    (fun k v s => if h : 2 * k + 1 < 2 * n + 2 then b (e n (⟨2 * k + 1, h⟩, v, s)) else false)
    (fun k v s => if h : 2 * k + 2 < 2 * n + 2 then b (e n (⟨2 * k + 2, h⟩, v, s)) else false)
    (fun v s => b (e n (⟨2 * n + 1, by omega⟩, v, s)))

/-- `decodeCNF` only depends on its block functions over `range n`. -/
theorem decodeCNF_congr {n : Nat} (h t : Fin (n + 1) → Bool → Bool)
    (b1 b1' b2 b2' : Nat → Fin (n + 1) → Bool → Bool)
    (hb1 : ∀ k, k < n → b1 k = b1' k) (hb2 : ∀ k, k < n → b2 k = b2' k) :
    decodeCNF n h b1 b2 t = decodeCNF n h b1' b2' t := by
  unfold decodeCNF
  congr 1
  congr 1
  congr 1
  apply List.flatMap_congr
  intro k hk
  rw [hb1 k (List.mem_range.mp hk), hb2 k (List.mem_range.mp hk)]

theorem head_eq {n : Nat} (x : Fin n → Bool) :
    (fun v s => bv x (e n (⟨0, by omega⟩, v, s))) = bvHead n := by
  funext v s
  show pInc x _ _ _ = bvHead n v s
  rw [Equiv.symm_apply_apply]
  simp [pInc]

theorem tail_eq {n : Nat} (x : Fin n → Bool) :
    (fun v s => bv x (e n (⟨2 * n + 1, by omega⟩, v, s))) = bvTail n := by
  funext v s
  show pInc x _ _ _ = bvTail n v s
  rw [Equiv.symm_apply_apply]
  show pInc x (2 * n + 1) v s = bvTail n v s
  unfold pInc
  rw [if_neg (by omega), if_pos rfl]

theorem block1_eq {n : Nat} (x : Fin n → Bool) (k : Nat) (hk : k < n) :
    (fun v s => if h : 2 * k + 1 < 2 * n + 2 then bv x (e n (⟨2 * k + 1, h⟩, v, s)) else false)
      = bvBlock1 x k := by
  funext v s
  rw [dif_pos (by omega : 2 * k + 1 < 2 * n + 2)]
  show pInc x _ _ _ = bvBlock1 x k v s
  rw [Equiv.symm_apply_apply]
  show pInc x (2 * k + 1) v s = bvBlock1 x k v s
  unfold pInc
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show (2 * k + 1 - 1) / 2 = k by omega]

theorem block2_eq {n : Nat} (x : Fin n → Bool) (k : Nat) (hk : k < n) :
    (fun v s => if h : 2 * k + 2 < 2 * n + 2 then bv x (e n (⟨2 * k + 2, h⟩, v, s)) else false)
      = bvBlock2 x k := by
  funext v s
  rw [dif_pos (by omega : 2 * k + 2 < 2 * n + 2)]
  show pInc x _ _ _ = bvBlock2 x k v s
  rw [Equiv.symm_apply_apply]
  show pInc x (2 * k + 2) v s = bvBlock2 x k v s
  unfold pInc
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    show (2 * k + 2 - 1) / 2 = k by omega]

/-- **The flat decoder of the parity bit-pattern is `decodeCNF` of the parity incidence.** -/
theorem decodeFlat_bv {n : Nat} (x : Fin n → Bool) :
    decodeFlat (bv x) = decodeCNF n (bvHead n) (bvBlock1 x) (bvBlock2 x) (bvTail n) := by
  unfold decodeFlat
  rw [head_eq x, tail_eq x]
  exact decodeCNF_congr _ _ _ _ _ _ (fun k hk => block1_eq x k hk) (fun k hk => block2_eq x k hk)

/-- **The flat decoder realises the parity family: `Satisfiable (decodeFlat (bv x)) ↔ ⊕ x = 0`.** -/
theorem decodeFlat_sat_iff_even {n : Nat} (x : Fin n → Bool) :
    Satisfiable (decodeFlat (bv x)) ↔ bxor (List.ofFn x) = false := by
  rw [decodeFlat_bv]; exact decodeCNF_sat_iff_even x

/-! ## Composition with the capstone: no small `AC⁰[p]` general-SAT decider -/

open PallLean.Paper93.DeepMath.PathB.PvsNPCircuitComposition
open PallLean.Paper93.DeepMath.PathB.PvsNPParitySATBridge
open PallLean.Paper93.DeepMath.PathB.PvsNPParityInterfaceDischarge

/-- **Gap (i) closed — the generic-encoding SAT lower bound (unconditional).**

If `Dec` is an `AC⁰[p]` circuit that decides SAT for **every** `decodeFlat b` (a general SAT decider over the
`Fin N`-bit-encoded bounded-CNF class), then the composite `subst Dec bvFamily` — which computes `PARITY`
because the parity family sits in `decodeFlat`'s range through the local `AC⁰` encoding — has size `≥ lower - 1`
for any `lower` with `4·lower ≤ pᵗ` and `m` in the RS window at depth `Dec.depth + 2`.  Taking
`t ≈ m^{1/(2(d+2))}` makes `lower` super-polynomial. -/
theorem no_small_ac0p_generic_SAT_decider_unconditional
    (m p t lower : ℕ) [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0) (ht1 : 1 ≤ t)
    (hpt : 1 ≤ (p - 1) * t)
    (Dec : BoolCircuitSyntax (Nbits (2 * m + 1)))
    (hm : 8 * (((p - 1) * t) ^ (Dec.depth + 2)) ^ 2 ≤ m)
    (hDec_ac0p : Dec.IsAC0pSyntax p)
    (hDec : ∀ b : Fin (Nbits (2 * m + 1)) → Bool,
      Dec.eval b = true ↔ Satisfiable (decodeFlat b))
    (hlow : 4 * lower ≤ p ^ t) :
    lower ≤ (subst Dec bvFamily).size + 1 := by
  have hac0p : (subst Dec bvFamily).IsAC0pSyntax p :=
    isAC0pSyntax_subst p Dec bvFamily
      (fun k => isAC0Syntax_imp_isAC0pSyntax p (bvFamily k) (bvFamily_ac0 k)) hDec_ac0p
  have hsat : ∀ x : Fin (2 * m + 1) → Bool,
      (subst Dec bvFamily).eval x = true ↔ Satisfiable (parityCNF (List.ofFn x)) := by
    intro x
    rw [eval_subst]
    have hfun : (fun j => (bvFamily j).eval x) = bv x := by funext j; exact bvFamily_eval x j
    rw [hfun, hDec, decodeFlat_bv]
    exact decodeCNF_sat_iff x
  have hdepth : (subst Dec bvFamily).depth ≤ Dec.depth + 1 := depth_subst_le 1 Dec bvFamily bvFamily_depth
  have hwin : 8 * (((p - 1) * t) ^ ((subst Dec bvFamily).depth + 1)) ^ 2 ≤ m := by
    refine le_trans ?_ hm
    have hmono : ((p - 1) * t) ^ ((subst Dec bvFamily).depth + 1)
        ≤ ((p - 1) * t) ^ (Dec.depth + 2) := Nat.pow_le_pow_right hpt (by omega)
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmono 2)
  exact no_small_ac0p_parityCNF_decider_unconditional p hp2 m t ht1 (subst Dec bvFamily)
    hwin hac0p hsat lower hlow

/-- **Actual lower bound on the generic SAT-decider circuit itself.** The local codec replaces every
input by a circuit of size at most two, so the parity lower bound on the composite implies
`lower ≤ 2 * Dec.size + 1`. -/
theorem generic_SAT_decider_size_lower_bound
    (m p t lower : ℕ) [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0) (ht1 : 1 ≤ t)
    (hpt : 1 ≤ (p - 1) * t)
    (Dec : BoolCircuitSyntax (Nbits (2 * m + 1)))
    (hm : 8 * (((p - 1) * t) ^ (Dec.depth + 2)) ^ 2 ≤ m)
    (hDec_ac0p : Dec.IsAC0pSyntax p)
    (hDec : ∀ b : Fin (Nbits (2 * m + 1)) → Bool,
      Dec.eval b = true ↔ Satisfiable (decodeFlat b))
    (hlow : 4 * lower ≤ p ^ t) :
    lower ≤ 2 * Dec.size + 1 := by
  have hlower := no_small_ac0p_generic_SAT_decider_unconditional
    m p t lower hp2 ht1 hpt Dec hm hDec_ac0p hDec hlow
  have hsize : (subst Dec bvFamily).size ≤ Dec.size * 2 :=
    subst_size_le bvFamily 2 bvFamily_size (by omega) Dec
  omega

/-- Fixed-depth packaging of the generic SAT-decider lower bound.  A uniform depth cap `d` supplies
the Razborov--Smolensky window independently of the particular circuit's actual depth. -/
theorem generic_SAT_decider_size_lower_bound_depth_le
    (m p t lower d : ℕ) [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0) (ht1 : 1 ≤ t)
    (hpt : 1 ≤ (p - 1) * t)
    (Dec : BoolCircuitSyntax (Nbits (2 * m + 1)))
    (hdepth : Dec.depth ≤ d)
    (hm : 8 * (((p - 1) * t) ^ (d + 2)) ^ 2 ≤ m)
    (hDec_ac0p : Dec.IsAC0pSyntax p)
    (hDec : ∀ b : Fin (Nbits (2 * m + 1)) → Bool,
      Dec.eval b = true ↔ Satisfiable (decodeFlat b))
    (hlow : 4 * lower ≤ p ^ t) :
    lower ≤ 2 * Dec.size + 1 := by
  have hpow : ((p - 1) * t) ^ (Dec.depth + 2) ≤ ((p - 1) * t) ^ (d + 2) :=
    Nat.pow_le_pow_right hpt (by omega)
  have hm' : 8 * (((p - 1) * t) ^ (Dec.depth + 2)) ^ 2 ≤ m := by
    exact le_trans (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hpow 2)) hm
  exact generic_SAT_decider_size_lower_bound
    m p t lower hp2 ht1 hpt Dec hm' hDec_ac0p hDec hlow

end PallLean.Paper93.DeepMath.PathB.PvsNPGenericCNFComposition

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPGenericCNFComposition.pCirc_eval
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPGenericCNFComposition.pCirc_ac0
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPGenericCNFComposition.pCirc_depth_le
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPGenericCNFComposition.pCirc_size_le
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPGenericCNFComposition.bvFamily_eval
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPGenericCNFComposition.bvFamily_ac0
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPGenericCNFComposition.decodeFlat_sat_iff_even
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPGenericCNFComposition.no_small_ac0p_generic_SAT_decider_unconditional
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPGenericCNFComposition.generic_SAT_decider_size_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPGenericCNFComposition.generic_SAT_decider_size_lower_bound_depth_le
