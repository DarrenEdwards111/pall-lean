import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameEndToEnd

/-!
# N-Frame: the binary decoder — value-correctness

The RAM file used one-hot addressing and named the binary residue: the `w → 2^w` decoder's *size* was already bounded
(`volume_mintermOn_le`); its **value-correctness** was the named mechanical step.  This file proves it, closing the
binary-addressing residue:

  `bitsVal` / `numToBits` — the binary value of a bit-vector, and its inverse.
  `bitsVal_lt` / `bitsVal_inj` / `numToBits_bitsVal` / `numToBits_of_bitsVal` — **PROVED**: the number ↔ pattern
        **bijection** below `2^w` (elementary parity/quotient induction, self-contained).
  `decoder_line_correct` — **PROVED, the decoder theorem**: the decoder line for value `v` — a `mintermOn` tree over the
        address coordinates — evaluates true **iff** the binary value of the address bits equals `v`.  With the
        bijection this makes the decoder output one-hot: on any input, exactly the line of the address's value fires.

Together with `volume_mintermOn_le` (each line `≤ 3w+1` gates, `2^w` lines), binary addressing reduces to the one-hot
machinery of the RAM file with a polynomial decoder layer, value-correct.

## Honest scope

This closes the named decoder residue.  The remaining mechanical residue on the machine side is the program-controlled
RAM's instruction dispatch (an `O(1)`-way multiplexer, same pattern).  The open target `NFrameCircuitLowerBoundTarget
SAT` is untouched.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The binary value and its inverse -/

/-- The binary value of a `w`-bit vector (bit `j` has weight `2^j`). -/
def bitsVal {w : ℕ} (a : Fin w → Bool) : ℕ :=
  ∑ j : Fin w, cond (a j) (2 ^ j.val) 0

/-- The bit-vector of a number. -/
def numToBits (w : ℕ) (v : ℕ) : Fin w → Bool :=
  fun j => decide (v / 2 ^ j.val % 2 = 1)

theorem bitsVal_succ {w : ℕ} (a : Fin (w + 1) → Bool) :
    bitsVal a = cond (a 0) 1 0 + 2 * bitsVal (fun j : Fin w => a j.succ) := by
  unfold bitsVal
  rw [Fin.sum_univ_succ]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  show cond (a j.succ) (2 ^ (j.val + 1)) 0 = 2 * cond (a j.succ) (2 ^ j.val) 0
  cases a j.succ
  · rfl
  · show 2 ^ (j.val + 1) = 2 * 2 ^ j.val
    rw [pow_succ]
    ring

theorem bitsVal_lt {w : ℕ} (a : Fin w → Bool) : bitsVal a < 2 ^ w := by
  induction w with
  | zero =>
    show bitsVal a < 1
    unfold bitsVal
    simp
  | succ w ih =>
    rw [bitsVal_succ]
    have h1 := ih (fun j : Fin w => a j.succ)
    have h2 : cond (a 0) 1 0 ≤ 1 := by cases a 0 <;> simp
    have h3 : (2 : ℕ) ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
    omega

/-- **Injectivity (proved)**: distinct bit-vectors have distinct values. -/
theorem bitsVal_inj : ∀ {w : ℕ} (a b : Fin w → Bool), bitsVal a = bitsVal b → a = b := by
  intro w
  induction w with
  | zero =>
    intro a b _
    funext j
    exact Fin.elim0 j
  | succ w ih =>
    intro a b heq
    rw [bitsVal_succ, bitsVal_succ] at heq
    have hca : cond (a 0) 1 0 ≤ 1 := by cases a 0 <;> simp
    have hcb : cond (b 0) 1 0 ≤ 1 := by cases b 0 <;> simp
    have hhead : cond (a 0) 1 0 = cond (b 0) 1 0 := by omega
    have htail : bitsVal (fun j : Fin w => a j.succ) = bitsVal (fun j : Fin w => b j.succ) := by
      omega
    have hab0 : a 0 = b 0 := by
      cases ha : a 0 <;> cases hb : b 0 <;> rw [ha, hb] at hhead <;> simp_all
    have htl := ih _ _ htail
    funext j
    refine Fin.cases ?_ ?_ j
    · exact hab0
    · intro k
      exact congrFun htl k

/-- **Surjectivity below `2^w` (proved)**: `numToBits` is a right inverse of `bitsVal`. -/
theorem numToBits_bitsVal : ∀ (w v : ℕ), v < 2 ^ w → bitsVal (numToBits w v) = v := by
  intro w
  induction w with
  | zero =>
    intro v hv
    have : v = 0 := by
      have : (2 : ℕ) ^ 0 = 1 := rfl
      omega
    subst this
    unfold bitsVal
    simp
  | succ w ih =>
    intro v hv
    rw [bitsVal_succ]
    have hhead : cond (numToBits (w + 1) v 0) 1 0 = v % 2 := by
      show cond (decide (v / 2 ^ (0 : ℕ) % 2 = 1)) 1 0 = v % 2
      rw [pow_zero, Nat.div_one]
      by_cases h : v % 2 = 1
      · rw [h]
        simp
      · have h0 : v % 2 = 0 := by omega
        rw [h0]
        simp
    have htail : (fun j : Fin w => numToBits (w + 1) v j.succ) = numToBits w (v / 2) := by
      funext j
      show decide (v / 2 ^ (j.val + 1) % 2 = 1) = decide (v / 2 / 2 ^ j.val % 2 = 1)
      rw [Nat.div_div_eq_div_mul, show (2 : ℕ) * 2 ^ j.val = 2 ^ (j.val + 1) from by
        rw [pow_succ]; ring]
    rw [hhead, htail, ih (v / 2) (by
      have h3 : (2 : ℕ) ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
      omega)]
    omega

/-- **The roundtrip (proved)**: `numToBits ∘ bitsVal = id`. -/
theorem numToBits_of_bitsVal {w : ℕ} (a : Fin w → Bool) : numToBits w (bitsVal a) = a :=
  bitsVal_inj _ _ (numToBits_bitsVal w (bitsVal a) (bitsVal_lt a))

/-! ### The decoder theorem -/

/-- **Decoder-line value-correctness (proved).**  The decoder line for value `v` — the `mintermOn` tree over the address
coordinates with pattern `numToBits w v` — fires **iff** the binary value of the address bits equals `v`.  By the
bijection, on any input exactly one line fires: the decoder output is one-hot at the address's value. -/
theorem decoder_line_correct {B w : ℕ} (addrCoord : Fin w → Fin B) (pat : Fin B → Bool)
    (v : ℕ) (hv : v < 2 ^ w) (hpat : ∀ j : Fin w, pat (addrCoord j) = numToBits w v j)
    (x : Fin B → Bool) :
    (eval (mintermOn pat ((List.finRange w).map addrCoord)) x = true)
      ↔ bitsVal (fun j => x (addrCoord j)) = v := by
  rw [eval_mintermOn, List.all_map, List.all_eq_true]
  constructor
  · intro h
    have hagree : (fun j => x (addrCoord j)) = numToBits w v := by
      funext j
      have := h j (List.mem_finRange j)
      simp only [Function.comp] at this
      have hbe := of_decide_eq_true (by exact this)
      rw [← hpat j]
      exact hbe
    rw [hagree]
    exact numToBits_bitsVal w v hv
  · intro h
    intro j _
    show decide (x (addrCoord j) = pat (addrCoord j)) = true
    rw [decide_eq_true_eq, hpat j]
    have : numToBits w (bitsVal (fun j => x (addrCoord j))) = (fun j => x (addrCoord j)) :=
      numToBits_of_bitsVal _
    rw [h] at this
    exact (congrFun this j).symm

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.bitsVal_inj
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.numToBits_bitsVal
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.decoder_line_correct
