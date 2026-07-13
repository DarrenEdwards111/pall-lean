import PallLean.Paper93.DeepMath.PathB.ComputationalDepthChargedGateLanguage
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthQFEasyHardMPS

/-!
# Step (3), calibration half: compiling the easy functions into the charged language

Compiles the four calibration targets into `ChargedGate.Prog` with **exact correctness** and polynomial cost:

* `constFalseProg` / `constTrueProg` — cost `0` / `3`;
* `parityProg` — parity of all `n` bits, cost `2n`;
* `eqProg` — equality of two `k`-bit halves, cost `3 + 5k`;
* `qfProg A` — the Boolean core of `QF A` (`decide (qf A z = 1)`), cost `4n²`.

This is the **critical easy-function gate**: the charged language admits polynomial-cost programs for exactly the
functions that static MPS cost gets wrong.  In particular `qfProg` puts `QF A` at `4n²` **charged dynamic** cost
while its static all-order MPS cost is `≥ 2^r` (`QFEasyHard.QF_cost_all_orderings`) — the distinction "static
poly-MPS universality is false, polynomial dynamic simulation exists" is now formal on both sides.  Any later
dynamic invariant must respect these calibrations.

## Honest scope

The calibration half of step (3) only: four concrete compiles.  The general bounded-fan-in circuit compiler
(arbitrary circuits/machines → charged programs with poly overhead) is the remaining half.  The dependency bound of
the language stays linear-strength; nothing here is a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ChargedCompiler

open PallLean.Paper93.DeepMath.PathB.ChargedGate
open PallLean.Paper93.DeepMath.PathB.GlobalResidual
open PallLean.Paper93.DeepMath.PathB.QFEasyHard

variable {n k : ℕ}

/-- Sequential execution splits over append. -/
theorem runGates_append (z : Fin n → Bool) (l1 l2 : List (Gate n 3)) (s : Fin 3 → Bool) :
    runGates z (l1 ++ l2) s = runGates z l2 (runGates z l1 s) :=
  List.foldl_append

/-! ## Fold seed-extraction lemmas -/

theorem foldr_xor_seed {α : Type*} (t : α → Bool) (l : List α) (b c : Bool) :
    l.foldr (fun p a => xor (t p) a) (xor b c) = xor b (l.foldr (fun p a => xor (t p) a) c) := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [List.foldr_cons, List.foldr_cons, ih, Bool.xor_left_comm]

theorem foldr_and_seed {α : Type*} (t : α → Bool) (l : List α) (b c : Bool) :
    l.foldr (fun p a => t p && a) (b && c) = (b && l.foldr (fun p a => t p && a) c) := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [List.foldr_cons, List.foldr_cons, ih, Bool.and_left_comm]

/-- An AND-fold with an all-`true` term list is `true`. -/
theorem foldr_and_true {α : Type*} (t : α → Bool) (l : List α) (hall : ∀ i ∈ l, t i = true) :
    l.foldr (fun i a => t i && a) true = true := by
  induction l with
  | nil => rfl
  | cons i li ih =>
    rw [List.foldr_cons, hall i List.mem_cons_self, ih (fun j hj => hall j (List.mem_cons_of_mem i hj)),
      Bool.true_and]

/-- An AND-fold with one `false` term is `false`. -/
theorem foldr_and_false {α : Type*} (t : α → Bool) (l : List α) (i0 : α) (hmem : i0 ∈ l)
    (hbit : t i0 = false) : l.foldr (fun i a => t i && a) true = false := by
  induction l with
  | nil => exact absurd hmem List.not_mem_nil
  | cons i li ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hmem with heq | hmemli
    · rw [← heq, hbit, Bool.false_and]
    · rw [ih hmemli, Bool.and_false]

/-! ## Generic accumulator-loop invariants (wire `0` is the accumulator) -/

/-- XOR loop: if each block XORs its term into wire `0`, the flatMap folds all terms. -/
theorem xorLoop_invariant {α : Type*} (z : Fin n → Bool) (t : α → Bool) (blk : α → List (Gate n 3))
    (hblk : ∀ p s, (runGates z (blk p) s) 0 = xor (s 0) (t p)) (l : List α) (s : Fin 3 → Bool) :
    (runGates z (l.flatMap blk) s) 0 = l.foldr (fun p a => xor (t p) a) (s 0) := by
  induction l generalizing s with
  | nil => rfl
  | cons p l ih =>
    rw [List.flatMap_cons, runGates_append, ih, List.foldr_cons, hblk p s, Bool.xor_comm (s 0),
      foldr_xor_seed]

/-- AND loop: if each block ANDs its term into wire `0`, the flatMap folds all terms. -/
theorem andLoop_invariant {α : Type*} (z : Fin n → Bool) (t : α → Bool) (blk : α → List (Gate n 3))
    (hblk : ∀ p s, (runGates z (blk p) s) 0 = (s 0 && t p)) (l : List α) (s : Fin 3 → Bool) :
    (runGates z (l.flatMap blk) s) 0 = l.foldr (fun p a => t p && a) (s 0) := by
  induction l generalizing s with
  | nil => rfl
  | cons p l ih =>
    rw [List.flatMap_cons, runGates_append, ih, List.foldr_cons, hblk p s, Bool.and_comm (s 0),
      foldr_and_seed]

/-! ## Constants -/

/-- `false`: the empty program (the all-`false` start is the charged preparation). -/
def constFalseProg (n : ℕ) : Prog n 3 := ⟨[], 0⟩

theorem constFalseProg_correct (z : Fin n → Bool) : (constFalseProg n).run z = false := rfl

theorem constFalseProg_cost : (constFalseProg n).cost = 0 := rfl

/-- `true`: three charged gates (`x₀`, self-XOR to `false`, NOT). -/
def constTrueProg (hn : 0 < n) : Prog n 3 :=
  ⟨[.input ⟨0, hn⟩ 0, .xorg 0 0 0, .notg 0 0], 0⟩

theorem constTrueProg_correct (hn : 0 < n) (z : Fin n → Bool) : (constTrueProg hn).run z = true := by
  simp [constTrueProg, Prog.run, runGates, step, Function.update]

theorem constTrueProg_cost (hn : 0 < n) : (constTrueProg hn).cost = 3 := rfl

/-! ## Parity -/

/-- Parity of all `n` bits. -/
def xorAll (z : Fin n → Bool) : Bool := (List.finRange n).foldr (fun i a => xor (z i) a) false

/-- Per-bit block: load, XOR into the accumulator. -/
def parityBlock (i : Fin n) : List (Gate n 3) := [.input i 1, .xorg 0 1 0]

theorem parityBlock_wire0 (z : Fin n → Bool) (i : Fin n) (s : Fin 3 → Bool) :
    (runGates z (parityBlock i) s) 0 = xor (s 0) (z i) := by
  simp [parityBlock, runGates, step, Function.update]

/-- The parity program: `2n` charged gates. -/
def parityProg (n : ℕ) : Prog n 3 := ⟨(List.finRange n).flatMap parityBlock, 0⟩

theorem parityProg_correct (z : Fin n → Bool) : (parityProg n).run z = xorAll z := by
  unfold parityProg Prog.run xorAll
  exact xorLoop_invariant z z parityBlock (parityBlock_wire0 z) (List.finRange n) _

theorem parityProg_cost : (parityProg n).cost = 2 * n := by
  unfold parityProg Prog.cost
  rw [List.length_flatMap]
  have h1 : (List.map (fun i : Fin n => (parityBlock i).length) (List.finRange n))
      = List.replicate n 2 := by
    have h2 : (fun i : Fin n => (parityBlock i).length) = Function.const (Fin n) 2 := rfl
    rw [h2, List.map_const, List.length_finRange]
  rw [h1, List.sum_replicate, smul_eq_mul, Nat.mul_comm]

/-! ## Equality of two halves -/

/-- Equality of the two `k`-bit halves of a `k + k`-bit input. -/
def eqHalves (z : Fin (k + k) → Bool) : Bool :=
  decide (∀ i : Fin k, z (Fin.castAdd k i) = z (Fin.natAdd k i))

/-- Per-index block: load both bits, XOR, NOT (equality bit), AND into the accumulator. -/
def eqBlock (i : Fin k) : List (Gate (k + k) 3) :=
  [.input (Fin.castAdd k i) 1, .input (Fin.natAdd k i) 2, .xorg 1 2 1, .notg 1 1, .andg 0 1 0]

theorem eqBlock_wire0 (z : Fin (k + k) → Bool) (i : Fin k) (s : Fin 3 → Bool) :
    (runGates z (eqBlock i) s) 0 = (s 0 && !(xor (z (Fin.castAdd k i)) (z (Fin.natAdd k i)))) := by
  simp [eqBlock, runGates, step, Function.update]

/-- The equality program: `true` preamble, then the `k` blocks — `3 + 5k` charged gates. -/
def eqProg (hk : 0 < k) : Prog (k + k) 3 :=
  ⟨[.input ⟨0, by omega⟩ 0, .xorg 0 0 0, .notg 0 0] ++ (List.finRange k).flatMap eqBlock, 0⟩

theorem eqProg_correct (hk : 0 < k) (z : Fin (k + k) → Bool) : (eqProg hk).run z = eqHalves z := by
  unfold eqProg Prog.run
  rw [runGates_append]
  have hpre : (runGates z [.input ⟨0, by omega⟩ 0, .xorg 0 0 0, .notg 0 0] (fun _ => false))
      = Function.update (fun _ : Fin 3 => false) 0 true := by
    funext j
    simp [runGates, step, Function.update]
  rw [hpre]
  have hloop := andLoop_invariant z
    (fun i => !(xor (z (Fin.castAdd k i)) (z (Fin.natAdd k i)))) eqBlock
    (eqBlock_wire0 z) (List.finRange k) (Function.update (fun _ : Fin 3 => false) 0 true)
  rw [show (Function.update (fun _ : Fin 3 => false) 0 true) 0 = true from Function.update_self ..]
    at hloop
  rw [hloop]
  -- fold = all = decide ∀
  by_cases h : ∀ i : Fin k, z (Fin.castAdd k i) = z (Fin.natAdd k i)
  · rw [eqHalves, decide_eq_true h]
    apply foldr_and_true
    intro i _
    rw [h i]
    cases z (Fin.natAdd k i) <;> rfl
  · rw [eqHalves, decide_eq_false h]
    push_neg at h
    obtain ⟨i0, hi0⟩ := h
    apply foldr_and_false _ _ i0 (List.mem_finRange i0)
    cases hc : z (Fin.castAdd k i0) <;> cases hn : z (Fin.natAdd k i0) <;> simp_all

theorem eqProg_cost (hk : 0 < k) : (eqProg hk).cost = 3 + 5 * k := by
  unfold eqProg Prog.cost
  rw [List.length_append, List.length_flatMap]
  have h1 : (List.map (fun i : Fin k => (eqBlock i).length) (List.finRange k))
      = List.replicate k 5 := by
    have h2 : (fun i : Fin k => (eqBlock i).length) = Function.const (Fin k) 5 := rfl
    rw [h2, List.map_const, List.length_finRange]
  rw [h1, List.sum_replicate, smul_eq_mul, Nat.mul_comm]
  rfl

/-! ## The quadratic form `QF A` -/

/-- Per-pair block: for a live entry, AND the two bits and XOR into the accumulator; for a dead entry, XOR a
self-cancelling pair (a charged no-op — the step count stays uniform). -/
def qfBlock (A : Matrix (Fin n) (Fin n) (ZMod 2)) (p : Fin n × Fin n) : List (Gate n 3) :=
  if A p.1 p.2 = 1 then [.input p.1 1, .input p.2 2, .andg 1 2 1, .xorg 0 1 0]
  else [.input p.1 1, .input p.1 2, .xorg 1 2 1, .xorg 0 1 0]

theorem qfBlock_wire0 (A : Matrix (Fin n) (Fin n) (ZMod 2)) (z : Fin n → Bool)
    (p : Fin n × Fin n) (s : Fin 3 → Bool) :
    (runGates z (qfBlock A p) s) 0 = xor (s 0) (stepEval A z p) := by
  by_cases hA : A p.1 p.2 = 1
  · rw [qfBlock, if_pos hA]
    simp [runGates, step, Function.update, stepEval, hA]
  · rw [qfBlock, if_neg hA]
    have hst : stepEval A z p = false := by
      unfold stepEval
      rw [decide_eq_false hA]
      rfl
    rw [hst]
    simp [runGates, step, Function.update]

/-- The `QF A` program: `4n²` charged gates. -/
def qfProg (A : Matrix (Fin n) (Fin n) (ZMod 2)) : Prog n 3 :=
  ⟨(pairList n).flatMap (qfBlock A), 0⟩

/-- **Correctness**: the charged program computes the Boolean core of `QF A`. -/
theorem qfProg_correct (A : Matrix (Fin n) (Fin n) (ZMod 2)) (z : Fin n → Bool) :
    (qfProg A).run z = decide (qf A z = 1) := by
  unfold qfProg Prog.run
  rw [xorLoop_invariant z (stepEval A z) (qfBlock A) (qfBlock_wire0 A z) (pairList n) _,
    ← seqEval_correct]
  rfl

theorem qfProg_cost (A : Matrix (Fin n) (Fin n) (ZMod 2)) : (qfProg A).cost = 4 * n ^ 2 := by
  unfold qfProg Prog.cost
  rw [List.length_flatMap]
  have h1 : (List.map (fun p => (qfBlock A p).length) (pairList n))
      = List.replicate ((pairList n).length) 4 := by
    have h2 : (fun p => (qfBlock A p).length) = Function.const (Fin n × Fin n) 4 := by
      funext p
      unfold qfBlock
      split <;> rfl
    rw [h2, List.map_const]
  rw [h1, List.sum_replicate, smul_eq_mul, pairList_length, Nat.mul_comm]

/-- **The two-sided calibration, formal.**  One `A`: charged dynamic cost `4(2h)²` (this file) vs static all-order
MPS cost `≥ 2^r` (`QF_cost_all_orderings`).  Any later dynamic invariant must sit on the dynamic side. -/
theorem qf_dynamic_easy_static_hard {K : Type*} [Field K] [CharZero K] {h r : ℕ}
    (hh : 4 * r + 2 < h) :
    ∃ A : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2),
      ((qfProg A).cost = 4 * (2 * h) ^ 2 ∧ ∀ z, (qfProg A).run z = decide (qf A z = 1))
      ∧ (∀ (χ : ℕ) (M : PallLean.Paper93.DeepMath.PathB.MPSCost.MPS (2 * h) χ K)
          (σ : Equiv.Perm (Fin (2 * h))),
          PallLean.Paper93.DeepMath.PathB.OrderedMPS.evalOrd M (permOrder σ) = QF (K := K) A →
          2 ^ r ≤ M.cost) := by
  obtain ⟨A, hA⟩ := QF_cost_all_orderings (K := K) hh
  exact ⟨A, ⟨qfProg_cost A, fun z => qfProg_correct A z⟩, hA⟩

end PallLean.Paper93.DeepMath.PathB.ChargedCompiler

#print axioms PallLean.Paper93.DeepMath.PathB.ChargedCompiler.parityProg_correct
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedCompiler.eqProg_correct
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedCompiler.qfProg_correct
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedCompiler.qf_dynamic_easy_static_hard
