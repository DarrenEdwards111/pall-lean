import PallLean.Paper93.DeepMath.PathB.ComputationalDepthOrderedMPSBond

/-!
# The hostile calibration: `QF A` is sequentially EASY and statically (MPS) HARD

Steps (0) and (1) of the build map.  Two results about the *same* witness `A`:

* **All-order corollaries** (`QF_bond_all_orderings`, `QF_cost_all_orderings`) — every permutation ordering has a
  balanced prefix, so every MPS computing `QF A` in any permutation order has bond `≥ 2^r` and cost `≥ 2^r`
  (the permutation-phrased packaging of `OrderedMPS.QF_ordered_bond`/`QF_ordered_cost`);
* **The easy side** (`seqEval`, `seqEval_correct`, `pairList_length`) — a straight-line evaluator computing the
  Boolean core of `QF A` in exactly `(2h)²` constant-size steps (one AND-AND-XOR per matrix entry): `QF A` is a
  *quadratic-time* function.

`QF_easy_hard_calibration` packages both for one `A`.  **Consequence (the stop rule for later invariants):** static
tensor bond does NOT lower-bound sequential runtime — `QF A` has exponential all-order bond yet `O(n²)` sequential
cost.  Any later "dynamic cost" invariant must assign `QF A` polynomial cost, or it is measuring entanglement, not
time.  (This is why a dynamic invariant must use information *growth*, e.g. log Schmidt rank — polynomially many
gates can create exponential raw rank, as `QF A` shows.)

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.QFEasyHard

open Matrix
open PallLean.Paper93.DeepMath.PathB.MPSCost
open PallLean.Paper93.DeepMath.PathB.GlobalResidual
open PallLean.Paper93.DeepMath.PathB.GlobalBestPartitionBond
open PallLean.Paper93.DeepMath.PathB.OrderedMPS

variable {K : Type*} [Field K] [CharZero K] {n h r : ℕ}

/-! ## Step (0): permutation-phrased all-order corollaries -/

/-- The site order induced by a permutation. -/
def permOrder (σ : Equiv.Perm (Fin n)) : List (Fin n) := (List.finRange n).map σ

theorem permOrder_nodup (σ : Equiv.Perm (Fin n)) : (permOrder σ).Nodup :=
  (List.nodup_finRange n).map σ.injective

theorem permOrder_length (σ : Equiv.Perm (Fin n)) : (permOrder σ).length = n := by
  rw [permOrder, List.length_map, List.length_finRange]

/-- **Every permutation ordering forces bond `≥ 2^r`.** -/
theorem QF_bond_all_orderings (hh : 4 * r + 2 < h) :
    ∃ A : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2),
      ∀ (χ : ℕ) (M : MPS (2 * h) χ K) (σ : Equiv.Perm (Fin (2 * h))),
        evalOrd M (permOrder σ) = QF (K := K) A → 2 ^ r ≤ χ := by
  obtain ⟨A, hA⟩ := QF_ordered_bond (K := K) hh
  exact ⟨A, fun χ M σ hM =>
    hA χ M (permOrder σ) (permOrder_nodup σ) (by rw [permOrder_length]; omega) hM⟩

/-- **Every permutation ordering forces cost `≥ 2^r`** — the all-order exponential representation-cost bound. -/
theorem QF_cost_all_orderings (hh : 4 * r + 2 < h) :
    ∃ A : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2),
      ∀ (χ : ℕ) (M : MPS (2 * h) χ K) (σ : Equiv.Perm (Fin (2 * h))),
        evalOrd M (permOrder σ) = QF (K := K) A → 2 ^ r ≤ M.cost := by
  obtain ⟨A, hA⟩ := QF_ordered_cost (K := K) hh
  exact ⟨A, fun χ M σ hM =>
    hA χ M (permOrder σ) (permOrder_nodup σ) (by rw [permOrder_length]; omega) hM⟩

/-! ## Step (1): the easy side — a `(2h)²`-step sequential evaluator -/

/-- The list of all index pairs (the evaluator's step sequence). -/
def pairList (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap (fun i => (List.finRange n).map (fun j => (i, j)))

/-- One constant-size step: `A[i][j] AND z i AND z j`. -/
def stepEval (A : Matrix (Fin n) (Fin n) (ZMod 2)) (z : Fin n → Bool) (p : Fin n × Fin n) : Bool :=
  decide (A p.1 p.2 = 1) && z p.1 && z p.2

/-- **The sequential evaluator**: XOR-fold of the `(2h)²` steps. -/
def seqEval (A : Matrix (Fin n) (Fin n) (ZMod 2)) (z : Fin n → Bool) : Bool :=
  (pairList n).foldr (fun p acc => xor (stepEval A z p) acc) false

/-- The evaluator has exactly `n²` steps. -/
theorem pairList_length (n : ℕ) : (pairList n).length = n ^ 2 := by
  rw [pairList, List.length_flatMap]
  have hmap : (List.map (fun i => (List.map (fun j => (i, j)) (List.finRange n)).length)
      (List.finRange n)) = List.replicate n n := by
    have h1 : (fun i : Fin n => (List.map (fun j => (i, j)) (List.finRange n)).length)
        = Function.const (Fin n) n := by
      funext i; rw [Function.const_apply, List.length_map, List.length_finRange]
    rw [h1, List.map_const, List.length_finRange]
  rw [hmap, List.sum_replicate, smul_eq_mul, pow_two]

/-- Bool-step / `ZMod 2`-term agreement. -/
theorem bit_stepEval (A : Matrix (Fin n) (Fin n) (ZMod 2)) (z : Fin n → Bool) (p : Fin n × Fin n) :
    bit (stepEval A z p) = A p.1 p.2 * bit (z p.1) * bit (z p.2) := by
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (A p.1 p.2) with hA | hA <;>
    cases hz1 : z p.1 <;> cases hz2 : z p.2 <;>
    simp [stepEval, bit, hA, hz1, hz2]

/-- XOR-fold computes the parity (`decide (sum = 1)`) of the `ZMod 2` terms. -/
theorem foldr_xor_eq_decide (z : Fin n → Bool) (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (l : List (Fin n × Fin n)) :
    l.foldr (fun p acc => xor (stepEval A z p) acc) false
      = decide ((l.map (fun p => A p.1 p.2 * bit (z p.1) * bit (z p.2))).sum = 1) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.foldr_cons, List.map_cons, List.sum_cons, ih, ← bit_stepEval]
    generalize (List.map (fun p => A p.1 p.2 * bit (z p.1) * bit (z p.2)) l).sum = s
    cases hb : stepEval A z p <;>
      rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) s with hs | hs <;> subst hs <;> decide

/-- Helper: the flatMap sum over an arbitrary outer list. -/
theorem flatMap_sum (A : Matrix (Fin n) (Fin n) (ZMod 2)) (z : Fin n → Bool)
    (lo : List (Fin n)) :
    ((lo.flatMap (fun i => (List.finRange n).map (fun j => (i, j)))).map
        (fun p => A p.1 p.2 * bit (z p.1) * bit (z p.2))).sum
      = (lo.map (fun i => ∑ j, A i j * bit (z i) * bit (z j))).sum := by
  induction lo with
  | nil => simp
  | cons i lo ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]
    congr 1
    rw [Fin.sum_univ_def, List.map_map]
    rfl

/-- The pair-list sum equals the double Finset sum `qf`. -/
theorem pairList_sum_eq_qf (A : Matrix (Fin n) (Fin n) (ZMod 2)) (z : Fin n → Bool) :
    ((pairList n).map (fun p => A p.1 p.2 * bit (z p.1) * bit (z p.2))).sum = qf A z := by
  unfold qf pairList
  rw [flatMap_sum, ← Fin.sum_univ_def]

/-- **Correctness**: the `(2h)²`-step evaluator computes the Boolean core of `QF A`. -/
theorem seqEval_correct (A : Matrix (Fin n) (Fin n) (ZMod 2)) (z : Fin n → Bool) :
    seqEval A z = decide (qf A z = 1) := by
  rw [seqEval, foldr_xor_eq_decide, pairList_sum_eq_qf]

/-- `QF A` is the `±1` encoding of the evaluator's output. -/
theorem QF_eq_seqEval (A : Matrix (Fin n) (Fin n) (ZMod 2)) (z : Fin n → Bool) :
    QF (K := K) A z = if seqEval A z then (-1 : K) else 1 := by
  rw [seqEval_correct]
  unfold QF sgn
  rcases hq : decide (qf A z = 1) <;> simp_all

/-! ## The calibration: easy and hard for the SAME `A` -/

/-- **The hostile calibration.**  One `A` for which: (easy) the Boolean core of `QF A` is computed by a
straight-line evaluator with `(2h)²` constant-size steps; (hard) every MPS computing `QF A` in every permutation
order has cost `≥ 2^r = 2^{Ω(n)}`.  Hence static tensor bond/cost does not lower-bound sequential runtime; any
later dynamic invariant must assign `QF A` polynomial cost. -/
theorem QF_easy_hard_calibration (hh : 4 * r + 2 < h) :
    ∃ A : Matrix (Fin (2 * h)) (Fin (2 * h)) (ZMod 2),
      (∀ z, seqEval A z = decide (qf A z = 1))
      ∧ (pairList (2 * h)).length = (2 * h) ^ 2
      ∧ (∀ (χ : ℕ) (M : MPS (2 * h) χ K) (σ : Equiv.Perm (Fin (2 * h))),
          evalOrd M (permOrder σ) = QF (K := K) A → 2 ^ r ≤ M.cost) := by
  obtain ⟨A, hA⟩ := QF_cost_all_orderings (K := K) hh
  exact ⟨A, fun z => seqEval_correct A z, pairList_length (2 * h), hA⟩

end PallLean.Paper93.DeepMath.PathB.QFEasyHard

#print axioms PallLean.Paper93.DeepMath.PathB.QFEasyHard.QF_bond_all_orderings
#print axioms PallLean.Paper93.DeepMath.PathB.QFEasyHard.seqEval_correct
#print axioms PallLean.Paper93.DeepMath.PathB.QFEasyHard.QF_easy_hard_calibration
