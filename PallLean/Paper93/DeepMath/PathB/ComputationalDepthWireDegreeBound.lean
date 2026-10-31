import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDegreeCalculus
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAffineOutput

/-!
# Step (a): the per-circuit degree bound `wire-degree ≤ 2^{#nonlinear gates}`

Threading the `DegreeCalculus` engine through the straight-line evaluation: every wire of a `CGate`
circuit has GF(2)-degree at most `2^{nlCount c}`, where `nlCount c` counts the gates that are *not*
affine.  Hence the output does too — so a circuit computing a degree-`D` function needs at least
`log₂ D` nonlinear gates.

* **`affineGateB` / `nlCount`** — the (Bool) affine-gate test and the nonlinear-gate count.
* **`nlCount_append_singleton` (proved)** — appending a gate adds `0` (affine) or `1` (nonlinear).
* **`wire_degLe` (proved)** — every wire has degree `≤ 2^{nlCount c}` (reverse induction: inherited
  wires by IH + monotonicity; a new **affine** gate keeps the degree (`isDegLe_op_affine`/`_unary`,
  `nlCount` unchanged); a new **nonlinear** gate at most doubles it (`isDegLe_op`, `nlCount` up by one,
  `2·2^k = 2^{k+1}`)).
* **`output_degLe` (proved)** — the output has degree `≤ 2^{nlCount c}`.
* **`nlCount_ge_of_degree` (proved)** — contrapositive: if `output c` is not of degree `≤ 2^m`, the
  circuit has more than `m` nonlinear gates.

**Honest scope.**  A real, unconditional lower bound on the *nonlinear-gate count* in terms of degree —
the base machinery of the Uhlig programme.  But it is only **logarithmic** (`log₂ D`), and bounds the
nonlinear-gate *count*, not the total gate count `NonlinearHorn` needs.  The full Uhlig no-sharing bound
that `cost_super` requires remains the open wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.WireDegreeBound

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.CostSuperDichotomy
open PallLean.Paper93.DeepMath.PathB.DegreeCalculus
open PallLean.Paper93.DeepMath.PathB.AffineOutput

variable {n : ℕ}

/-- Bool test: is a gate affine?  (`var`/`cst`/`un` always; `bin op` iff `op` is affine.) -/
def affineGateB : CGate n → Bool
  | .var _ => true
  | .cst _ => true
  | .un _ _ => true
  | .bin op _ _ =>
      !(Bool.xor (Bool.xor (op false false) (op false true)) (Bool.xor (op true false) (op true true)))

/-- A `bin` gate flagged affine really has an affine op. -/
theorem isAffineOp_of_affineGateB {op : Bool → Bool → Bool} {j k : ℕ}
    (h : affineGateB (CGate.bin op j k : CGate n) = true) : IsAffineOp op := by
  simp only [affineGateB, Bool.not_eq_true', Bool.not_eq_false] at h
  exact h

/-- The number of non-affine (nonlinear) gates in a circuit. -/
def nlCount (c : List (CGate n)) : ℕ := c.countP (fun g => !(affineGateB g))

/-- Appending a gate adds `0` (affine) or `1` (nonlinear) to the nonlinear count. -/
theorem nlCount_append_singleton (c : List (CGate n)) (g : CGate n) :
    nlCount (c ++ [g]) = nlCount c + (if affineGateB g then 0 else 1) := by
  simp only [nlCount, List.countP_append, List.countP_cons, List.countP_nil, Nat.zero_add]
  cases affineGateB g <;> simp

/-- Appending an affine gate leaves the nonlinear count unchanged. -/
theorem nlCount_append_affine (c : List (CGate n)) (g : CGate n) (h : affineGateB g = true) :
    nlCount (c ++ [g]) = nlCount c := by
  rw [nlCount_append_singleton, h]; simp

/-- Appending a nonlinear gate raises the nonlinear count by one. -/
theorem nlCount_append_nonaffine (c : List (CGate n)) (g : CGate n) (h : affineGateB g = false) :
    nlCount (c ++ [g]) = nlCount c + 1 := by
  rw [nlCount_append_singleton, h]; simp

/-- **Every wire has GF(2)-degree ≤ `2^{nlCount c}` (proved).** -/
theorem wire_degLe :
    ∀ (c : List (CGate n)) (j : ℕ),
      IsDegLe (2 ^ nlCount c) (fun x => (runFrom x [] c).getD j false) := by
  intro c
  induction c using List.reverseRecOn with
  | nil =>
    intro j
    have h0 : (fun x : Fin n → Bool => (runFrom x [] ([] : List (CGate n))).getD j false)
            = fun _ => false := by funext x; rfl
    rw [h0]; exact isDegLe_const _ false
  | append_singleton c' g ih =>
    intro j
    have hrun : ∀ x : Fin n → Bool,
        runFrom x [] (c' ++ [g]) = runFrom x [] c' ++ [evalGate x (runFrom x [] c') g] := by
      intro x; rw [runFrom_append]; simp [runFrom]
    have hlen : ∀ x : Fin n → Bool, (runFrom x [] c').length = c'.length := by
      intro x; rw [runFrom_length x c' []]; simp
    have hmono : nlCount c' ≤ nlCount (c' ++ [g]) := by
      rw [nlCount_append_singleton]; omega
    rcases lt_trichotomy j c'.length with hj | hj | hj
    · -- inherited wire
      have heq : (fun x => (runFrom x [] (c' ++ [g])).getD j false)
               = fun x => (runFrom x [] c').getD j false := by
        funext x
        rw [hrun x, List.getD_append _ _ _ _ (by rw [hlen x]; exact hj)]
      rw [heq]
      exact isDegLe_mono_le (Nat.pow_le_pow_right (by norm_num) hmono) _ (ih j)
    · -- new gate output
      subst hj
      have heq : (fun x => (runFrom x [] (c' ++ [g])).getD c'.length false)
               = fun x => evalGate x (runFrom x [] c') g := by
        funext x; rw [hrun x, ← hlen x, getD_concat]
      rw [heq]
      cases g with
      | var i =>
        rw [nlCount_append_affine c' (CGate.var i) (by rfl)]
        simp only [evalGate]
        exact isDegLe_mono_le Nat.one_le_two_pow _ (isDegLe_var i)
      | cst b =>
        rw [nlCount_append_affine c' (CGate.cst b) (by rfl)]
        simp only [evalGate]
        exact isDegLe_const _ b
      | un op k =>
        rw [nlCount_append_affine c' (CGate.un op k) (by rfl)]
        simp only [evalGate]
        exact isDegLe_unary op _ _ (ih k)
      | bin op k l =>
        cases hb : affineGateB (CGate.bin op k l : CGate n) with
        | true =>
          rw [nlCount_append_affine c' (CGate.bin op k l) hb]
          simp only [evalGate]
          exact isDegLe_op_affine (isAffineOp_of_affineGateB hb) _ _ _ (ih k) (ih l)
        | false =>
          rw [nlCount_append_nonaffine c' (CGate.bin op k l) hb]
          simp only [evalGate]
          have hdbl : (2 : ℕ) ^ (nlCount c' + 1) = 2 ^ nlCount c' + 2 ^ nlCount c' := by
            rw [pow_succ]; ring
          rw [hdbl]
          exact isDegLe_op op _ _ _ _ (ih k) (ih l)
    · -- past the end: default false
      have heq : (fun x => (runFrom x [] (c' ++ [g])).getD j false)
               = fun _ : Fin n → Bool => false := by
        funext x
        rw [hrun x]
        apply List.getD_eq_default
        rw [List.length_append, hlen x, List.length_singleton]
        omega
      rw [heq]; exact isDegLe_const _ false

/-- **The output has GF(2)-degree ≤ `2^{nlCount c}` (proved).** -/
theorem output_degLe (c : List (CGate n)) : IsDegLe (2 ^ nlCount c) (output c) :=
  wire_degLe c (c.length - 1)

/-- **Contrapositive (proved): high degree forces many nonlinear gates.**  If the output is not of
degree `≤ 2^m`, then the circuit has more than `m` nonlinear gates. -/
theorem nlCount_ge_of_degree (c : List (CGate n)) (m : ℕ)
    (hdeg : ¬ IsDegLe (2 ^ m) (output c)) : m < nlCount c := by
  by_contra h
  push_neg at h
  exact hdeg (isDegLe_mono_le (Nat.pow_le_pow_right (by norm_num) h) _ (output_degLe c))

end PallLean.Paper93.DeepMath.PathB.WireDegreeBound

#print axioms PallLean.Paper93.DeepMath.PathB.WireDegreeBound.wire_degLe
#print axioms PallLean.Paper93.DeepMath.PathB.WireDegreeBound.output_degLe
#print axioms PallLean.Paper93.DeepMath.PathB.WireDegreeBound.nlCount_ge_of_degree
