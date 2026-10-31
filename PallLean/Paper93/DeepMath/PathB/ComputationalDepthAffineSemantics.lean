import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCostSuperDichotomy

/-!
# Rigidity teeth: the affine class is closed under exactly the affine-gate operations

`CostSuperDichotomy` classified gates syntactically (`IsAffineOp`).  This file supplies the *semantic*
justification the fuzzy plan flagged as load-bearing: the class of GF(2)-**affine functions** is closed
under precisely the operations an affine gate performs — constants, projections, unary ops, and affine
binary ops.  Hence an affine-mixed circuit computes an affine function, so the linear horn really is
the GF(2)-linear / **matrix-rigidity** regime (Valiant), not a mere syntactic tag.

A function is affine iff its 3-fold second difference vanishes:
`φx ⊕ φy ⊕ φz = φ(x ⊕ y ⊕ z)` (equivalently `φ(x) = a ⊕ linear(x)`).

* **`isAffineFn_const` / `isAffineFn_proj` (proved)** — constants and input projections are affine.
* **`op_affine_decomp` (proved)** — an affine binary op is its ANF `op a b = op₀₀ ⊕ (a ∧ k₁) ⊕ (b ∧ k₂)`.
* **`isAffineFn_xor` / `isAffineFn_andConst` (proved)** — the affine class is closed under `⊕` and
  under `∧` with a constant.
* **`isAffineFn_bin` (proved)** — closure under any affine binary op (via the ANF decomposition).
* **`isAffineFn_unary` (proved)** — closure under any unary op (all `1`-bit ops are affine).

**Honest scope.**  These are the per-gate closure facts: the affine class is preserved by exactly what
an affine gate does.  They give the linear horn its rigidity teeth.  The full statement "an
affine-mixed circuit's *output* is affine" is these composed along the straight-line evaluation
(`runFrom`) — mechanical list-index threading, not included here.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.AffineSemantics

open PallLean.Paper93.DeepMath.PathB.CostSuperDichotomy

variable {n : ℕ}

/-- A Boolean function of the inputs is **GF(2)-affine** iff its 3-fold second difference vanishes. -/
def IsAffineFn (φ : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y z : Fin n → Bool,
    Bool.xor (Bool.xor (φ x) (φ y)) (φ z)
      = φ (fun i => Bool.xor (Bool.xor (x i) (y i)) (z i))

/-- Constants are affine. -/
theorem isAffineFn_const (b : Bool) : IsAffineFn (fun _ : Fin n → Bool => b) := by
  intro x y z; cases b <;> rfl

/-- Input projections are affine. -/
theorem isAffineFn_proj (i : Fin n) : IsAffineFn (fun x : Fin n → Bool => x i) := by
  intro x y z; rfl

/-- The affine class is closed under XOR. -/
theorem isAffineFn_xor {φ ψ : (Fin n → Bool) → Bool} (hφ : IsAffineFn φ) (hψ : IsAffineFn ψ) :
    IsAffineFn (fun x => Bool.xor (φ x) (ψ x)) := by
  intro x y z
  dsimp only
  rw [← hφ x y z, ← hψ x y z]
  cases φ x <;> cases φ y <;> cases φ z <;> cases ψ x <;> cases ψ y <;> cases ψ z <;> decide

/-- An **affine binary op** is its ANF: `op a b = op₀₀ ⊕ (a ∧ (op₀₀ ⊕ op₁₀)) ⊕ (b ∧ (op₀₀ ⊕ op₀₁))`. -/
theorem op_affine_decomp {op : Bool → Bool → Bool} (hop : IsAffineOp op) (a b : Bool) :
    op a b = Bool.xor (Bool.xor (op false false)
        (Bool.and a (Bool.xor (op false false) (op true false))))
        (Bool.and b (Bool.xor (op false false) (op false true))) := by
  revert hop
  unfold IsAffineOp
  cases a <;> cases b <;>
    cases op false false <;> cases op false true <;> cases op true false <;> cases op true true <;>
    decide

/-- The affine class is closed under AND with a constant. -/
theorem isAffineFn_andConst {φ : (Fin n → Bool) → Bool} (hφ : IsAffineFn φ) (c : Bool) :
    IsAffineFn (fun x => Bool.and (φ x) c) := by
  cases c
  · simp only [Bool.and_false]; exact isAffineFn_const false
  · simp only [Bool.and_true]; exact hφ

/-- The affine class is closed under any **affine binary op** — the key closure for the linear horn. -/
theorem isAffineFn_bin {op : Bool → Bool → Bool} (hop : IsAffineOp op)
    {φ ψ : (Fin n → Bool) → Bool} (hφ : IsAffineFn φ) (hψ : IsAffineFn ψ) :
    IsAffineFn (fun x => op (φ x) (ψ x)) := by
  have hrw : (fun x => op (φ x) (ψ x))
      = fun x => Bool.xor (Bool.xor (op false false)
          (Bool.and (φ x) (Bool.xor (op false false) (op true false))))
          (Bool.and (ψ x) (Bool.xor (op false false) (op false true))) := by
    funext x; exact op_affine_decomp hop (φ x) (ψ x)
  rw [hrw]
  exact isAffineFn_xor
    (isAffineFn_xor (isAffineFn_const _) (isAffineFn_andConst hφ _))
    (isAffineFn_andConst hψ _)

/-- The affine class is closed under any **unary op** (all `1`-bit functions are affine). -/
theorem isAffineFn_unary (op : Bool → Bool) {φ : (Fin n → Bool) → Bool} (hφ : IsAffineFn φ) :
    IsAffineFn (fun x => op (φ x)) := by
  have hrw : (fun x => op (φ x))
      = fun x => Bool.xor (op false) (Bool.and (φ x) (Bool.xor (op false) (op true))) := by
    funext x; cases φ x <;> cases op false <;> cases op true <;> decide
  rw [hrw]
  exact isAffineFn_xor (isAffineFn_const _) (isAffineFn_andConst hφ _)

end PallLean.Paper93.DeepMath.PathB.AffineSemantics

#print axioms PallLean.Paper93.DeepMath.PathB.AffineSemantics.isAffineFn_bin
#print axioms PallLean.Paper93.DeepMath.PathB.AffineSemantics.isAffineFn_unary
#print axioms PallLean.Paper93.DeepMath.PathB.AffineSemantics.op_affine_decomp
