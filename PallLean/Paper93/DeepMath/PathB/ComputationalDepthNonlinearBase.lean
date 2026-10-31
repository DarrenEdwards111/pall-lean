import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAffineSemantics

/-!
# Attacking `NonlinearHorn`: one nonlinear gate on affine inputs is GF(2)-degree ≤ 2

`HornCollapse` reduced the SAT wall to `NonlinearHorn` (circuits with a nonlinear gate).  The Uhlig
lower bound is proven by induction on the number of nonlinear gates; this file builds the **degree
layer** that powers its base case.  Degree is tracked recursively: `F` has GF(2)-degree `≤ 2` iff every
first finite difference `Δ_a F(x) = F(x) ⊕ F(x⊕a)` is **affine** (degree `≤ 1`, the `IsAffineFn` class).

* **`op_anf` (proved, axiom-free)** — the algebraic normal form of *any* binary op:
  `op a b = c₀ ⊕ (c₁∧a) ⊕ (c₂∧b) ⊕ (c₃∧a∧b)`.
* **`affine_shift` (proved)** — for an affine `F`, shifting the input is an affine correction:
  `F(x⊕a) = F(x) ⊕ (F(a) ⊕ F(0))`.
* **`isDegLe2_of_affine` (proved)** — affine ⟹ degree `≤ 2` (a first difference of an affine function
  is *constant*).
* **`degLe2_of_op_affine` (proved)** — **the base-case core**: for affine `φ, ψ` and *any* op (nonlinear
  allowed), `op(φ,ψ)` has degree `≤ 2`.  A single nonlinear gate fed by affine wires produces at most a
  quadratic — one nonlinear gate cannot manufacture high degree.  Proof: `Δ_a[op(φ,ψ)]` expands via the
  ANF and the affine shifts into `(c₃∧dψ)·φ ⊕ (c₃∧dφ)·ψ ⊕ const`, manifestly affine (`dφ, dψ` the
  constant input-differences), closed by the `AffineSemantics` lemmas.

**Honest scope.**  This is the degree engine for the base case: `0` nonlinear gates ⟹ degree `≤ 1`
(`AffineOutput`), and now one nonlinear gate on affine inputs ⟹ degree `≤ 2`.  Threading it through a
whole circuit (every wire's degree ≤ `2^{nonlinear-count}`) and instantiating "SAT has high degree" are
the next steps; `NonlinearHorn` for SAT — the full Uhlig bound — remains the open wall.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NonlinearBase

open PallLean.Paper93.DeepMath.PathB.AffineSemantics

variable {n : ℕ}

/-- **Algebraic normal form of a binary op (proved, axiom-free).** -/
theorem op_anf (op : Bool → Bool → Bool) (a b : Bool) :
    op a b = Bool.xor (Bool.xor (Bool.xor (op false false)
        (Bool.and (Bool.xor (op false false) (op true false)) a))
        (Bool.and (Bool.xor (op false false) (op false true)) b))
        (Bool.and (Bool.xor (Bool.xor (Bool.xor (op false false) (op false true)) (op true false))
          (op true true)) (Bool.and a b)) := by
  cases a <;> cases b <;>
    cases op false false <;> cases op false true <;> cases op true false <;> cases op true true <;>
    decide

/-- **Degree ≤ 2**: every first finite difference `Δ_a F` is affine. -/
def IsDegLe2 (F : (Fin n → Bool) → Bool) : Prop :=
  ∀ a : Fin n → Bool, IsAffineFn (fun x => Bool.xor (F x) (F (fun i => Bool.xor (x i) (a i))))

/-- **Shifting the input of an affine function is an affine (constant) correction (proved).** -/
theorem affine_shift {F : (Fin n → Bool) → Bool} (hF : IsAffineFn F) (a x : Fin n → Bool) :
    F (fun i => Bool.xor (x i) (a i))
      = Bool.xor (F x) (Bool.xor (F a) (F (fun _ => false))) := by
  have h := hF x a (fun _ => false)
  simp only [Bool.xor_false] at h
  rw [← h, Bool.xor_assoc]

/-- **Affine ⟹ degree ≤ 2 (proved).**  A first difference of an affine function is constant. -/
theorem isDegLe2_of_affine {F : (Fin n → Bool) → Bool} (hF : IsAffineFn F) : IsDegLe2 F := by
  intro a
  have hcst : (fun x => Bool.xor (F x) (F (fun i => Bool.xor (x i) (a i))))
            = fun _ => Bool.xor (F a) (F (fun _ => false)) := by
    funext x
    rw [affine_shift hF a x]
    cases F x <;> simp
  rw [hcst]; exact isAffineFn_const _

/-- **THE BASE-CASE CORE (proved).**  For affine `φ, ψ` and *any* binary op, `op(φ,ψ)` has degree ≤ 2:
one nonlinear gate on affine inputs produces at most a quadratic. -/
theorem degLe2_of_op_affine {op : Bool → Bool → Bool} {φ ψ : (Fin n → Bool) → Bool}
    (hφ : IsAffineFn φ) (hψ : IsAffineFn ψ) :
    IsDegLe2 (fun x => op (φ x) (ψ x)) := by
  intro a
  -- `Δ_a[op(φ,ψ)]` in manifestly-affine form: `(c₃∧dψ)·φ ⊕ (c₃∧dφ)·ψ ⊕ const`
  have hfun : (fun x => Bool.xor (op (φ x) (ψ x))
                (op (φ (fun i => Bool.xor (x i) (a i))) (ψ (fun i => Bool.xor (x i) (a i)))))
            = fun x => Bool.xor (Bool.xor
                (Bool.and (φ x)
                  (Bool.and (Bool.xor (Bool.xor (Bool.xor (op false false) (op false true))
                    (op true false)) (op true true)) (Bool.xor (ψ a) (ψ (fun _ => false)))))
                (Bool.and (ψ x)
                  (Bool.and (Bool.xor (Bool.xor (Bool.xor (op false false) (op false true))
                    (op true false)) (op true true)) (Bool.xor (φ a) (φ (fun _ => false))))))
                (Bool.xor (Bool.xor
                  (Bool.and (Bool.xor (op false false) (op true false))
                    (Bool.xor (φ a) (φ (fun _ => false))))
                  (Bool.and (Bool.xor (op false false) (op false true))
                    (Bool.xor (ψ a) (ψ (fun _ => false)))))
                  (Bool.and (Bool.and (Bool.xor (Bool.xor (Bool.xor (op false false) (op false true))
                    (op true false)) (op true true)) (Bool.xor (φ a) (φ (fun _ => false))))
                    (Bool.xor (ψ a) (ψ (fun _ => false))))) := by
    funext x
    rw [affine_shift hφ a x, affine_shift hψ a x, op_anf op (φ x) (ψ x),
      op_anf op (Bool.xor (φ x) (Bool.xor (φ a) (φ (fun _ => false))))
        (Bool.xor (ψ x) (Bool.xor (ψ a) (ψ (fun _ => false))))]
    cases φ x <;> cases ψ x <;> cases φ a <;> cases ψ a <;>
      cases φ (fun _ => false) <;> cases ψ (fun _ => false) <;>
      cases op false false <;> cases op false true <;> cases op true false <;> cases op true true <;>
      decide
  rw [hfun]
  exact isAffineFn_xor
    (isAffineFn_xor (isAffineFn_andConst hφ _) (isAffineFn_andConst hψ _))
    (isAffineFn_const _)

end PallLean.Paper93.DeepMath.PathB.NonlinearBase

#print axioms PallLean.Paper93.DeepMath.PathB.NonlinearBase.op_anf
#print axioms PallLean.Paper93.DeepMath.PathB.NonlinearBase.isDegLe2_of_affine
#print axioms PallLean.Paper93.DeepMath.PathB.NonlinearBase.degLe2_of_op_affine
