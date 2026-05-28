import Mathlib

/-!
# Genuine cutting-planes substrate: integer inequalities and rank

This file replaces the abstract rung-3 cutting-planes `{ resource : Nat }`
placeholder with an actual syntactic cutting-planes object:

* a line is an integer linear inequality `rhs ≤ ∑ i, coeff i * x_i`;
* derivations contain real cutting-planes rules: axioms, addition,
  nonnegative scaling, and a Chvátal-style division step;
* the resource is rank: axioms/addition/scaling do not increase rank, while a
  Chvátal division increases rank by one;
* rank is bounded by tree size, hence a rank lower bound rules out small
  tree-like cutting-planes derivations.

Scope: this is a genuine inequality/rank model, not a proof of Tseitin/PHP
cutting-planes lower bounds.  The Chvátal rule is included syntactically with
the divisibility witness that identifies the divided coefficients.  Full semantic
soundness of the division rule and family-specific lower bounds are separate
formalization targets.
-/

namespace PallLean.Paper93.DeepMath.PathB

set_option linter.unusedSectionVars false

open scoped BigOperators

universe u

variable {σ : Type u} [Fintype σ]

/-- An integer linear inequality `rhs ≤ ∑ i, coeff i * x_i`. -/
structure CuttingPlanesLine (σ : Type u) where
  coeff : σ -> Int
  rhs : Int

namespace CuttingPlanesLine

variable [Fintype σ]

/-- Evaluate the left linear form on an integer assignment. -/
noncomputable def eval (L : CuttingPlanesLine σ) (x : σ -> Int) : Int :=
  ∑ i, L.coeff i * x i

/-- Semantic satisfaction of a cutting-planes inequality. -/
def Satisfied (L : CuttingPlanesLine σ) (x : σ -> Int) : Prop :=
  L.rhs <= L.eval x

/-- Add two inequalities. -/
def add (L M : CuttingPlanesLine σ) : CuttingPlanesLine σ where
  coeff := fun i => L.coeff i + M.coeff i
  rhs := L.rhs + M.rhs

/-- Multiply an inequality by a natural nonnegative scalar. -/
def scale (k : Nat) (L : CuttingPlanesLine σ) : CuttingPlanesLine σ where
  coeff := fun i => (k : Int) * L.coeff i
  rhs := (k : Int) * L.rhs

/-- A Chvátal-style division line: if all coefficients of `L` are divisible by
`k`, replace them by the provided quotients and divide the right-hand side using
integer division.  The derivation rule below carries the divisibility equality
`L.coeff i = k * coeff' i` as an explicit witness. -/
def chvatalDiv (k : Nat) (L : CuttingPlanesLine σ) (coeff' : σ -> Int) :
    CuttingPlanesLine σ where
  coeff := coeff'
  rhs := L.rhs / (k : Int)

@[simp] theorem add_rhs (L M : CuttingPlanesLine σ) :
    (add L M).rhs = L.rhs + M.rhs :=
  rfl

@[simp] theorem scale_rhs (k : Nat) (L : CuttingPlanesLine σ) :
    (scale k L).rhs = (k : Int) * L.rhs :=
  rfl

/-- Addition is semantically sound. -/
theorem add_satisfied {L M : CuttingPlanesLine σ} {x : σ -> Int}
    (hL : L.Satisfied x) (hM : M.Satisfied x) :
    (add L M).Satisfied x := by
  unfold Satisfied eval add at *
  calc
    L.rhs + M.rhs <= (∑ i, L.coeff i * x i) + (∑ i, M.coeff i * x i) :=
      add_le_add hL hM
    _ = ∑ i, (L.coeff i + M.coeff i) * x i := by
      simp [add_mul, Finset.sum_add_distrib]

/-- Nonnegative scaling is semantically sound. -/
theorem scale_satisfied {L : CuttingPlanesLine σ} {x : σ -> Int}
    (k : Nat) (hL : L.Satisfied x) :
    (scale k L).Satisfied x := by
  unfold Satisfied eval scale at *
  calc
    (k : Int) * L.rhs <= (k : Int) * (∑ i, L.coeff i * x i) :=
      Int.mul_le_mul_of_nonneg_left hL (Int.natCast_nonneg k)
    _ = ∑ i, ((k : Int) * L.coeff i) * x i := by
      simp [Finset.mul_sum, mul_assoc]

end CuttingPlanesLine

/-! ## Cutting-planes derivations and rank -/

/-- Tree-like cutting-planes derivations over actual integer inequalities.

The Chvátal step carries a positive divisor and a coefficient quotient witness;
its child line is `chvatalDiv`. -/
inductive CuttingPlanesDerivation
    (Axiom : CuttingPlanesLine σ -> Prop) :
    CuttingPlanesLine σ -> Type (u + 1) where
  | ax {L : CuttingPlanesLine σ} :
      Axiom L -> CuttingPlanesDerivation Axiom L
  | add {L M : CuttingPlanesLine σ} :
      CuttingPlanesDerivation Axiom L ->
      CuttingPlanesDerivation Axiom M ->
      CuttingPlanesDerivation Axiom (CuttingPlanesLine.add L M)
  | scale {L : CuttingPlanesLine σ} (k : Nat) :
      CuttingPlanesDerivation Axiom L ->
      CuttingPlanesDerivation Axiom (CuttingPlanesLine.scale k L)
  | chvatal {L : CuttingPlanesLine σ}
      (k : Nat) (hk : 0 < k) (coeff' : σ -> Int)
      (hcoeff : forall i : σ, L.coeff i = (k : Int) * coeff' i) :
      CuttingPlanesDerivation Axiom L ->
      CuttingPlanesDerivation Axiom (CuttingPlanesLine.chvatalDiv k L coeff')

namespace CuttingPlanesDerivation

variable {Axiom : CuttingPlanesLine σ -> Prop}

/-- Tree size of a cutting-planes derivation. -/
def size {L : CuttingPlanesLine σ}
    (D : CuttingPlanesDerivation Axiom L) : Nat :=
  match D with
  | ax _ => 1
  | add D E => size D + size E + 1
  | scale _ D => size D + 1
  | chvatal _ _ _ _ D => size D + 1

/-- Chvátal rank of a cutting-planes derivation.  Addition and scaling preserve
rank; Chvátal division increases it by one. -/
def rank {L : CuttingPlanesLine σ}
    (D : CuttingPlanesDerivation Axiom L) : Nat :=
  match D with
  | ax _ => 0
  | add D E => max (rank D) (rank E)
  | scale _ D => rank D
  | chvatal _ _ _ _ D => rank D + 1

/-- Cutting-planes rank is bounded by tree size. -/
theorem rank_le_size {L : CuttingPlanesLine σ}
    (D : CuttingPlanesDerivation Axiom L) :
    D.rank <= D.size := by
  induction D with
  | ax _ => simp [rank, size]
  | add D E ihD ihE =>
      simp [rank, size]
      constructor
      · omega
      · omega
  | scale k D ih =>
      simp [rank, size]
      omega
  | chvatal k hk coeff' hcoeff D ih =>
      simp [rank, size]
      omega

end CuttingPlanesDerivation

/-- A genuine cutting-planes rank lower bound for deriving `Target`. -/
def CuttingPlanesRankLowerBound
    (Axiom : CuttingPlanesLine σ -> Prop)
    (Target : CuttingPlanesLine σ)
    (r : Nat) : Prop :=
  forall D : CuttingPlanesDerivation Axiom Target,
    r <= D.rank

/-- A rank lower bound rules out tree-like derivations with fewer than `r`
nodes. -/
theorem no_small_cuttingPlanes_derivation_of_rank_lower_bound
    {Axiom : CuttingPlanesLine σ -> Prop}
    {Target : CuttingPlanesLine σ}
    {r s : Nat}
    (Hrank : CuttingPlanesRankLowerBound Axiom Target r)
    (hgap : s < r) :
    Not (exists D : CuttingPlanesDerivation Axiom Target, D.size <= s) := by
  rintro ⟨D, hD⟩
  have hrank : r <= D.rank := Hrank D
  have hsize : D.rank <= s := Nat.le_trans D.rank_le_size hD
  exact Nat.not_lt_of_ge (Nat.le_trans hrank hsize) hgap

/-! ## Kernel-only axiom trace -/

#print axioms CuttingPlanesLine.add_satisfied
#print axioms CuttingPlanesLine.scale_satisfied
#print axioms CuttingPlanesDerivation.rank_le_size
#print axioms no_small_cuttingPlanes_derivation_of_rank_lower_bound

end PallLean.Paper93.DeepMath.PathB
