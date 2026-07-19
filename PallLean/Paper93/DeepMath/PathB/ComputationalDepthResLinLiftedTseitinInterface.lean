import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResLinParityRestriction
import Mathlib.Data.Nat.Log

/-!
# Lifted-Tseitin depth/size interface for `Res(⊕)`

This file states the modern lower-bound target directly over the checked dag object.  The motivating
result is Bhattacharya--Chattopadhyay, ECCC TR25-106 (revision 2, 2025): lifted Tseitin formulas on
constant-degree expanders require size `exp(Ω̃(N^ε))` for proofs of depth `O(N^(2-ε))`, and their
general lifting theorem has the shape

`depth = Ω(p*q / log(size))`

for `(p,q)`-decision-tree-hard source formulas and parity-fooling gadgets.

We do **not** assert that theorem as proved here.  Instead we formalize:

* the family/encoding contract consumed by such a theorem;
* its division-free tradeoff form `p*q ≤ c*depth*(log₂(size)+1)`;
* the exact small-size/shallow-depth contradiction;
* the precise remaining gap from a bounded-depth result to an unrestricted dag lower bound.

Thus every downstream theorem visibly takes the mathematical lifting claim as a hypothesis.
-/

namespace PallLean.Paper93.DeepMath.PathB.ResLinParity

open Classical

/-- Encoding-level data for a family of lifted Tseitin instances.  Constructing a concrete member
requires supplying its actual affine-clause encoding and a semantic unsatisfiability proof. -/
structure LiftedTseitinFamily where
  variableCount : ℕ → ℕ
  baseVertices : ℕ → ℕ
  gadgetBits : ℕ → ℕ
  axioms : ∀ m, Finset (Clause (variableCount m))
  unsatisfiable : ∀ m, ¬ ∃ x : Fin (variableCount m) → ZMod 2, Models x (axioms m)

/-- The exact checked proof type for one member of a family. -/
abbrev FamilyRefutation (F : LiftedTseitinFamily) (m : ℕ) :=
  DAGRefutation (F.variableCount m) (F.axioms m)

/-- A parameterized depth/size lower bound. -/
def HasDepthSizeLowerBound (F : LiftedTseitinFamily)
    (depthCap sizeFloor : ℕ → ℕ) : Prop :=
  ∀ m (P : FamilyRefutation F m), P.depth ≤ depthCap m → sizeFloor m ≤ P.size

/-- The unrestricted size lower bound that remains open for `Res(⊕)`. -/
def HasUnrestrictedSizeLowerBound (F : LiftedTseitinFamily)
    (sizeFloor : ℕ → ℕ) : Prop :=
  ∀ m (P : FamilyRefutation F m), sizeFloor m ≤ P.size

/-- Division-free form of the lifting theorem's `Ω(p*q/log(size))` depth tradeoff.  `constant` is
the hidden absolute multiplicative constant. -/
def HasLiftingTradeoff (F : LiftedTseitinFamily)
    (p q : ℕ → ℕ) (constant : ℕ) : Prop :=
  ∀ m (P : FamilyRefutation F m),
    p m * q m ≤ constant * P.depth * (Nat.log2 P.size + 1)

/-- A bounded-depth lower bound is equivalently a size/depth dichotomy. -/
theorem depth_size_dichotomy {F : LiftedTseitinFamily} {depthCap sizeFloor : ℕ → ℕ}
    (h : HasDepthSizeLowerBound F depthCap sizeFloor) (m : ℕ)
    (P : FamilyRefutation F m) :
    sizeFloor m ≤ P.size ∨ depthCap m < P.depth := by
  by_cases hd : P.depth ≤ depthCap m
  · exact Or.inl (h m P hd)
  · exact Or.inr (Nat.lt_of_not_ge hd)

/-- The lifting tradeoff excludes any proof simultaneously below a proposed size and depth cap
once the numerical gap beats the tradeoff's right-hand side. -/
theorem liftingTradeoff_excludes_small_shallow
    {F : LiftedTseitinFamily} {p q : ℕ → ℕ} {constant m S D : ℕ}
    (htrade : HasLiftingTradeoff F p q constant)
    (hgap : constant * D * (Nat.log2 S + 1) < p m * q m)
    (P : FamilyRefutation F m) (hsize : P.size ≤ S) (hdepth : P.depth ≤ D) : False := by
  have hlog : Nat.log2 P.size ≤ Nat.log2 S := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right hsize
  have hupper : constant * P.depth * (Nat.log2 P.size + 1) ≤
      constant * D * (Nat.log2 S + 1) := by
    exact Nat.mul_le_mul (Nat.mul_le_mul_left constant hdepth) (Nat.add_le_add_right hlog 1)
  have hlower := htrade m P
  omega

/-- Pointwise numerical gaps turn the general lifting tradeoff into a depth/size lower bound. -/
theorem depthSizeLowerBound_of_liftingTradeoff
    {F : LiftedTseitinFamily} {p q depthCap sizeFloor : ℕ → ℕ} {constant : ℕ}
    (htrade : HasLiftingTradeoff F p q constant)
    (hgap : ∀ m, constant * depthCap m * (Nat.log2 (sizeFloor m - 1) + 1) < p m * q m) :
    HasDepthSizeLowerBound F depthCap sizeFloor := by
  intro m P hdepth
  by_contra hsmall
  have hsize : P.size ≤ sizeFloor m - 1 := by omega
  exact liftingTradeoff_excludes_small_shallow htrade (hgap m) P hsize hdepth

/-- A bounded-depth theorem becomes unrestricted only with an all-refutations depth cap (or an
equivalent depth-reduction theorem).  This is the exact missing bridge, exposed as a hypothesis. -/
theorem unrestricted_of_depthSize_of_all_shallow
    {F : LiftedTseitinFamily} {depthCap sizeFloor : ℕ → ℕ}
    (hbound : HasDepthSizeLowerBound F depthCap sizeFloor)
    (hall : ∀ m (P : FamilyRefutation F m), P.depth ≤ depthCap m) :
    HasUnrestrictedSizeLowerBound F sizeFloor := by
  intro m P
  exact hbound m P (hall m P)

/-- Conversely, if the bounded-depth theorem holds but the unrestricted bound fails, the witness
must be a genuinely deep small dag refutation.  No change of terminology can avoid this case. -/
theorem deep_small_refutation_of_unrestricted_failure
    {F : LiftedTseitinFamily} {depthCap sizeFloor : ℕ → ℕ}
    (hbound : HasDepthSizeLowerBound F depthCap sizeFloor)
    (hfail : ¬ HasUnrestrictedSizeLowerBound F sizeFloor) :
    ∃ m, ∃ P : FamilyRefutation F m, P.size < sizeFloor m ∧ depthCap m < P.depth := by
  unfold HasUnrestrictedSizeLowerBound at hfail
  push_neg at hfail
  rcases hfail with ⟨m, P, hsmall⟩
  exact ⟨m, P, hsmall, (depth_size_dichotomy hbound m P).resolve_left (by omega)⟩

/-- The bounded-depth result and unrestricted result agree exactly when deep-small witnesses are
ruled out. -/
theorem unrestricted_iff_no_deep_small
    {F : LiftedTseitinFamily} {depthCap sizeFloor : ℕ → ℕ}
    (hbound : HasDepthSizeLowerBound F depthCap sizeFloor) :
    HasUnrestrictedSizeLowerBound F sizeFloor ↔
      ¬ ∃ m, ∃ P : FamilyRefutation F m,
        P.size < sizeFloor m ∧ depthCap m < P.depth := by
  constructor
  · intro hunres
    rintro ⟨m, P, hsmall, _⟩
    exact (Nat.not_lt_of_ge (hunres m P)) hsmall
  · intro hno
    by_contra hfail
    exact hno (deep_small_refutation_of_unrestricted_failure hbound hfail)

#print axioms liftingTradeoff_excludes_small_shallow
#print axioms depthSizeLowerBound_of_liftingTradeoff
#print axioms deep_small_refutation_of_unrestricted_failure
#print axioms unrestricted_iff_no_deep_small

end PallLean.Paper93.DeepMath.PathB.ResLinParity
