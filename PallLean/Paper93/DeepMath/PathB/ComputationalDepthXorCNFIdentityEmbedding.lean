import PallLean.Paper93.DeepMath.PathB.ComputationalDepthXorDNFCosetCollapse

/-!
# XOR-CNF identity embedding: the succinct boundary

The DNF target-list collapse does not extend automatically to CNF.  Give each input bit its own singleton parity gate.
The resulting parity profile is exactly the original Boolean assignment (embedded in `ZMod 2`).  Therefore any CNF
over those parity outputs is semantically identical to the original CNF.

This file formalizes that identity embedding.  It does not assert a complexity lower bound, but it proves that no SAT
collapse for XOR-CNF can follow merely from replacing variables by parity gates: the class already contains ordinary
CNF semantics as the singleton-support case.
-/

namespace PallLean.Paper93.DeepMath.PathB.XorCNFIdentityEmbedding

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0ParityConstraintRealization

variable {n : ℕ}

/-- A literal is a variable together with its required Boolean value. -/
abbrev Literal (n : ℕ) := Fin n × Bool

/-- A CNF is a finite set of finite disjunctive clauses. -/
abbrev CNF (n : ℕ) := Finset (Finset (Literal n))

def evalLiteral (x : Fin n → Bool) (l : Literal n) : Prop := x l.1 = l.2

def evalClause (x : Fin n → Bool) (clause : Finset (Literal n)) : Prop :=
  ∃ l ∈ clause, evalLiteral x l

def evalCNF (x : Fin n → Bool) (φ : CNF n) : Prop :=
  ∀ clause ∈ φ, evalClause x clause

/-- Singleton parity supports reproduce the input coordinates. -/
def singletonSupports (n : ℕ) : Fin n → Finset (Fin n) := fun i => {i}

/-- Boolean assignment embedded coordinatewise in `ZMod 2`. -/
def boolProfile (x : Fin n → Bool) : Fin n → ZMod 2 :=
  fun i => if x i then 1 else 0

/-- Decode an F₂ profile back to Boolean coordinates. -/
def profileBool (z : Fin n → ZMod 2) : Fin n → Bool :=
  fun i => decide (z i = 1)

/-- The singleton parity layer is exactly the coordinatewise Boolean embedding. -/
theorem parityVector_singletonSupports (x : Fin n → Bool) :
    parityVector (singletonSupports n) x = boolProfile x := by
  funext i
  unfold parityVector singletonSupports boolProfile
  rw [modQStatOn_two_eq_sum]
  simp only [Finset.sum_singleton]

/-- Decoding the embedded Boolean profile is the identity. -/
theorem profileBool_boolProfile (x : Fin n → Bool) : profileBool (boolProfile x) = x := by
  funext i
  cases h : x i <;> simp [profileBool, boolProfile, h]

/-- CNF acceptance applied to a parity profile. -/
def xorCNFAccept (φ : CNF n) (z : Fin n → ZMod 2) : Prop := evalCNF (profileBool z) φ

/-- **XOR-CNF singleton-support identity (proved).** -/
theorem xorCNF_singleton_eq (φ : CNF n) (x : Fin n → Bool) :
    xorCNFAccept φ (parityVector (singletonSupports n) x) ↔ evalCNF x φ := by
  rw [parityVector_singletonSupports, xorCNFAccept, profileBool_boolProfile]

/-- Consequently the satisfiability statements are exactly equivalent. -/
theorem xorCNF_singleton_sat_iff (φ : CNF n) :
    (∃ x, xorCNFAccept φ (parityVector (singletonSupports n) x)) ↔ ∃ x, evalCNF x φ := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (xorCNF_singleton_eq φ x).mp hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (xorCNF_singleton_eq φ x).mpr hx⟩

end PallLean.Paper93.DeepMath.PathB.XorCNFIdentityEmbedding

#print axioms PallLean.Paper93.DeepMath.PathB.XorCNFIdentityEmbedding.parityVector_singletonSupports
#print axioms PallLean.Paper93.DeepMath.PathB.XorCNFIdentityEmbedding.xorCNF_singleton_eq
#print axioms PallLean.Paper93.DeepMath.PathB.XorCNFIdentityEmbedding.xorCNF_singleton_sat_iff
