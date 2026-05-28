import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSignedThreeCNFModel

/-!
# Real bounded-depth Frege core

**STATUS: REAL FORMULA/DERIVATION SUBSTRATE, NOT A FREGE LOWER-BOUND ENGINE.**

This file replaces the old rung-3 bounded-depth Frege placeholder with an actual
propositional formula syntax, Boolean semantics, a Hilbert-style Frege derivation
kernel using modus ponens, formula depth, proof depth, and a lower-bound
interface.

It proves the honest accounting theorem needed by the proof-complexity ladder:
if every axiom has formula depth at most `k`, then every line in every derivation
from those axioms has proof depth at most `k`; hence a proof-depth lower bound
above `k` rules out such bounded-depth derivations.

This does **not** formalize Ajtai/Håstad-style bounded-depth Frege lower bounds,
nor any family-specific Tseitin/PHP lower bound.  Those remain literature and
future formalization targets.
-/

namespace PallLean.Paper93.DeepMath.PathB

/-! ## Propositional formulas -/

/-- Propositional formulas over `n` Boolean variables. -/
inductive PropFormula (n : Nat) : Type where
  | falsum : PropFormula n
  | var : Fin n -> PropFormula n
  | neg : PropFormula n -> PropFormula n
  | and : PropFormula n -> PropFormula n -> PropFormula n
  | or : PropFormula n -> PropFormula n -> PropFormula n
  | imp : PropFormula n -> PropFormula n -> PropFormula n

deriving instance DecidableEq for PropFormula

namespace PropFormula

/-- Boolean evaluation of propositional formulas. -/
def eval {n : Nat} (σ : Fin n -> Bool) : PropFormula n -> Bool
  | falsum => false
  | var i => σ i
  | neg A => !(eval σ A)
  | and A B => eval σ A && eval σ B
  | or A B => eval σ A || eval σ B
  | imp A B => (!(eval σ A)) || eval σ B

/-- Formula depth. Variables and `⊥` have depth zero; each connective adds one. -/
def depth {n : Nat} : PropFormula n -> Nat
  | falsum => 0
  | var _ => 0
  | neg A => A.depth + 1
  | and A B => max A.depth B.depth + 1
  | or A B => max A.depth B.depth + 1
  | imp A B => max A.depth B.depth + 1

/-- Formula size, used only as an honest syntactic measure. -/
def size {n : Nat} : PropFormula n -> Nat
  | falsum => 1
  | var _ => 1
  | neg A => A.size + 1
  | and A B => A.size + B.size + 1
  | or A B => A.size + B.size + 1
  | imp A B => A.size + B.size + 1

@[simp] theorem depth_falsum {n : Nat} : (falsum (n := n)).depth = 0 := rfl
@[simp] theorem depth_var {n : Nat} (i : Fin n) : (var i).depth = 0 := rfl
@[simp] theorem depth_neg {n : Nat} (A : PropFormula n) : (neg A).depth = A.depth + 1 := rfl
@[simp] theorem depth_and {n : Nat} (A B : PropFormula n) :
    (and A B).depth = max A.depth B.depth + 1 := rfl
@[simp] theorem depth_or {n : Nat} (A B : PropFormula n) :
    (or A B).depth = max A.depth B.depth + 1 := rfl
@[simp] theorem depth_imp {n : Nat} (A B : PropFormula n) :
    (imp A B).depth = max A.depth B.depth + 1 := rfl

/-- The consequent of an implication has depth bounded by the implication. -/
theorem consequent_depth_le_imp_depth {n : Nat} (A B : PropFormula n) :
    B.depth <= (imp A B).depth := by
  simp [depth]
  omega

end PropFormula

/-! ## Signed 3-CNF clauses as formulas -/

namespace SignedLiteral

/-- Translate a signed literal to a propositional formula. -/
def toPropFormula {n : Nat} : SignedLiteral n -> PropFormula n
  | pos i => PropFormula.var i
  | neg i => PropFormula.neg (PropFormula.var i)

/-- A signed literal has formula depth at most one. -/
theorem toPropFormula_depth_le_one {n : Nat} (l : SignedLiteral n) :
    l.toPropFormula.depth <= 1 := by
  cases l <;> simp [toPropFormula, PropFormula.depth]

end SignedLiteral

namespace SignedClause3

/-- Translate a 3-CNF clause to a propositional disjunction. -/
def toPropFormula {n : Nat} (c : SignedClause3 n) : PropFormula n :=
  PropFormula.or c.lit1.toPropFormula
    (PropFormula.or c.lit2.toPropFormula c.lit3.toPropFormula)

/-- The standard 3-CNF clause translation has depth at most three. -/
theorem toPropFormula_depth_le_three {n : Nat} (c : SignedClause3 n) :
    c.toPropFormula.depth <= 3 := by
  have h1 := SignedLiteral.toPropFormula_depth_le_one c.lit1
  have h2 := SignedLiteral.toPropFormula_depth_le_one c.lit2
  have h3 := SignedLiteral.toPropFormula_depth_le_one c.lit3
  simp [toPropFormula, PropFormula.depth]
  omega

end SignedClause3

/-! ## Frege derivations -/

/-- A minimal Frege kernel: arbitrary axiom formulas plus modus ponens.  This is
an actual formula-level derivation system rather than a free resource counter. -/
inductive FregeDerivation {n : Nat} (Axiom : PropFormula n -> Prop) :
    PropFormula n -> Type where
  | ax {A : PropFormula n} : Axiom A -> FregeDerivation Axiom A
  | modusPonens {A B : PropFormula n} :
      FregeDerivation Axiom A ->
      FregeDerivation Axiom (PropFormula.imp A B) ->
      FregeDerivation Axiom B

namespace FregeDerivation

/-- Number of nodes in the tree-like Frege derivation. -/
def size {n : Nat} {Axiom : PropFormula n -> Prop} {A : PropFormula n}
    (D : FregeDerivation Axiom A) : Nat :=
  match D with
  | ax _ => 1
  | modusPonens L R => size L + size R + 1

/-- Maximum formula depth occurring in the derivation tree. -/
def proofDepth {n : Nat} {Axiom : PropFormula n -> Prop} {A : PropFormula n}
    (D : FregeDerivation Axiom A) : Nat :=
  match D with
  | ax (A := A) _ => A.depth
  | modusPonens L R => max (proofDepth L) (proofDepth R)

/-- The root formula depth is bounded by proof depth. -/
theorem root_depth_le_proofDepth {n : Nat} {Axiom : PropFormula n -> Prop}
    {A : PropFormula n} (D : FregeDerivation Axiom A) :
    A.depth <= D.proofDepth := by
  induction D with
  | ax h => simp [proofDepth]
  | modusPonens L R ihL ihR =>
      exact le_trans (PropFormula.consequent_depth_le_imp_depth _ _)
        (le_trans ihR (le_max_right _ _))

end FregeDerivation

/-- Every axiom formula has depth at most `k`. -/
def FregeAxiomsDepthAtMost {n : Nat}
    (Axiom : PropFormula n -> Prop) (k : Nat) : Prop :=
  forall A : PropFormula n, Axiom A -> A.depth <= k

/-- A lower bound saying every Frege derivation of `Target` must contain a line
of formula depth at least `d`. -/
def FregeDepthLowerBound {n : Nat}
    (Axiom : PropFormula n -> Prop) (Target : PropFormula n) (d : Nat) : Prop :=
  forall D : FregeDerivation Axiom Target, d <= D.proofDepth

/-- In the formula-level Frege kernel, modus ponens cannot create deeper formulas
than those already appearing in the implication parent.  Therefore proof depth is
bounded by the axiom-depth cap. -/
theorem fregeProofDepth_le_axiomDepth {n : Nat}
    {Axiom : PropFormula n -> Prop} {Target : PropFormula n} {k : Nat}
    (Hax : FregeAxiomsDepthAtMost Axiom k)
    (D : FregeDerivation Axiom Target) :
    D.proofDepth <= k := by
  induction D with
  | ax h =>
      simpa [FregeDerivation.proofDepth] using Hax _ h
  | modusPonens L R ihL ihR =>
      simp [FregeDerivation.proofDepth]
      exact ⟨ihL, ihR⟩

/-- A proof-depth lower bound above the axiom-depth cap rules out derivations. -/
theorem no_frege_derivation_of_depth_lower_bound
    {n : Nat} {Axiom : PropFormula n -> Prop} {Target : PropFormula n}
    {k d : Nat}
    (Hax : FregeAxiomsDepthAtMost Axiom k)
    (Hdepth : FregeDepthLowerBound Axiom Target d)
    (hgap : k < d) :
    Not (Nonempty (FregeDerivation Axiom Target)) := by
  rintro ⟨D⟩
  have hlo : D.proofDepth <= k := fregeProofDepth_le_axiomDepth Hax D
  have hhi : d <= D.proofDepth := Hdepth D
  exact Nat.not_lt_of_ge (le_trans hhi hlo) hgap

/-! ## Signed 3-CNF bounded-depth Frege interface -/

/-- Signed 3-CNF Frege axioms are exactly the translated clauses. -/
def SignedThreeCNFFregeAxiom (φ : SignedThreeCNF) :
    PropFormula φ.numVars -> Prop :=
  fun A => exists c : SignedClause3 φ.numVars,
    c ∈ φ.clauses /\ c.toPropFormula = A

/-- The contradiction target is `⊥`. -/
def fregeContradictionFormula (n : Nat) : PropFormula n :=
  PropFormula.falsum

abbrev SignedThreeCNFFregeRefutation (φ : SignedThreeCNF) :=
  FregeDerivation (SignedThreeCNFFregeAxiom φ)
    (fregeContradictionFormula φ.numVars)

/-- Signed 3-CNF Frege axioms have formula depth at most three. -/
theorem signedThreeCNFFregeAxioms_depth_le_three (φ : SignedThreeCNF) :
    FregeAxiomsDepthAtMost (SignedThreeCNFFregeAxiom φ) 3 := by
  intro A hA
  rcases hA with ⟨c, _hc, rfl⟩
  exact SignedClause3.toPropFormula_depth_le_three c

/-- A Frege proof-depth lower bound above three rules out signed-3-CNF Frege
refutations from clause axioms. -/
theorem no_signedThreeCNF_frege_refutation_of_depth_lower_bound
    (φ : SignedThreeCNF) {d : Nat}
    (Hdepth : FregeDepthLowerBound
      (SignedThreeCNFFregeAxiom φ) (fregeContradictionFormula φ.numVars) d)
    (hgap : 3 < d) :
    Not (Nonempty (SignedThreeCNFFregeRefutation φ)) :=
  no_frege_derivation_of_depth_lower_bound
    (signedThreeCNFFregeAxioms_depth_le_three φ) Hdepth hgap

/-! ## Kernel-only axiom trace -/

#print axioms PropFormula.consequent_depth_le_imp_depth
#print axioms SignedClause3.toPropFormula_depth_le_three
#print axioms FregeDerivation.root_depth_le_proofDepth
#print axioms fregeProofDepth_le_axiomDepth
#print axioms no_frege_derivation_of_depth_lower_bound
#print axioms signedThreeCNFFregeAxioms_depth_le_three
#print axioms no_signedThreeCNF_frege_refutation_of_depth_lower_bound

end PallLean.Paper93.DeepMath.PathB
