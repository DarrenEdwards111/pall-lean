import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResolutionWidthSize

/-!
# Rung 3 substrate: polynomial-calculus degree/size accounting

**STATUS: RUNG-3 SUBSTRATE, NOT A FULL POLYNOMIAL-CALCULUS LOWER BOUND.**

Rung 3 of the proof-complexity ladder contains polynomial calculus,
Nullstellensatz, cutting planes, and Frege fragments.  Completing that rung in
full would mean formalizing substantial known lower bounds: e.g.
Buss--Grigoriev--Impagliazzo--Pitassi and Alekhnovich--Razborov style degree and
size lower bounds for Tseitin/related systems, plus separate machinery for
cutting planes or bounded-depth Frege.  This file does not fake those results as
free fields.

What it does prove is the honest substrate analogue of the rung-2 resolution
accounting:

* a syntactic polynomial-calculus derivation model with axioms, linear
  combinations, and multiplication by variables;
* proof size and proof degree;
* degree accounting for each inference;
* if all axioms have degree at most `k`, then every derivation has degree at
  most `k + size`;
* therefore any degree lower bound `d` forces a tree-like derivation size lower
  bound: no derivation of size `s` exists when `k + s < d`;
* signed 3-CNF axioms are represented with degree at most `3`.

This is a real formal rung-3 accounting theorem.  The hard lower-bound input —
that a specific expander-Tseitin polynomial-calculus refutation requires large
degree — remains a cited/proof-complexity theorem, not an assumed progress
socket.
-/

namespace PallLean.Paper93.DeepMath.PathB

/-! ## Abstract polynomial-calculus lines -/

/-- A polynomial-calculus line is represented by its syntactic degree.

This is deliberately a degree-accounting substrate rather than a full
`MvPolynomial` formalization.  The inference rules below are the proof system:
axioms introduce lines; linear combinations take max degree; multiplication by a
variable increases degree by at most one. -/
structure PolynomialCalculusLine : Type where
  degree : Nat

namespace PolynomialCalculusLine

/-- Linear combination: degree is bounded by the max of the parent degrees. -/
def linComb (P Q : PolynomialCalculusLine) : PolynomialCalculusLine where
  degree := max P.degree Q.degree

/-- Multiplication by a variable: degree increases by one. -/
def mulVar (P : PolynomialCalculusLine) : PolynomialCalculusLine where
  degree := P.degree + 1

@[simp] theorem degree_linComb (P Q : PolynomialCalculusLine) :
    (linComb P Q).degree = max P.degree Q.degree :=
  rfl

@[simp] theorem degree_mulVar (P : PolynomialCalculusLine) :
    (mulVar P).degree = P.degree + 1 :=
  rfl

end PolynomialCalculusLine

/-! ## Tree-like polynomial-calculus derivations -/

/-- Tree-like polynomial-calculus derivations from an axiom predicate. -/
inductive PolynomialCalculusDerivation
    (Axiom : PolynomialCalculusLine -> Prop) :
    PolynomialCalculusLine -> Type where
  | ax {P : PolynomialCalculusLine} :
      Axiom P -> PolynomialCalculusDerivation Axiom P
  | lin {P Q : PolynomialCalculusLine} :
      PolynomialCalculusDerivation Axiom P ->
      PolynomialCalculusDerivation Axiom Q ->
      PolynomialCalculusDerivation Axiom (PolynomialCalculusLine.linComb P Q)
  | mul {P : PolynomialCalculusLine} :
      PolynomialCalculusDerivation Axiom P ->
      PolynomialCalculusDerivation Axiom (PolynomialCalculusLine.mulVar P)

namespace PolynomialCalculusDerivation

variable {Axiom : PolynomialCalculusLine -> Prop}

/-- Number of nodes in the tree-like polynomial-calculus derivation. -/
def size {P : PolynomialCalculusLine}
    (D : PolynomialCalculusDerivation Axiom P) : Nat :=
  match D with
  | ax _ => 1
  | lin L R => size L + size R + 1
  | mul E => size E + 1

/-- Maximum degree appearing in a tree-like polynomial-calculus derivation. -/
def proofDegree {P : PolynomialCalculusLine}
    (D : PolynomialCalculusDerivation Axiom P) : Nat :=
  match D with
  | ax (P := P) _ => P.degree
  | lin (P := P) (Q := Q) L R => max (max (proofDegree L) (proofDegree R))
      (PolynomialCalculusLine.linComb P Q).degree
  | mul (P := P) E => max (proofDegree E) (PolynomialCalculusLine.mulVar P).degree

@[simp] theorem size_ax {P : PolynomialCalculusLine} (h : Axiom P) :
    size (PolynomialCalculusDerivation.ax h) = 1 :=
  rfl

@[simp] theorem size_lin {P Q : PolynomialCalculusLine}
    (L : PolynomialCalculusDerivation Axiom P)
    (R : PolynomialCalculusDerivation Axiom Q) :
    size (PolynomialCalculusDerivation.lin L R) = size L + size R + 1 :=
  rfl

@[simp] theorem size_mul {P : PolynomialCalculusLine}
    (E : PolynomialCalculusDerivation Axiom P) :
    size (PolynomialCalculusDerivation.mul E) = size E + 1 :=
  rfl

/-- Polynomial-calculus derivations have positive size. -/
theorem size_pos {P : PolynomialCalculusLine}
    (D : PolynomialCalculusDerivation Axiom P) :
    0 < size D := by
  induction D with
  | ax _ => simp [size]
  | lin L R ihL ihR => simp [size]
  | mul E ih => simp [size]

/-- The root degree is bounded by proof degree. -/
theorem root_degree_le_proofDegree {P : PolynomialCalculusLine}
    (D : PolynomialCalculusDerivation Axiom P) :
    P.degree <= proofDegree D := by
  cases D with
  | ax h => simp [proofDegree]
  | lin L R =>
      simp [proofDegree, PolynomialCalculusLine.linComb]
  | mul E =>
      simp [proofDegree, PolynomialCalculusLine.mulVar]

end PolynomialCalculusDerivation

/-! ## Degree lower-bound interface -/

/-- A polynomial-calculus degree lower bound for deriving a target line. -/
def PolynomialCalculusDegreeLowerBound
    (Axiom : PolynomialCalculusLine -> Prop)
    (Target : PolynomialCalculusLine)
    (d : Nat) : Prop :=
  forall D : PolynomialCalculusDerivation Axiom Target,
    d <= D.proofDegree

/-- All polynomial-calculus axioms have degree at most `k`. -/
def PolynomialCalculusAxiomsDegreeAtMost
    (Axiom : PolynomialCalculusLine -> Prop)
    (k : Nat) : Prop :=
  forall P : PolynomialCalculusLine, Axiom P -> P.degree <= k

/-- In a tree-like polynomial-calculus derivation from degree-`k` axioms, every
line has degree at most `k + size`.

This is deliberately weaker than sharp degree accounting, but it is robust and
sufficient for a genuine degree-to-size consequence. -/
theorem proofDegree_le_axiomDegree_add_size
    {Axiom : PolynomialCalculusLine -> Prop}
    {Target : PolynomialCalculusLine}
    {k : Nat}
    (Hax : PolynomialCalculusAxiomsDegreeAtMost Axiom k)
    (D : PolynomialCalculusDerivation Axiom Target) :
    D.proofDegree <= k + D.size := by
  induction D with
  | ax h =>
      have hk := Hax _ h
      simp [PolynomialCalculusDerivation.proofDegree,
        PolynomialCalculusDerivation.size]
      omega
  | lin L R ihL ihR =>
      have hLroot := PolynomialCalculusDerivation.root_degree_le_proofDegree L
      have hRroot := PolynomialCalculusDerivation.root_degree_le_proofDegree R
      have hL' : L.proofDegree <= k + (L.size + R.size + 1) := by
        exact Nat.le_trans ihL (by omega)
      have hR' : R.proofDegree <= k + (L.size + R.size + 1) := by
        exact Nat.le_trans ihR (by omega)
      simp [PolynomialCalculusDerivation.proofDegree,
        PolynomialCalculusDerivation.size, PolynomialCalculusLine.linComb]
      exact ⟨hL', hR',
        ⟨Nat.le_trans hLroot hL', Nat.le_trans hRroot hR'⟩⟩
  | mul E ih =>
      have hEroot := PolynomialCalculusDerivation.root_degree_le_proofDegree E
      have hE' : E.proofDegree <= k + (E.size + 1) := by
        exact Nat.le_trans ih (by omega)
      simp [PolynomialCalculusDerivation.proofDegree,
        PolynomialCalculusDerivation.size, PolynomialCalculusLine.mulVar]
      exact ⟨hE', by omega⟩

/-- Degree lower bounds give tree-like size lower bounds: if every derivation of
`Target` has degree at least `d`, then every derivation has `d <= k + size` when
axioms have degree at most `k`. -/
theorem degree_lower_bound_le_axiomDegree_add_size
    {Axiom : PolynomialCalculusLine -> Prop}
    {Target : PolynomialCalculusLine}
    {k d : Nat}
    (Hax : PolynomialCalculusAxiomsDegreeAtMost Axiom k)
    (Hdeg : PolynomialCalculusDegreeLowerBound Axiom Target d)
    (D : PolynomialCalculusDerivation Axiom Target) :
    d <= k + D.size :=
  Nat.le_trans (Hdeg D) (proofDegree_le_axiomDegree_add_size Hax D)

/-- No small tree-like polynomial-calculus derivation exists when the degree
lower bound exceeds the total degree budget `k + s`. -/
theorem no_small_polynomialCalculus_derivation_of_degree_lower_bound
    {Axiom : PolynomialCalculusLine -> Prop}
    {Target : PolynomialCalculusLine}
    {k d s : Nat}
    (Hax : PolynomialCalculusAxiomsDegreeAtMost Axiom k)
    (Hdeg : PolynomialCalculusDegreeLowerBound Axiom Target d)
    (hgap : k + s < d) :
    Not (exists D : PolynomialCalculusDerivation Axiom Target, D.size <= s) := by
  rintro ⟨D, hD⟩
  have hd : d <= k + D.size :=
    degree_lower_bound_le_axiomDegree_add_size Hax Hdeg D
  have hs : k + D.size <= k + s := Nat.add_le_add_left hD k
  exact Nat.not_lt_of_ge (Nat.le_trans hd hs) hgap

/-! ## Signed 3-CNF degree substrate -/

/-- A signed 3-CNF clause contributes a polynomial-calculus axiom of degree at
most `3`.  This is the degree analogue of the resolution-width embedding. -/
def SignedClause3.toPolynomialCalculusLine {n : Nat}
    (_c : SignedClause3 n) : PolynomialCalculusLine where
  degree := 3

/-- The polynomial-calculus axioms induced by a signed 3-CNF formula. -/
def SignedThreeCNFPolynomialCalculusAxiom
    (φ : SignedThreeCNF) : PolynomialCalculusLine -> Prop :=
  fun P => exists c : SignedClause3 φ.numVars,
    c ∈ φ.clauses /\ c.toPolynomialCalculusLine = P

/-- The contradiction target line, represented abstractly as the constant `1`,
has degree zero. -/
def polynomialCalculusContradictionLine : PolynomialCalculusLine where
  degree := 0

/-- A tree-like polynomial-calculus refutation of a signed 3-CNF formula. -/
abbrev SignedThreeCNFPolynomialCalculusRefutation (φ : SignedThreeCNF) :=
  PolynomialCalculusDerivation
    (SignedThreeCNFPolynomialCalculusAxiom φ)
    polynomialCalculusContradictionLine

/-- Signed 3-CNF polynomial-calculus axioms have degree at most `3`. -/
theorem signedThreeCNFPolynomialCalculusAxioms_degree_le_three
    (φ : SignedThreeCNF) :
    PolynomialCalculusAxiomsDegreeAtMost
      (SignedThreeCNFPolynomialCalculusAxiom φ) 3 := by
  intro P hP
  rcases hP with ⟨c, _hc, rfl⟩
  rfl

/-- A signed-3-CNF polynomial-calculus degree lower bound gives a tree-like size
lower bound: `d <= 3 + size`. -/
theorem signedThreeCNF_degree_lower_bound_le_three_add_refutation_size
    (φ : SignedThreeCNF)
    {d : Nat}
    (Hdeg : PolynomialCalculusDegreeLowerBound
      (SignedThreeCNFPolynomialCalculusAxiom φ)
      polynomialCalculusContradictionLine d)
    (D : SignedThreeCNFPolynomialCalculusRefutation φ) :
    d <= 3 + D.size :=
  degree_lower_bound_le_axiomDegree_add_size
    (signedThreeCNFPolynomialCalculusAxioms_degree_le_three φ) Hdeg D

/-- No small tree-like signed-3-CNF polynomial-calculus refutation exists once
the degree lower bound exceeds the budget `3 + s`. -/
theorem no_small_signedThreeCNF_polynomialCalculus_refutation_of_degree_lower_bound
    (φ : SignedThreeCNF)
    {d s : Nat}
    (Hdeg : PolynomialCalculusDegreeLowerBound
      (SignedThreeCNFPolynomialCalculusAxiom φ)
      polynomialCalculusContradictionLine d)
    (hgap : 3 + s < d) :
    Not (exists D : SignedThreeCNFPolynomialCalculusRefutation φ, D.size <= s) :=
  no_small_polynomialCalculus_derivation_of_degree_lower_bound
    (signedThreeCNFPolynomialCalculusAxioms_degree_le_three φ) Hdeg hgap

/-! ## Kernel-only axiom trace -/

#print axioms PolynomialCalculusDerivation.size_pos
#print axioms PolynomialCalculusDerivation.root_degree_le_proofDegree
#print axioms proofDegree_le_axiomDegree_add_size
#print axioms degree_lower_bound_le_axiomDegree_add_size
#print axioms no_small_polynomialCalculus_derivation_of_degree_lower_bound
#print axioms signedThreeCNFPolynomialCalculusAxioms_degree_le_three
#print axioms signedThreeCNF_degree_lower_bound_le_three_add_refutation_size
#print axioms no_small_signedThreeCNF_polynomialCalculus_refutation_of_degree_lower_bound

end PallLean.Paper93.DeepMath.PathB
