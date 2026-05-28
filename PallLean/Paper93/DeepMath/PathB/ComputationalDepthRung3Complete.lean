import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPolynomialCalculusRung

/-!
# Rung 3 completed as formal substrates

Rung 3 is not one proof system.  It is the cluster of algebraic and
semi-algebraic proof systems that sit above resolution and below circuit lower
bounds: polynomial calculus, Nullstellensatz, cutting planes, and bounded-depth
Frege fragments.

This file completes the formal **substrate** for that rung in the same honest
sense as the resolution substrate:

* polynomial calculus is imported from `ComputationalDepthPolynomialCalculusRung`;
* Nullstellensatz is exposed as the certificate/degree fragment of polynomial
  calculus;
* cutting planes gets a tree-like rank accounting model;
* bounded-depth Frege gets a tree-like depth accounting model;
* each system has a lower-bound interface and a proved "resource lower bound
  rules out small tree-like derivations" theorem;
* signed 3-CNF axioms are wired into each model with the expected constant
  starting resource.

The hard family-specific lower bounds for Tseitin in these systems remain
literature theorems and future formalization targets.  They are not introduced
as Lean assumptions here.
-/

namespace PallLean.Paper93.DeepMath.PathB

/-! ## Nullstellensatz as the static degree face of polynomial calculus -/

/-- Nullstellensatz certificate degree lower bounds are represented by the same
syntactic degree interface as polynomial calculus: a certificate deriving `1`
from degree-`3` clause polynomials must reach the asserted degree. -/
abbrev NullstellensatzDegreeLowerBound
    (Axiom : PolynomialCalculusLine -> Prop)
    (Target : PolynomialCalculusLine)
    (d : Nat) : Prop :=
  PolynomialCalculusDegreeLowerBound Axiom Target d

/-- A signed-3-CNF Nullstellensatz refutation, modelled as the static certificate
fragment of polynomial calculus. -/
abbrev SignedThreeCNFNullstellensatzRefutation (φ : SignedThreeCNF) :=
  SignedThreeCNFPolynomialCalculusRefutation φ

/-- Nullstellensatz degree lower bounds give the same tree-like size obstruction
as the polynomial-calculus certificate substrate. -/
theorem no_small_signedThreeCNF_nullstellensatz_refutation_of_degree_lower_bound
    (φ : SignedThreeCNF)
    {d s : Nat}
    (Hdeg : NullstellensatzDegreeLowerBound
      (SignedThreeCNFPolynomialCalculusAxiom φ)
      polynomialCalculusContradictionLine d)
    (hgap : 3 + s < d) :
    Not (exists D : SignedThreeCNFNullstellensatzRefutation φ, D.size <= s) :=
  no_small_signedThreeCNF_polynomialCalculus_refutation_of_degree_lower_bound
    φ Hdeg hgap

/-! ## Generic tree-like resource accounting for rank/depth systems -/

/-- A line in an abstract rung-3 proof system, carrying only the resource that
matters for the substrate theorem: rank, depth, or analogous measure. -/
structure Rung3ResourceLine : Type where
  resource : Nat

namespace Rung3ResourceLine

/-- Binary inference combines two lines and increases the active resource by at
most one over the harder parent. -/
def combine (P Q : Rung3ResourceLine) : Rung3ResourceLine where
  resource := max P.resource Q.resource + 1

/-- Unary inference increases the active resource by at most one. -/
def step (P : Rung3ResourceLine) : Rung3ResourceLine where
  resource := P.resource + 1

@[simp] theorem resource_combine (P Q : Rung3ResourceLine) :
    (combine P Q).resource = max P.resource Q.resource + 1 :=
  rfl

@[simp] theorem resource_step (P : Rung3ResourceLine) :
    (step P).resource = P.resource + 1 :=
  rfl

end Rung3ResourceLine

/-- Tree-like derivations for a rank/depth style proof system. -/
inductive Rung3ResourceDerivation
    (Axiom : Rung3ResourceLine -> Prop) :
    Rung3ResourceLine -> Type where
  | ax {P : Rung3ResourceLine} :
      Axiom P -> Rung3ResourceDerivation Axiom P
  | combine {P Q : Rung3ResourceLine} :
      Rung3ResourceDerivation Axiom P ->
      Rung3ResourceDerivation Axiom Q ->
      Rung3ResourceDerivation Axiom (Rung3ResourceLine.combine P Q)
  | step {P : Rung3ResourceLine} :
      Rung3ResourceDerivation Axiom P ->
      Rung3ResourceDerivation Axiom (Rung3ResourceLine.step P)

namespace Rung3ResourceDerivation

variable {Axiom : Rung3ResourceLine -> Prop}

/-- Number of nodes in the tree-like resource derivation. -/
def size {P : Rung3ResourceLine}
    (D : Rung3ResourceDerivation Axiom P) : Nat :=
  match D with
  | ax _ => 1
  | combine L R => size L + size R + 1
  | step E => size E + 1

/-- Maximum resource appearing in the derivation. -/
def proofResource {P : Rung3ResourceLine}
    (D : Rung3ResourceDerivation Axiom P) : Nat :=
  match D with
  | ax (P := P) _ => P.resource
  | combine (P := P) (Q := Q) L R =>
      max (max (proofResource L) (proofResource R))
        (Rung3ResourceLine.combine P Q).resource
  | step (P := P) E =>
      max (proofResource E) (Rung3ResourceLine.step P).resource

/-- The root resource is bounded by the proof resource. -/
theorem root_resource_le_proofResource {P : Rung3ResourceLine}
    (D : Rung3ResourceDerivation Axiom P) :
    P.resource <= D.proofResource := by
  cases D with
  | ax h => simp [proofResource]
  | combine L R =>
      simp [proofResource, Rung3ResourceLine.combine]
  | step E =>
      simp [proofResource, Rung3ResourceLine.step]

end Rung3ResourceDerivation

/-- Every axiom in a rank/depth system starts with resource at most `k`. -/
def Rung3AxiomsResourceAtMost
    (Axiom : Rung3ResourceLine -> Prop)
    (k : Nat) : Prop :=
  forall P : Rung3ResourceLine, Axiom P -> P.resource <= k

/-- A lower bound saying every derivation of `Target` must contain resource at
least `r`. -/
def Rung3ResourceLowerBound
    (Axiom : Rung3ResourceLine -> Prop)
    (Target : Rung3ResourceLine)
    (r : Nat) : Prop :=
  forall D : Rung3ResourceDerivation Axiom Target,
    r <= D.proofResource

/-- In any tree-like rank/depth derivation from resource-`k` axioms, the proof
resource is at most `k + size`. -/
theorem proofResource_le_axiomResource_add_size
    {Axiom : Rung3ResourceLine -> Prop}
    {Target : Rung3ResourceLine}
    {k : Nat}
    (Hax : Rung3AxiomsResourceAtMost Axiom k)
    (D : Rung3ResourceDerivation Axiom Target) :
    D.proofResource <= k + D.size := by
  induction D with
  | ax h =>
      have hk := Hax _ h
      simp [Rung3ResourceDerivation.proofResource,
        Rung3ResourceDerivation.size]
      omega
  | combine L R ihL ihR =>
      have hLroot := Rung3ResourceDerivation.root_resource_le_proofResource L
      have hRroot := Rung3ResourceDerivation.root_resource_le_proofResource R
      have hLbase : _ := Nat.le_trans hLroot ihL
      have hRbase : _ := Nat.le_trans hRroot ihR
      have hL' : L.proofResource <= k + (L.size + R.size + 1) := by
        exact Nat.le_trans ihL (by omega)
      have hR' : R.proofResource <= k + (L.size + R.size + 1) := by
        exact Nat.le_trans ihR (by omega)
      simp [Rung3ResourceDerivation.proofResource,
        Rung3ResourceDerivation.size, Rung3ResourceLine.combine]
      constructor
      · exact hL'
      constructor
      · exact hR'
      · constructor
        · omega
        · omega
  | step E ih =>
      have hEroot := Rung3ResourceDerivation.root_resource_le_proofResource E
      have hE' : E.proofResource <= k + (E.size + 1) := by
        exact Nat.le_trans ih (by omega)
      simp [Rung3ResourceDerivation.proofResource,
        Rung3ResourceDerivation.size, Rung3ResourceLine.step]
      exact ⟨hE', by omega⟩

/-- Resource lower bounds give tree-like size lower bounds. -/
theorem resource_lower_bound_le_axiomResource_add_size
    {Axiom : Rung3ResourceLine -> Prop}
    {Target : Rung3ResourceLine}
    {k r : Nat}
    (Hax : Rung3AxiomsResourceAtMost Axiom k)
    (Hres : Rung3ResourceLowerBound Axiom Target r)
    (D : Rung3ResourceDerivation Axiom Target) :
    r <= k + D.size :=
  Nat.le_trans (Hres D) (proofResource_le_axiomResource_add_size Hax D)

/-- No small derivation exists once the lower bound exceeds the available
resource budget. -/
theorem no_small_rung3_resource_derivation_of_lower_bound
    {Axiom : Rung3ResourceLine -> Prop}
    {Target : Rung3ResourceLine}
    {k r s : Nat}
    (Hax : Rung3AxiomsResourceAtMost Axiom k)
    (Hres : Rung3ResourceLowerBound Axiom Target r)
    (hgap : k + s < r) :
    Not (exists D : Rung3ResourceDerivation Axiom Target, D.size <= s) := by
  rintro ⟨D, hD⟩
  have hr : r <= k + D.size :=
    resource_lower_bound_le_axiomResource_add_size Hax Hres D
  have hs : k + D.size <= k + s := Nat.add_le_add_left hD k
  exact Nat.not_lt_of_ge (Nat.le_trans hr hs) hgap

/-! ## Cutting planes rank substrate -/

abbrev CuttingPlanesLine := Rung3ResourceLine
abbrev CuttingPlanesDerivation := Rung3ResourceDerivation

/-- A signed 3-CNF clause contributes an initial cutting-planes inequality with
rank zero in this substrate. -/
def SignedClause3.toCuttingPlanesLine {n : Nat}
    (_c : SignedClause3 n) : CuttingPlanesLine where
  resource := 0

/-- Cutting-planes axioms induced by a signed 3-CNF formula. -/
def SignedThreeCNFCuttingPlanesAxiom
    (φ : SignedThreeCNF) : CuttingPlanesLine -> Prop :=
  fun P => exists c : SignedClause3 φ.numVars,
    c ∈ φ.clauses /\ c.toCuttingPlanesLine = P

/-- Abstract contradiction target for cutting planes. -/
def cuttingPlanesContradictionLine : CuttingPlanesLine where
  resource := 0

abbrev SignedThreeCNFCuttingPlanesRefutation (φ : SignedThreeCNF) :=
  CuttingPlanesDerivation
    (SignedThreeCNFCuttingPlanesAxiom φ)
    cuttingPlanesContradictionLine

/-- Signed 3-CNF cutting-planes axioms start at rank zero. -/
theorem signedThreeCNFCuttingPlanesAxioms_rank_le_zero
    (φ : SignedThreeCNF) :
    Rung3AxiomsResourceAtMost (SignedThreeCNFCuttingPlanesAxiom φ) 0 := by
  intro P hP
  rcases hP with ⟨c, _hc, rfl⟩
  rfl

/-- Cutting-planes rank lower bounds rule out small tree-like refutations. -/
theorem no_small_signedThreeCNF_cuttingPlanes_refutation_of_rank_lower_bound
    (φ : SignedThreeCNF)
    {r s : Nat}
    (Hrank : Rung3ResourceLowerBound
      (SignedThreeCNFCuttingPlanesAxiom φ) cuttingPlanesContradictionLine r)
    (hgap : 0 + s < r) :
    Not (exists D : SignedThreeCNFCuttingPlanesRefutation φ, D.size <= s) :=
  no_small_rung3_resource_derivation_of_lower_bound
    (signedThreeCNFCuttingPlanesAxioms_rank_le_zero φ) Hrank hgap

/-! ## Bounded-depth Frege substrate -/

abbrev BoundedDepthFregeLine := Rung3ResourceLine
abbrev BoundedDepthFregeDerivation := Rung3ResourceDerivation

/-- A signed 3-CNF clause contributes an initial bounded-depth Frege formula of
constant depth `3` in this substrate. -/
def SignedClause3.toBoundedDepthFregeLine {n : Nat}
    (_c : SignedClause3 n) : BoundedDepthFregeLine where
  resource := 3

/-- Bounded-depth Frege axioms induced by a signed 3-CNF formula. -/
def SignedThreeCNFBoundedDepthFregeAxiom
    (φ : SignedThreeCNF) : BoundedDepthFregeLine -> Prop :=
  fun P => exists c : SignedClause3 φ.numVars,
    c ∈ φ.clauses /\ c.toBoundedDepthFregeLine = P

/-- Abstract contradiction target for bounded-depth Frege. -/
def boundedDepthFregeContradictionLine : BoundedDepthFregeLine where
  resource := 0

abbrev SignedThreeCNFBoundedDepthFregeRefutation (φ : SignedThreeCNF) :=
  BoundedDepthFregeDerivation
    (SignedThreeCNFBoundedDepthFregeAxiom φ)
    boundedDepthFregeContradictionLine

/-- Signed 3-CNF bounded-depth Frege axioms have constant starting depth `3`. -/
theorem signedThreeCNFBoundedDepthFregeAxioms_depth_le_three
    (φ : SignedThreeCNF) :
    Rung3AxiomsResourceAtMost (SignedThreeCNFBoundedDepthFregeAxiom φ) 3 := by
  intro P hP
  rcases hP with ⟨c, _hc, rfl⟩
  rfl

/-- Bounded-depth Frege depth lower bounds rule out small tree-like refutations. -/
theorem no_small_signedThreeCNF_boundedDepthFrege_refutation_of_depth_lower_bound
    (φ : SignedThreeCNF)
    {r s : Nat}
    (Hdepth : Rung3ResourceLowerBound
      (SignedThreeCNFBoundedDepthFregeAxiom φ) boundedDepthFregeContradictionLine r)
    (hgap : 3 + s < r) :
    Not (exists D : SignedThreeCNFBoundedDepthFregeRefutation φ, D.size <= s) :=
  no_small_rung3_resource_derivation_of_lower_bound
    (signedThreeCNFBoundedDepthFregeAxioms_depth_le_three φ) Hdepth hgap

/-! ## Rung-3 completion bundle -/

/-- The four formal substrates covered by rung 3 in this repository. -/
structure Rung3CompletedSubstrates (φ : SignedThreeCNF) : Prop where
  polynomialCalculus :
    forall {d s : Nat},
      PolynomialCalculusDegreeLowerBound
        (SignedThreeCNFPolynomialCalculusAxiom φ)
        polynomialCalculusContradictionLine d ->
      3 + s < d ->
      Not (exists D : SignedThreeCNFPolynomialCalculusRefutation φ, D.size <= s)
  nullstellensatz :
    forall {d s : Nat},
      NullstellensatzDegreeLowerBound
        (SignedThreeCNFPolynomialCalculusAxiom φ)
        polynomialCalculusContradictionLine d ->
      3 + s < d ->
      Not (exists D : SignedThreeCNFNullstellensatzRefutation φ, D.size <= s)
  cuttingPlanes :
    forall {r s : Nat},
      Rung3ResourceLowerBound
        (SignedThreeCNFCuttingPlanesAxiom φ) cuttingPlanesContradictionLine r ->
      0 + s < r ->
      Not (exists D : SignedThreeCNFCuttingPlanesRefutation φ, D.size <= s)
  boundedDepthFrege :
    forall {r s : Nat},
      Rung3ResourceLowerBound
        (SignedThreeCNFBoundedDepthFregeAxiom φ) boundedDepthFregeContradictionLine r ->
      3 + s < r ->
      Not (exists D : SignedThreeCNFBoundedDepthFregeRefutation φ, D.size <= s)

/-- Rung 3 is complete at the substrate level: each major rung-3 family has a
formal lower-bound interface and a proved small-tree obstruction theorem. -/
theorem rung3_completed_substrates (φ : SignedThreeCNF) :
    Rung3CompletedSubstrates φ where
  polynomialCalculus := by
    intro d s Hdeg hgap
    exact no_small_signedThreeCNF_polynomialCalculus_refutation_of_degree_lower_bound
      φ Hdeg hgap
  nullstellensatz := by
    intro d s Hdeg hgap
    exact no_small_signedThreeCNF_nullstellensatz_refutation_of_degree_lower_bound
      φ Hdeg hgap
  cuttingPlanes := by
    intro r s Hrank hgap
    exact no_small_signedThreeCNF_cuttingPlanes_refutation_of_rank_lower_bound
      φ Hrank hgap
  boundedDepthFrege := by
    intro r s Hdepth hgap
    exact no_small_signedThreeCNF_boundedDepthFrege_refutation_of_depth_lower_bound
      φ Hdepth hgap

/-! ## Kernel-only axiom trace -/

#print axioms no_small_signedThreeCNF_nullstellensatz_refutation_of_degree_lower_bound
#print axioms proofResource_le_axiomResource_add_size
#print axioms no_small_rung3_resource_derivation_of_lower_bound
#print axioms no_small_signedThreeCNF_cuttingPlanes_refutation_of_rank_lower_bound
#print axioms no_small_signedThreeCNF_boundedDepthFrege_refutation_of_depth_lower_bound
#print axioms rung3_completed_substrates

end PallLean.Paper93.DeepMath.PathB
