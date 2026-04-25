import PallLean.Paper93.Direct.BooleanityDirect
import PallLean.Paper93.Direct.AdjacencyDirect
import PallLean.Paper93.Direct.TransitionLeftDirect
import PallLean.Paper93.Spanning.PerDerivativeSpanning

/-!
# ConcreteW factor membership frontier

This file attacks H3 for the canonical concrete row-embedding package

`fun tau => Wiring.concreteW n hn4 (Fin.castLEEmb hn4) tau`.

The direct branch theorems for booleanity and adjacency provide membership in
`concreteW` for an existential, factor-dependent embedding.  The canonical
PathB package fixes the embedding to `Fin.castLEEmb hn4`.  We therefore expose
the exact remaining transport needed to turn those existential branch facts
into H3 at the canonical row.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open TuringMachine
open SymmetricPowerBound
open WithinProfileBound
open PallLean.Paper93
open PallLean.Paper93.Bridge
open PallLean.Paper93.Direct
open PallLean.Paper93.Spanning
open PallLean.Paper93.Wiring

attribute [local instance] Classical.dec

/-! ## Canonical template membership at the fixed row -/

/-- The canonical booleanity template at slot `0` lies in the fixed
`concreteW n hn4 (Fin.castLEEmb hn4) .booleanity` row. -/
theorem canonical_booleanity_factor_mem_concreteW
    (n : ℕ) (hn4 : n ≥ 4) :
    (1 - MvPolynomial.X ((Fin.castLEEmb hn4) (0 : Fin 4))
        + (MvPolynomial.X ((Fin.castLEEmb hn4) (0 : Fin 4))) ^ 2 :
        MvPolynomial (Fin n) ℚ)
      ∈ concreteW n hn4 (Fin.castLEEmb hn4) ConstraintType.booleanity := by
  classical
  unfold concreteW
  have hOne :
      (1 : MvPolynomial (Fin n) ℚ)
        ∈ ambientPerTypeSpace perTypeInterfaceSpace n hn4
            (Fin.castLEEmb hn4) ConstraintType.booleanity :=
    one_mem_booleanityAmbient_discharged n hn4 (Fin.castLEEmb hn4)
  have hLift :
      (MvPolynomial.X ((Fin.castLEEmb hn4) (0 : Fin 4))
          - (MvPolynomial.X ((Fin.castLEEmb hn4) (0 : Fin 4))) ^ 2 :
          MvPolynomial (Fin n) ℚ)
        ∈ ambientPerTypeSpace perTypeInterfaceSpace n hn4
            (Fin.castLEEmb hn4) ConstraintType.booleanity :=
    booleanityLift_mem_ambientPerType n hn4 (Fin.castLEEmb hn4)
  have hSub :
      ((1 : MvPolynomial (Fin n) ℚ)
          - (MvPolynomial.X ((Fin.castLEEmb hn4) (0 : Fin 4))
              - (MvPolynomial.X ((Fin.castLEEmb hn4) (0 : Fin 4))) ^ 2))
        ∈ ambientPerTypeSpace perTypeInterfaceSpace n hn4
            (Fin.castLEEmb hn4) ConstraintType.booleanity :=
    (ambientPerTypeSpace perTypeInterfaceSpace n hn4
        (Fin.castLEEmb hn4) ConstraintType.booleanity).sub_mem hOne hLift
  have hEq :
      (1 - MvPolynomial.X ((Fin.castLEEmb hn4) (0 : Fin 4))
          + (MvPolynomial.X ((Fin.castLEEmb hn4) (0 : Fin 4))) ^ 2 :
          MvPolynomial (Fin n) ℚ)
        =
      (1 : MvPolynomial (Fin n) ℚ)
          - (MvPolynomial.X ((Fin.castLEEmb hn4) (0 : Fin 4))
              - (MvPolynomial.X ((Fin.castLEEmb hn4) (0 : Fin 4))) ^ 2) := by
    ring
  rw [hEq]
  exact hSub

/-- The canonical adjacency template at slots `0,1` lies in the fixed
`concreteW n hn4 (Fin.castLEEmb hn4) .adjacency` row. -/
theorem canonical_adjacency_factor_mem_concreteW
    (n : ℕ) (hn4 : n ≥ 4) :
    (1 - MvPolynomial.X ((Fin.castLEEmb hn4) (0 : Fin 4))
        * MvPolynomial.X ((Fin.castLEEmb hn4) (1 : Fin 4)) :
        MvPolynomial (Fin n) ℚ)
      ∈ concreteW n hn4 (Fin.castLEEmb hn4) ConstraintType.adjacency := by
  classical
  unfold concreteW
  have hOne :
      (1 : MvPolynomial (Fin n) ℚ)
        ∈ ambientPerTypeSpace perTypeInterfaceSpace n hn4
            (Fin.castLEEmb hn4) ConstraintType.adjacency :=
    one_mem_adjacencyAmbient_discharged n hn4 (Fin.castLEEmb hn4)
  have hProd :
      (MvPolynomial.X ((Fin.castLEEmb hn4) (0 : Fin 4))
          * MvPolynomial.X ((Fin.castLEEmb hn4) (1 : Fin 4)) :
          MvPolynomial (Fin n) ℚ)
        ∈ ambientPerTypeSpace perTypeInterfaceSpace n hn4
            (Fin.castLEEmb hn4) ConstraintType.adjacency :=
    adjacencyLift_mem_ambientPerType n hn4 (Fin.castLEEmb hn4)
  exact
    (ambientPerTypeSpace perTypeInterfaceSpace n hn4
        (Fin.castLEEmb hn4) ConstraintType.adjacency).sub_mem hOne hProd

/-- The canonical transition-left template lies in the fixed
`concreteW n hn4 (Fin.castLEEmb hn4) .transitionLeft` row. -/
theorem canonical_transitionLeft_factor_mem_concreteW
    (n : ℕ) (hn4 : n ≥ 4) :
    (transitionLeftAmbientFactor (Fin.castLEEmb hn4) :
        MvPolynomial (Fin n) ℚ)
      ∈ concreteW n hn4 (Fin.castLEEmb hn4)
          ConstraintType.transitionLeft := by
  classical
  unfold concreteW
  rw [transitionLeftAmbientFactor_eq_X]
  exact transitionLeftLift_mem_ambientPerType n hn4 (Fin.castLEEmb hn4)

/-! ## Exact canonical-shape reduction -/

/-- Per-factor canonical shape witnesses strong enough to close H3 directly.

This states that each factor is already one of the three fixed-row canonical
templates for its classified type.  It is intentionally strong: real compiled
booleanity/adjacency rows usually carry variable-dependent embeddings, so this
records the no-transport case separately from the existential direct case. -/
def CookLevinCanonicalConcreteWShapeWitnesses
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4) :
    Prop :=
  ∀ i : Fin (cookLevinFactorList M n hn htb hns).length,
    match cookLevinConstraintType M n hn htb hns i with
    | ConstraintType.booleanity =>
        (cookLevinFactorList M n hn htb hns).get i =
          (1 - MvPolynomial.X ((Fin.castLEEmb hn4) (0 : Fin 4))
              + (MvPolynomial.X ((Fin.castLEEmb hn4) (0 : Fin 4))) ^ 2 :
              MvPolynomial (Fin n) ℚ)
    | ConstraintType.adjacency =>
        (cookLevinFactorList M n hn htb hns).get i =
          (1 - MvPolynomial.X ((Fin.castLEEmb hn4) (0 : Fin 4))
              * MvPolynomial.X ((Fin.castLEEmb hn4) (1 : Fin 4)) :
              MvPolynomial (Fin n) ℚ)
    | ConstraintType.transitionLeft =>
        (cookLevinFactorList M n hn htb hns).get i =
          (transitionLeftAmbientFactor (Fin.castLEEmb hn4) :
              MvPolynomial (Fin n) ℚ)
    | ConstraintType.transitionRight =>
        False

/-- H3 closes if every classified factor is already a fixed-row canonical
template. -/
theorem CookLevinFactorMemPerType_concreteW_of_canonicalShapeWitnesses
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hShape :
      CookLevinCanonicalConcreteWShapeWitnesses M n hn htb hns hn4) :
    CookLevinFactorMemPerType M n hn htb hns
      (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau) := by
  classical
  intro i
  have hi := hShape i
  cases hType : cookLevinConstraintType M n hn htb hns i with
  | booleanity =>
    have hFactor :
        (cookLevinFactorList M n hn htb hns).get i =
          (1 - MvPolynomial.X ((Fin.castLEEmb hn4) (0 : Fin 4))
              + (MvPolynomial.X ((Fin.castLEEmb hn4) (0 : Fin 4))) ^ 2 :
              MvPolynomial (Fin n) ℚ) := by
      simpa [CookLevinCanonicalConcreteWShapeWitnesses, hType] using hi
    rw [hFactor]
    exact canonical_booleanity_factor_mem_concreteW n hn4
  | adjacency =>
    have hFactor :
        (cookLevinFactorList M n hn htb hns).get i =
          (1 - MvPolynomial.X ((Fin.castLEEmb hn4) (0 : Fin 4))
              * MvPolynomial.X ((Fin.castLEEmb hn4) (1 : Fin 4)) :
              MvPolynomial (Fin n) ℚ) := by
      simpa [CookLevinCanonicalConcreteWShapeWitnesses, hType] using hi
    rw [hFactor]
    exact canonical_adjacency_factor_mem_concreteW n hn4
  | transitionLeft =>
    have hFactor :
        (cookLevinFactorList M n hn htb hns).get i =
          (transitionLeftAmbientFactor (Fin.castLEEmb hn4) :
              MvPolynomial (Fin n) ℚ) := by
      simpa [CookLevinCanonicalConcreteWShapeWitnesses, hType] using hi
    rw [hFactor]
    exact canonical_transitionLeft_factor_mem_concreteW n hn4
  | transitionRight =>
    have hFalse : False := by
      simpa [hType] using hi
    exact False.elim hFalse

/-! ## Existential direct membership and the missing canonical transport -/

/-- The direct branch facts establish this form: each factor lands in some
`concreteW n hn4 σ tau`.  This is still weaker than the canonical H3 target,
because the PathB package fixes `σ = Fin.castLEEmb hn4`. -/
def CookLevinConcreteWExistsRowMembership
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4) :
    Prop :=
  ∀ i : Fin (cookLevinFactorList M n hn htb hns).length,
    ∃ σ : Fin 4 ↪ Fin n,
      (cookLevinFactorList M n hn htb hns).get i
        ∈ concreteW n hn4 σ
            (cookLevinConstraintType M n hn htb hns i)

/-- The exact missing transport from arbitrary direct witnesses to the
canonical fixed row.  This is deliberately restricted to the actual compiled
factor at each index, rather than claiming a false global equality between
different row-embedded `concreteW` spaces. -/
def CookLevinConcreteWCanonicalRowTransport
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4) :
    Prop :=
  ∀ (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (σ : Fin 4 ↪ Fin n),
      (cookLevinFactorList M n hn htb hns).get i
        ∈ concreteW n hn4 σ
            (cookLevinConstraintType M n hn htb hns i) →
      (cookLevinFactorList M n hn htb hns).get i
        ∈ concreteW n hn4 (Fin.castLEEmb hn4)
            (cookLevinConstraintType M n hn htb hns i)

/-- H3 reduced to the two ingredients currently separated by the direct layer:
existential row membership and transport to the canonical row. -/
theorem CookLevinFactorMemPerType_concreteW_of_existsRowMembership_transport
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hExists :
      CookLevinConcreteWExistsRowMembership M n hn htb hns hn4)
    (hTransport :
      CookLevinConcreteWCanonicalRowTransport M n hn htb hns hn4) :
    CookLevinFactorMemPerType M n hn htb hns
      (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau) := by
  intro i
  obtain ⟨σ, hσ⟩ := hExists i
  exact hTransport i σ hσ

/-- A shape package matching the existing direct branch theorems.  It reduces
the compiled factor at each index to one of the public direct branch forms,
which then gives existential row membership. -/
def CookLevinDirectBranchShapeWitnesses
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4) :
    Prop :=
  ∀ i : Fin (cookLevinFactorList M n hn htb hns).length,
    (∃ v : Fin n,
        cookLevinConstraintType M n hn htb hns i =
          ConstraintType.booleanity ∧
        (cookLevinFactorList M n hn htb hns).get i =
          (1 - MvPolynomial.X v + (MvPolynomial.X v) ^ 2 :
              MvPolynomial (Fin n) ℚ)) ∨
    (∃ a b : Fin n,
        a ≠ b ∧
        cookLevinConstraintType M n hn htb hns i =
          ConstraintType.adjacency ∧
        (cookLevinFactorList M n hn htb hns).get i =
          (1 - MvPolynomial.X a * MvPolynomial.X b :
              MvPolynomial (Fin n) ℚ)) ∨
    (cookLevinConstraintType M n hn htb hns i =
        ConstraintType.transitionLeft ∧
      (cookLevinFactorList M n hn htb hns).get i =
        (transitionLeftAmbientFactor (Fin.castLEEmb hn4) :
            MvPolynomial (Fin n) ℚ))

/-- Existing direct branch theorems give existential row membership once the
actual compiled factor is identified with their branch-local polynomial. -/
theorem CookLevinConcreteWExistsRowMembership_of_directBranchShapeWitnesses
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hShape : CookLevinDirectBranchShapeWitnesses M n hn htb hns hn4) :
    CookLevinConcreteWExistsRowMembership M n hn htb hns hn4 := by
  classical
  intro i
  rcases hShape i with
    ⟨v, hType, hFactor⟩ |
    ⟨a, b, hab, hType, hFactor⟩ |
    ⟨hType, hFactor⟩
  · obtain ⟨σ, hσ⟩ :=
      booleanity_factor_direct_mem M n hn htb hns v hn4
    refine ⟨σ, ?_⟩
    rw [hType, hFactor]
    exact hσ
  · obtain ⟨σ, hσ⟩ :=
      adjacency_factor_direct_mem M n hn htb hns a b hn4 hab
    refine ⟨σ, ?_⟩
    rw [hType, hFactor]
    exact hσ
  · refine ⟨Fin.castLEEmb hn4, ?_⟩
    rw [hType, hFactor]
    exact canonical_transitionLeft_factor_mem_concreteW n hn4

/-- Combined reduction for the concrete H3 target: branch-local factor
identification plus the per-factor canonical-row transport closes H3. -/
theorem CookLevinFactorMemPerType_concreteW_of_directBranchShapes_transport
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hShape : CookLevinDirectBranchShapeWitnesses M n hn htb hns hn4)
    (hTransport :
      CookLevinConcreteWCanonicalRowTransport M n hn htb hns hn4) :
    CookLevinFactorMemPerType M n hn htb hns
      (fun tau => concreteW n hn4 (Fin.castLEEmb hn4) tau) :=
  CookLevinFactorMemPerType_concreteW_of_existsRowMembership_transport
    M n hn htb hns hn4
    (CookLevinConcreteWExistsRowMembership_of_directBranchShapeWitnesses
      M n hn htb hns hn4 hShape)
    hTransport

/-! ## Axiom audit anchors -/

#print axioms canonical_booleanity_factor_mem_concreteW
#print axioms canonical_adjacency_factor_mem_concreteW
#print axioms canonical_transitionLeft_factor_mem_concreteW
#print axioms CookLevinFactorMemPerType_concreteW_of_canonicalShapeWitnesses
#print axioms CookLevinFactorMemPerType_concreteW_of_existsRowMembership_transport
#print axioms CookLevinConcreteWExistsRowMembership_of_directBranchShapeWitnesses
#print axioms CookLevinFactorMemPerType_concreteW_of_directBranchShapes_transport

end PallLean.Paper93.DeepMath.PathB
