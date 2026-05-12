import PallLean.Paper93.DeepMath.PathB.ConcreteWFactorMembership

/-!
# Augmented concrete `W` family for the corrected Route B P-side bridge

The existing `Wiring.concreteW n hn4 sigma .adjacency` is the rename of the
local span `{1, X0 * X1}`.  That contains the adjacency factor itself, but it
does not contain the endpoint variables needed by derivative closure.  This
file records a conservative ambient replacement: each active branch is still a
small explicit span of Cook-Levin-shaped generators over `Fin n`, rather than
the full polynomial ring.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open SymmetricPowerBound
open TuringMachine
open PallLean.Paper93
open PallLean.Paper93.Spanning
open WithinProfileBound

attribute [local instance] Classical.dec

abbrev AugmentedPoly (n : ℕ) := MvPolynomial (Fin n) ℚ

def augmentedBooleanityGenerators (n : ℕ) : Set (AugmentedPoly n) :=
  {p | p = 1 ∨
      (∃ v : Fin n, p = MvPolynomial.X v) ∨
      (∃ v : Fin n, p = (MvPolynomial.X v) ^ 2)}

def augmentedAdjacencyGenerators (n : ℕ) : Set (AugmentedPoly n) :=
  {p | p = 1 ∨
      (∃ v : Fin n, p = MvPolynomial.X v) ∨
      (∃ a b : Fin n, p = MvPolynomial.X a * MvPolynomial.X b)}

def augmentedTransitionLeftGenerators (n : ℕ) : Set (AugmentedPoly n) :=
  {p | p = 1 ∨
      (∃ v : Fin n, p = MvPolynomial.X v)}

/-- A conservative corrected concrete interface family for the Route B P-side.

The adjacency case deliberately includes endpoint variables in addition to
pair products, so differentiating `X a * X b` can remain inside the same type
space.  The dormant `transitionRight` branch remains `⊥`.
-/
noncomputable def augmentedConcreteW
    (n : ℕ) (τ : ConstraintType) :
    Submodule ℚ (AugmentedPoly n) :=
  match τ with
  | .booleanity =>
      Submodule.span ℚ (augmentedBooleanityGenerators n)
  | .adjacency =>
      Submodule.span ℚ (augmentedAdjacencyGenerators n)
  | .transitionLeft =>
      Submodule.span ℚ (augmentedTransitionLeftGenerators n)
  | .transitionRight => ⊥

@[simp] theorem augmentedConcreteW_transitionRight (n : ℕ) :
    augmentedConcreteW n ConstraintType.transitionRight =
      (⊥ : Submodule ℚ (AugmentedPoly n)) := rfl

/-! ## Booleanity branch -/

theorem augmentedConcreteW_one_mem_booleanity (n : ℕ) :
    (1 : AugmentedPoly n) ∈
      augmentedConcreteW n ConstraintType.booleanity := by
  change (1 : AugmentedPoly n) ∈
    Submodule.span ℚ (augmentedBooleanityGenerators n)
  exact Submodule.subset_span (by
    exact Or.inl rfl)

theorem augmentedConcreteW_booleanity_variable_mem
    (n : ℕ) (v : Fin n) :
    (MvPolynomial.X v : AugmentedPoly n) ∈
      augmentedConcreteW n ConstraintType.booleanity := by
  change (MvPolynomial.X v : AugmentedPoly n) ∈
    Submodule.span ℚ (augmentedBooleanityGenerators n)
  exact Submodule.subset_span (by
    exact Or.inr (Or.inl ⟨v, rfl⟩))

theorem augmentedConcreteW_booleanity_square_mem
    (n : ℕ) (v : Fin n) :
    ((MvPolynomial.X v : AugmentedPoly n) ^ 2) ∈
      augmentedConcreteW n ConstraintType.booleanity := by
  change ((MvPolynomial.X v : AugmentedPoly n) ^ 2) ∈
    Submodule.span ℚ (augmentedBooleanityGenerators n)
  exact Submodule.subset_span (by
    exact Or.inr (Or.inr ⟨v, rfl⟩))

theorem augmentedConcreteW_booleanity_relation_mem
    (n : ℕ) (v : Fin n) :
    (MvPolynomial.X v - (MvPolynomial.X v) ^ 2 : AugmentedPoly n) ∈
      augmentedConcreteW n ConstraintType.booleanity := by
  exact (augmentedConcreteW n ConstraintType.booleanity).sub_mem
    (augmentedConcreteW_booleanity_variable_mem n v)
    (augmentedConcreteW_booleanity_square_mem n v)

/-- The affine booleanity factor used by the current Cook-Levin factor list. -/
theorem augmentedConcreteW_booleanity_factor_mem
    (n : ℕ) (v : Fin n) :
    (1 - MvPolynomial.X v + (MvPolynomial.X v) ^ 2 : AugmentedPoly n) ∈
      augmentedConcreteW n ConstraintType.booleanity := by
  exact (augmentedConcreteW n ConstraintType.booleanity).add_mem
    ((augmentedConcreteW n ConstraintType.booleanity).sub_mem
      (augmentedConcreteW_one_mem_booleanity n)
      (augmentedConcreteW_booleanity_variable_mem n v))
    (augmentedConcreteW_booleanity_square_mem n v)

/-! ## Adjacency branch -/

theorem augmentedConcreteW_one_mem_adjacency (n : ℕ) :
    (1 : AugmentedPoly n) ∈
      augmentedConcreteW n ConstraintType.adjacency := by
  change (1 : AugmentedPoly n) ∈
    Submodule.span ℚ (augmentedAdjacencyGenerators n)
  exact Submodule.subset_span (by
    exact Or.inl rfl)

theorem augmentedConcreteW_adjacency_variable_mem
    (n : ℕ) (v : Fin n) :
    (MvPolynomial.X v : AugmentedPoly n) ∈
      augmentedConcreteW n ConstraintType.adjacency := by
  change (MvPolynomial.X v : AugmentedPoly n) ∈
    Submodule.span ℚ (augmentedAdjacencyGenerators n)
  exact Submodule.subset_span (by
    exact Or.inr (Or.inl ⟨v, rfl⟩))

theorem augmentedConcreteW_adjacency_leftEndpoint_mem
    (n : ℕ) (a : Fin n) (_b : Fin n) :
    (MvPolynomial.X a : AugmentedPoly n) ∈
      augmentedConcreteW n ConstraintType.adjacency :=
  augmentedConcreteW_adjacency_variable_mem n a

theorem augmentedConcreteW_adjacency_rightEndpoint_mem
    (n : ℕ) (_a : Fin n) (b : Fin n) :
    (MvPolynomial.X b : AugmentedPoly n) ∈
      augmentedConcreteW n ConstraintType.adjacency :=
  augmentedConcreteW_adjacency_variable_mem n b

theorem augmentedConcreteW_adjacency_product_mem
    (n : ℕ) (a b : Fin n) :
    (MvPolynomial.X a * MvPolynomial.X b : AugmentedPoly n) ∈
      augmentedConcreteW n ConstraintType.adjacency := by
  change (MvPolynomial.X a * MvPolynomial.X b : AugmentedPoly n) ∈
    Submodule.span ℚ (augmentedAdjacencyGenerators n)
  exact Submodule.subset_span (by
    exact Or.inr (Or.inr ⟨a, b, rfl⟩))

/-- The adjacency factor used by the current Cook-Levin factor list. -/
theorem augmentedConcreteW_adjacency_factor_mem
    (n : ℕ) (a b : Fin n) :
    (1 - MvPolynomial.X a * MvPolynomial.X b : AugmentedPoly n) ∈
      augmentedConcreteW n ConstraintType.adjacency := by
  exact (augmentedConcreteW n ConstraintType.adjacency).sub_mem
    (augmentedConcreteW_one_mem_adjacency n)
    (augmentedConcreteW_adjacency_product_mem n a b)

/-! ## Transition-left branch -/

theorem augmentedConcreteW_one_mem_transitionLeft (n : ℕ) :
    (1 : AugmentedPoly n) ∈
      augmentedConcreteW n ConstraintType.transitionLeft := by
  change (1 : AugmentedPoly n) ∈
    Submodule.span ℚ (augmentedTransitionLeftGenerators n)
  exact Submodule.subset_span (by
    exact Or.inl rfl)

theorem augmentedConcreteW_transitionLeft_variable_mem
    (n : ℕ) (v : Fin n) :
    (MvPolynomial.X v : AugmentedPoly n) ∈
      augmentedConcreteW n ConstraintType.transitionLeft := by
  change (MvPolynomial.X v : AugmentedPoly n) ∈
    Submodule.span ℚ (augmentedTransitionLeftGenerators n)
  exact Submodule.subset_span (by
    exact Or.inr ⟨v, rfl⟩)

theorem augmentedConcreteW_transitionLeft_affineFactor_mem
    (n : ℕ) (v : Fin n) :
    (1 - MvPolynomial.X v : AugmentedPoly n) ∈
      augmentedConcreteW n ConstraintType.transitionLeft := by
  exact (augmentedConcreteW n ConstraintType.transitionLeft).sub_mem
    (augmentedConcreteW_one_mem_transitionLeft n)
    (augmentedConcreteW_transitionLeft_variable_mem n v)

theorem augmentedConcreteW_transitionLeftAmbientFactor_mem
    {n : ℕ} (σ : Fin 4 ↪ Fin n) :
    (transitionLeftAmbientFactor σ : AugmentedPoly n) ∈
      augmentedConcreteW n ConstraintType.transitionLeft := by
  rw [transitionLeftAmbientFactor_eq_X]
  exact augmentedConcreteW_transitionLeft_variable_mem n (σ 0)

/-! ## Factor-list H3 surface for the augmented family -/

/-- The direct branch-shape surface from `ConcreteWFactorMembership` closes H3
for the augmented family without any canonical-row transport: booleanity and
adjacency are now global ambient spans over the actual endpoint variables. -/
theorem CookLevinFactorMemPerType_augmentedConcreteW_of_directBranchShapes
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hShape : CookLevinDirectBranchShapeWitnesses M n hn htb hns hn4) :
    CookLevinFactorMemPerType M n hn htb hns
      (augmentedConcreteW n) := by
  classical
  intro i
  rcases hShape i with
    ⟨v, hType, hFactor⟩ |
    ⟨a, b, _hab, hType, hFactor⟩ |
    ⟨hType, hFactor⟩
  · rw [hType, hFactor]
    exact augmentedConcreteW_booleanity_factor_mem n v
  · rw [hType, hFactor]
    exact augmentedConcreteW_adjacency_factor_mem n a b
  · rw [hType, hFactor]
    exact augmentedConcreteW_transitionLeftAmbientFactor_mem
      (Fin.castLEEmb hn4)

/-- H3/H4/I5 closure frontier for the augmented family.  This is the exact
P-side package still needed before the existing template-collapse machinery can
be retargeted away from the old `concreteW` family. -/
def CookLevinAugmentedConcreteWClosureFrontier
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  CookLevinFactorMemPerType M n hn htb hns (augmentedConcreteW n) ∧
    DerivClosurePerType (n := n) (augmentedConcreteW n) ∧
    PerTypeShiftMlprojClosure (n := n) (augmentedConcreteW n)

/-! ## Axiom audit anchors -/

#print axioms augmentedConcreteW_one_mem_booleanity
#print axioms augmentedConcreteW_booleanity_variable_mem
#print axioms augmentedConcreteW_booleanity_square_mem
#print axioms augmentedConcreteW_booleanity_relation_mem
#print axioms augmentedConcreteW_booleanity_factor_mem
#print axioms augmentedConcreteW_one_mem_adjacency
#print axioms augmentedConcreteW_adjacency_variable_mem
#print axioms augmentedConcreteW_adjacency_leftEndpoint_mem
#print axioms augmentedConcreteW_adjacency_rightEndpoint_mem
#print axioms augmentedConcreteW_adjacency_product_mem
#print axioms augmentedConcreteW_adjacency_factor_mem
#print axioms augmentedConcreteW_one_mem_transitionLeft
#print axioms augmentedConcreteW_transitionLeft_variable_mem
#print axioms augmentedConcreteW_transitionLeft_affineFactor_mem
#print axioms augmentedConcreteW_transitionLeftAmbientFactor_mem
#print axioms CookLevinFactorMemPerType_augmentedConcreteW_of_directBranchShapes

end PallLean.Paper93.DeepMath.PathB
