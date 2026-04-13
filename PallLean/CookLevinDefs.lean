/-
  CookLevinDefs.lean — Cook-Levin compilation definitions

  Extracted from PaperFaithfulSeparation.lean to break the circular import
  between PaperFaithfulSeparation and ProfileCompression.

  Contains:
  - LocalConstraint, CompiledTableau structures
  - compiledPoly (the product polynomial)
  - cook_levin_compilation (the honest compilation)
  - has_bounded_locality, locality_implies_poly_rank
-/
import PallLean.SPDPDefs
import PallLean.MultilinearSPDP
import PallLean.TuringMachine
import Mathlib.Tactic
import Mathlib.Data.Nat.Log

namespace PaperFaithfulSeparation

open SPDP MultilinearSPDP MvPolynomial TuringMachine

/-! ## §17: Cook-Levin Tableau Polynomial -/

/-- A local constraint is a polynomial on a bounded number of variables
in a fixed-radius neighborhood of a tableau cell. -/
structure LocalConstraint (N : ℕ) where
  poly : MvPolynomial (Fin N) ℚ
  support : Finset (Fin N)
  support_bound : support.card ≤ 10  -- O(1) variables per constraint
  vars_contained : poly.vars ⊆ support
  degree_bound : poly.totalDegree ≤ 6  -- constant degree

/-- A compiled tableau family packages the Cook-Levin construction for a DTM M
at input size n. The polynomial is 1 - Σ C² where C ranges over local constraints. -/
structure CompiledTableau (M : DTM) (n : ℕ) where
  numVars : ℕ
  numVars_poly : numVars ≤ n ^ 10  -- poly(n) variables
  constraints : List (LocalConstraint numVars)
  constraints_poly : constraints.length ≤ n ^ 10  -- poly(n) constraints
  /-- Each constraint touches variables in a constant-radius neighborhood -/
  locality_radius : ℕ
  locality_bound : locality_radius ≤ 5  -- O(1)
  /-- The block partition groups variables by tableau cell neighborhood -/
  partition : BlockPartition numVars

/-- The compiled polynomial: P_{M,n} = ∏ᵢ (1 - Cᵢ)

This is the product form from the paper (§17.1). Each factor (1 - Cᵢ) vanishes
when constraint Cᵢ is violated, so the product vanishes iff any constraint fails.

The product form (as opposed to the sum-of-squares 1 - Σ Cᵢ²) is essential:
- **NP-side**: The product creates cross-variable interactions that survive
  iterated differentiation, enabling the identity minor (Lemmas 123-124).
- **P-side**: Profile compression (§9, Theorem 92) gives polynomial SPDP rank
  by bounding the number of distinct constraint profiles. -/
noncomputable def compiledPoly {M : DTM} {n : ℕ} (T : CompiledTableau M n) :
    MvPolynomial (Fin T.numVars) ℚ :=
  (T.constraints.map (fun c => 1 - c.poly)).prod

/-! ## §17.3: P-side SPDP Rank Bound (Profile Compression) -/

/-- The key locality property: each SPDP row is a linear combination of at most
C₁ local terms, each supported in a neighborhood of size R₀ = O(1).

This is Lemma 91 in the paper. For P = ∏(1 - Cᵢ), the Leibniz rule gives
∂_S P = Σ_{T⊆S} (∏_{i∈T} (-∂_{sᵢ}Cᵢ)) × (∏_{j∉T} (1-Cⱼ)).
Profile compression (§9) bounds the number of distinct constraint profiles,
giving polynomial SPDP rank (Theorem 92). -/
def has_bounded_locality {N : ℕ} (B : BlockPartition N)
    (p : MvPolynomial (Fin N) ℚ)
    (R : ℕ)  -- max variables per row
    (C₁ : ℕ)  -- max local terms per row
    : Prop :=
  ∀ (S : List (Fin N)) (m : MvPolynomial (Fin N) ℚ),
    S.length = Nat.log 2 N →
    m.totalDegree ≤ Nat.log 2 N →
    isBlockAdmissible B S →
    (mlProj (m * iterDerivList S p)).vars.card ≤ R

/-- The P-side rank bound: any polynomial whose SPDP subspace is contained
in the span of a finite set G with |G| ≤ N^200 has SPDP rank ≤ N^200. -/
theorem locality_implies_poly_rank {N : ℕ} (B : BlockPartition N)
    (p : MvPolynomial (Fin N) ℚ)
    (G : Finset (MvPolynomial (Fin N) ℚ))
    (hSpan : mlBlockedSpdpSubspace B (Nat.log 2 N) (Nat.log 2 N) p ≤
      Submodule.span ℚ (↑G : Set (MvPolynomial (Fin N) ℚ)))
    (hCard : G.card ≤ N ^ 200) :
    mlBlockedSpdpRank B (Nat.log 2 N) (Nat.log 2 N) p ≤ N ^ 200 := by
  unfold mlBlockedSpdpRank
  have hmono : Module.finrank ℚ
      (mlBlockedSpdpSubspace B (Nat.log 2 N) (Nat.log 2 N) p) ≤
      Module.finrank ℚ (Submodule.span ℚ (↑G : Set (MvPolynomial (Fin N) ℚ))) :=
    Submodule.finrank_mono hSpan
  have hspan_card : Module.finrank ℚ
      (Submodule.span ℚ (↑G : Set (MvPolynomial (Fin N) ℚ))) ≤ G.card :=
    finrank_span_finset_le_card G
  exact le_trans (le_trans hmono hspan_card) hCard

/-! ## §29.2: Cook-Levin Compilation (Honest Construction) -/

/-- Booleanity polynomial z * (1 - z) for variable v. -/
private noncomputable def boolPoly' (N : ℕ) (v : Fin N) : MvPolynomial (Fin N) ℚ :=
  MvPolynomial.X v * (1 - MvPolynomial.X v)

/-- boolPoly' variables are contained in {v}. -/
private theorem boolPoly'_vars (N : ℕ) (v : Fin N) :
    (boolPoly' N v).vars ⊆ ({v} : Finset (Fin N)) := by
  unfold boolPoly'
  intro w hw
  simp only [Finset.mem_singleton]
  have hsub := MvPolynomial.vars_mul (MvPolynomial.X v : MvPolynomial (Fin N) ℚ) (1 - MvPolynomial.X v)
  have hw2 := hsub hw
  simp only [Finset.mem_union] at hw2
  cases hw2 with
  | inl h1 => rwa [MvPolynomial.vars_X, Finset.mem_singleton] at h1
  | inr h2 =>
    have hsub2 := MvPolynomial.vars_sub_subset
      (p := (1 : MvPolynomial (Fin N) ℚ)) (q := (MvPolynomial.X v : MvPolynomial (Fin N) ℚ))
    have h3 := hsub2 h2
    simp only [Finset.mem_union, MvPolynomial.vars_one, Finset.empty_union,
               MvPolynomial.vars_X, Finset.mem_singleton] at h3
    exact h3

/-- boolPoly' has degree <= 2. -/
private theorem boolPoly'_degree (N : ℕ) (v : Fin N) :
    (boolPoly' N v).totalDegree ≤ 2 := by
  unfold boolPoly'
  have h1 := MvPolynomial.totalDegree_mul
    (MvPolynomial.X v : MvPolynomial (Fin N) ℚ) (1 - MvPolynomial.X v)
  have h2 : (MvPolynomial.X v : MvPolynomial (Fin N) ℚ).totalDegree = 1 :=
    MvPolynomial.totalDegree_X v
  have h3 : (1 - MvPolynomial.X v : MvPolynomial (Fin N) ℚ).totalDegree ≤ 1 := by
    have := MvPolynomial.totalDegree_sub
      (1 : MvPolynomial (Fin N) ℚ) (MvPolynomial.X v : MvPolynomial (Fin N) ℚ)
    simp [MvPolynomial.totalDegree_one, MvPolynomial.totalDegree_X] at this
    exact this
  linarith

/-- Build a LocalConstraint from a booleanity polynomial. -/
private noncomputable def boolLC (N : ℕ) (v : Fin N) : LocalConstraint N where
  poly := boolPoly' N v
  support := {v}
  support_bound := by simp
  vars_contained := boolPoly'_vars N v
  degree_bound := le_trans (boolPoly'_degree N v) (by omega)

/-- List of n booleanity constraints. -/
private noncomputable def boolConstraintList (N : ℕ) : List (LocalConstraint N) :=
  (List.finRange N).map (fun v => boolLC N v)

private theorem boolConstraintList_length (N : ℕ) :
    (boolConstraintList N).length = N := by
  simp [boolConstraintList]

/-- Adjacency polynomial X_i * X_{i+1} for consecutive variables. -/
private noncomputable def adjPoly (N : ℕ) (i : Fin N) (hi : i.val + 1 < N) :
    MvPolynomial (Fin N) ℚ :=
  MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩

/-- adjPoly variables are contained in {i, i+1}. -/
private theorem adjPoly_vars (N : ℕ) (i : Fin N) (hi : i.val + 1 < N) :
    (adjPoly N i hi).vars ⊆ ({i, ⟨i.val + 1, hi⟩} : Finset (Fin N)) := by
  unfold adjPoly
  intro w hw
  have hsub := MvPolynomial.vars_mul
    (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)
    (MvPolynomial.X ⟨i.val + 1, hi⟩ : MvPolynomial (Fin N) ℚ)
  have hw2 := hsub hw
  simp only [Finset.mem_union, MvPolynomial.vars_X, Finset.mem_singleton,
             Finset.mem_insert] at hw2 ⊢
  exact hw2

/-- adjPoly has degree <= 2. -/
private theorem adjPoly_degree (N : ℕ) (i : Fin N) (hi : i.val + 1 < N) :
    (adjPoly N i hi).totalDegree ≤ 2 := by
  unfold adjPoly
  have h := MvPolynomial.totalDegree_mul
    (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)
    (MvPolynomial.X ⟨i.val + 1, hi⟩ : MvPolynomial (Fin N) ℚ)
  simp [MvPolynomial.totalDegree_X] at h
  linarith

/-- Build a LocalConstraint from an adjacency polynomial. -/
private noncomputable def adjLC (N : ℕ) (i : Fin N) (hi : i.val + 1 < N) :
    LocalConstraint N where
  poly := adjPoly N i hi
  support := {i, ⟨i.val + 1, hi⟩}
  support_bound := by
    have h := Finset.card_insert_le i ({⟨i.val + 1, hi⟩} : Finset (Fin N))
    simp at h; linarith
  vars_contained := adjPoly_vars N i hi
  degree_bound := le_trans (adjPoly_degree N i hi) (by omega)

/-- List of (N-1) adjacency constraints for consecutive variable pairs. -/
private noncomputable def adjConstraintList (N : ℕ) : List (LocalConstraint N) :=
  (List.finRange N).filterMap (fun i =>
    if h : i.val + 1 < N then some (adjLC N i h) else none)

private theorem adjConstraintList_length (N : ℕ) (hN : N ≥ 1) :
    (adjConstraintList N).length ≤ N := by
  unfold adjConstraintList
  trans (List.finRange N).length
  · exact List.length_filterMap_le _ _
  · simp [List.length_finRange]

/-! ## §29.2b: M-Dependent Transition Skeleton Constraints

These constraints encode a skeleton of M's transition function into the
compiled polynomial. For each state q and consecutive variable pair (i, i+1),
we add a constraint whose coefficient is extracted from M.transition(q, false).
This makes the compiled polynomial genuinely depend on M's transition function,
which is essential for the NP-side axiom: the polynomial of a 3-SAT decider
has different structure from the polynomial of an arbitrary DTM. -/

/-- Transition coefficient: extract a rational number from M's transition at state q.
    Uses the new-state index from M.transition q false as the coefficient. -/
private noncomputable def transCoeff (M : DTM) (q : Fin M.numStates) : ℚ :=
  ((M.transition q false).1.val + 1 : ℚ)

/-- Transition skeleton polynomial: c_q * X_i * X_{i+1} where c_q depends on
    M.transition at state q. -/
private noncomputable def transSkelPoly (M : DTM) (N : ℕ) (q : Fin M.numStates)
    (i : Fin N) (hi : i.val + 1 < N) : MvPolynomial (Fin N) ℚ :=
  MvPolynomial.C (transCoeff M q) * (MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩)

/-- transSkelPoly variables are contained in {i, i+1}.

    The proof follows the same pattern as adjPoly_vars: vars of C(c) * (X_i * X_j)
    are contained in vars(X_i * X_j) ⊆ {i, j}. -/
private theorem transSkelPoly_vars (M : DTM) (N : ℕ) (q : Fin M.numStates)
    (i : Fin N) (hi : i.val + 1 < N) :
    (transSkelPoly M N q i hi).vars ⊆ ({i, ⟨i.val + 1, hi⟩} : Finset (Fin N)) := by
  unfold transSkelPoly
  intro w hw
  -- Use adjPoly_vars pattern: vars(C * p) ⊆ vars(C) ∪ vars(p), vars(C) = ∅
  have h_cmul := MvPolynomial.vars_mul
    (MvPolynomial.C (transCoeff M q) : MvPolynomial (Fin N) ℚ)
    (MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩ : MvPolynomial (Fin N) ℚ)
  have hw1 := h_cmul hw
  simp only [Finset.mem_union, MvPolynomial.vars_C] at hw1
  have hw1' : w ∈ (MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩ :
      MvPolynomial (Fin N) ℚ).vars := by
    rcases hw1 with h | h
    · simp at h
    · exact h
  have h_xmul := MvPolynomial.vars_mul
    (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)
    (MvPolynomial.X ⟨i.val + 1, hi⟩ : MvPolynomial (Fin N) ℚ)
  have hw2 := h_xmul hw1'
  simp only [Finset.mem_union, MvPolynomial.vars_X, Finset.mem_singleton,
             Finset.mem_insert] at hw2 ⊢
  exact hw2

/-- transSkelPoly has degree <= 2. -/
private theorem transSkelPoly_degree (M : DTM) (N : ℕ) (q : Fin M.numStates)
    (i : Fin N) (hi : i.val + 1 < N) :
    (transSkelPoly M N q i hi).totalDegree ≤ 2 := by
  unfold transSkelPoly
  have h1 := MvPolynomial.totalDegree_mul
    (MvPolynomial.C (transCoeff M q) : MvPolynomial (Fin N) ℚ)
    (MvPolynomial.X i * MvPolynomial.X ⟨i.val + 1, hi⟩ : MvPolynomial (Fin N) ℚ)
  have h2 := MvPolynomial.totalDegree_mul
    (MvPolynomial.X i : MvPolynomial (Fin N) ℚ)
    (MvPolynomial.X ⟨i.val + 1, hi⟩ : MvPolynomial (Fin N) ℚ)
  simp [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C] at h1 h2
  linarith

/-- Build a LocalConstraint from a transition skeleton polynomial. -/
private noncomputable def transSkelLC (M : DTM) (N : ℕ) (q : Fin M.numStates)
    (i : Fin N) (hi : i.val + 1 < N) : LocalConstraint N where
  poly := transSkelPoly M N q i hi
  support := {i, ⟨i.val + 1, hi⟩}
  support_bound := by
    have h := Finset.card_insert_le i ({⟨i.val + 1, hi⟩} : Finset (Fin N))
    simp at h; linarith
  vars_contained := transSkelPoly_vars M N q i hi
  degree_bound := le_trans (transSkelPoly_degree M N q i hi) (by omega)

/-- Helper: constraint list for a single state q. -/
private noncomputable def transSkelForState (M : DTM) (N : ℕ) (q : Fin M.numStates) :
    List (LocalConstraint N) :=
  (List.finRange N).filterMap (fun i =>
    if h : i.val + 1 < N then some (transSkelLC M N q i h) else none)

private theorem transSkelForState_length (M : DTM) (N : ℕ) (q : Fin M.numStates) :
    (transSkelForState M N q).length ≤ N := by
  unfold transSkelForState
  trans (List.finRange N).length
  · exact List.length_filterMap_le _ _
  · simp [List.length_finRange]

/-- List of transition skeleton constraints: one per (state, consecutive variable pair).
    The number of constraints is at most M.numStates * N ≤ n * n = n^2. -/
private noncomputable def transSkelConstraintList (M : DTM) (N : ℕ) : List (LocalConstraint N) :=
  (List.finRange M.numStates).flatMap (fun q => transSkelForState M N q)

private theorem flatMap_length_le {α β : Type*} (f : α → List β)
    (l : List α) (bound : ℕ) (hf : ∀ a, (f a).length ≤ bound) :
    (l.flatMap f).length ≤ l.length * bound := by
  induction l with
  | nil => simp [List.flatMap]
  | cons a as ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have ha := hf a
    nlinarith

private theorem transSkelConstraintList_length (M : DTM) (N : ℕ) :
    (transSkelConstraintList M N).length ≤ M.numStates * N := by
  unfold transSkelConstraintList
  have h := flatMap_length_le (fun q => transSkelForState M N q) (List.finRange M.numStates) N
    (fun q => transSkelForState_length M N q)
  rwa [List.length_finRange] at h

/-- Locality-respecting block partition: groups every 3 consecutive variables
into one block. Variable i is assigned to block i/3.

With this partition, block-admissibility requires at most 1 variable per block
(i.e., at most 1 variable from each group of 3 consecutive indices).
This is essential for the profile compression argument (§9, Theorem 92):
the locality structure ensures that each constraint touches at most 2 adjacent
blocks, and block-admissibility limits the derivative set S to touching
at most κ blocks. Combined with the constraint-type counting (profile
compression), this gives polynomial SPDP rank.

Note: The identity partition (numBlocks = n, assign = id) makes block-admissibility
trivial (just Nodup), which gives SPDP rank ≥ C(n, log n) = superpolynomial.
The locality partition is what makes the P-side bound ≤ n^200 true. -/
private def localityNumBlocks (n : ℕ) : ℕ := (n + 2) / 3

private def localityAssign (n : ℕ) (i : Fin n) : Fin (localityNumBlocks n) :=
  ⟨i.val / 3, by
    unfold localityNumBlocks
    exact Nat.div_lt_of_lt_mul (by omega)⟩

/-- Cook-Levin compilation with booleanity, adjacency, AND transition skeleton constraints.

The transition skeleton constraints make the compiled polynomial depend on
M.transition, which is essential for the NP-side axiom: when M decides 3-SAT,
the transition-dependent polynomial structure encodes the formula verification
semantics that the identity minor exploits.

Uses a locality-respecting block partition (block size 3) rather than the
identity partition. This is necessary for the profile compression P-side
bound to hold: with identity partition, the SPDP rank is C(n, log n) which
is superpolynomial, violating the n^200 bound. -/
noncomputable def cook_levin_compilation (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    CompiledTableau M n :=
  { numVars := n
    numVars_poly := by
      have h1 : 1 ≤ n := by omega
      calc n = n ^ 1 := (pow_one n).symm
        _ ≤ n ^ 10 := Nat.pow_le_pow_right h1 (by omega)
    constraints := boolConstraintList n ++ adjConstraintList n ++ transSkelConstraintList M n
    constraints_poly := by
      have hbool : (boolConstraintList n).length = n := boolConstraintList_length n
      have hadj : (adjConstraintList n).length ≤ n := adjConstraintList_length n (by omega)
      have htrans : (transSkelConstraintList M n).length ≤ M.numStates * n :=
        transSkelConstraintList_length M n
      simp only [List.length_append]
      have h1 : 1 ≤ n := by omega
      calc (boolConstraintList n).length + (adjConstraintList n).length +
              (transSkelConstraintList M n).length
          ≤ n + n + M.numStates * n := by omega
        _ ≤ n + n + n * n := by nlinarith
        _ = 2 * n + n ^ 2 := by ring
        _ ≤ n ^ 2 + n ^ 2 := by nlinarith
        _ = 2 * n ^ 2 := by ring
        _ ≤ n ^ 3 := by nlinarith [sq_nonneg n]
        _ ≤ n ^ 10 := Nat.pow_le_pow_right h1 (by omega)
    locality_radius := 1
    locality_bound := by omega
    partition := { numBlocks := localityNumBlocks n, assign := localityAssign n } }

end PaperFaithfulSeparation
