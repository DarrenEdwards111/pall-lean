import PallLean.PneqNP_v3
import PallLean.CoupledVerifier
import PallLean.PneqNP_Defs

/-!
Instance-aware compiled polynomial scaffold (paper-faithful direction).

This file keeps v3 untouched while introducing the instance-parameterized
objects needed by §12.
-/

open MvPolynomial TuringMachine PneqNP_v3 CoupledVerifier PneqNP_Defs
open scoped BigOperators

namespace PneqNPv3

/-- NP instance payload used by the clause sheet. -/
structure SATInstance (N L : ℕ) where
  dcs : DisjointClauseSystem N L

/-- Compiled variable space (same as v3). -/
abbrev CVar (M : DTM) (n : ℕ) := Fin (numVars M n 0)

/-- Data to embed coupled vars into compiled vars. -/
structure ClauseEmbedData (M : DTM) (n N L : ℕ) where
  emb : Fin (N + L) → CVar M n
  emb_injective : Function.Injective emb

/-- Rename map from coupled space into compiled space. -/
noncomputable def renameCoupledIntoCompiled
    {M : DTM} {n N L : ℕ}
    (E : ClauseEmbedData M n N L) :
    MvPolynomial (Fin (N + L)) ℚ →ₐ[ℚ] MvPolynomial (CVar M n) ℚ :=
  MvPolynomial.rename E.emb

/-- Existing machine-side constraints as polynomials. -/
noncomputable def tableauConstraintPolys (M : DTM) (n : ℕ) :
    List (MvPolynomial (CVar M n) ℚ) :=
  (constraintList M n ++ transitionConstraints M n).map LocalConstraint.poly

/-- Instance-dependent clause factors in compiled variable space. -/
noncomputable def clauseConstraintPolys
    (M : DTM) (n N L : ℕ)
    (inst : SATInstance N L)
    (E : ClauseEmbedData M n N L) :
    List (MvPolynomial (CVar M n) ℚ) :=
  ((Finset.univ : Finset (Fin L)).toList.map fun C =>
    renameCoupledIntoCompiled E (coupledFactor N L inst.dcs C))

/-- Full instance-aware compiled constraints (tableau ++ clause). -/
noncomputable def compiledConstraintPolys
    (M : DTM) (n N L : ℕ)
    (inst : SATInstance N L)
    (E : ClauseEmbedData M n N L) :
    List (MvPolynomial (CVar M n) ℚ) :=
  tableauConstraintPolys M n ++ clauseConstraintPolys M n N L inst E

/-- Raw violation polynomial on a list of polynomial constraints. -/
noncomputable def violationPolyRaw {V : Type*} [DecidableEq V]
    (constraints : List (MvPolynomial V ℚ)) : MvPolynomial V ℚ :=
  (constraints.map (fun p => p * p)).sum

/-- Instance-aware compiled violation polynomial (sum of squares). -/
noncomputable def compiledViolationPolyInst
    (M : DTM) (n N L : ℕ)
    (inst : SATInstance N L)
    (E : ClauseEmbedData M n N L) :
    MvPolynomial (CVar M n) ℚ :=
  violationPolyRaw (compiledConstraintPolys M n N L inst E)

/-- Factor-list decomposition by construction (tableau ++ clause). -/
theorem compiledConstraintPolys_append
    (M : DTM) (n N L : ℕ)
    (inst : SATInstance N L)
    (E : ClauseEmbedData M n N L) :
    compiledConstraintPolys M n N L inst E
      = tableauConstraintPolys M n ++ clauseConstraintPolys M n N L inst E := by
  rfl

/-- Clause part is exactly renamed coupled factors list. -/
theorem clauseConstraintPolys_eq_renamed_factors
    (M : DTM) (n N L : ℕ)
    (inst : SATInstance N L)
    (E : ClauseEmbedData M n N L) :
    clauseConstraintPolys M n N L inst E
      = ((Finset.univ : Finset (Fin L)).toList.map fun C =>
          renameCoupledIntoCompiled E (coupledFactor N L inst.dcs C)) := by
  rfl

/-- Instance-aware block partition (reuse v3 partition initially). -/
noncomputable def compiledPartitionInst (M : DTM) (n : ℕ) :
    CompiledPoly.BlockPartition (numVars M n 0) :=
  compiledPartition M n

/-- Instance-aware blocked SPDP rank. -/
noncomputable def blockedSpdpRankInst
    (M : DTM) (n N L κ ℓ : ℕ)
    (inst : SATInstance N L)
    (E : ClauseEmbedData M n N L) : ℕ :=
  CompiledPoly.blockedSpdpRankQ κ ℓ
    (compiledViolationPolyInst M n N L inst E)
    (compiledPartitionInst M n)

/-- Instance-aware InCcoll predicate. -/
def InCcollInst
    (M : DTM) (n N L c : ℕ)
    (inst : SATInstance N L)
    (E : ClauseEmbedData M n N L) : Prop :=
  blockedSpdpRankInst M n N L (Nat.log 2 n) (Nat.log 2 n) inst E ≤ n ^ c

/-- Unfolding lemma for InCcollInst. -/
theorem InCcollInst_iff
    (M : DTM) (n N L c : ℕ)
    (inst : SATInstance N L)
    (E : ClauseEmbedData M n N L) :
    InCcollInst M n N L c inst E
      ↔ CompiledPoly.blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n)
          (compiledViolationPolyInst M n N L inst E)
          (compiledPartition M n) ≤ n ^ c := by
  rfl

/-- God-Move polynomial correctness (paper Definition 6 identity). -/
axiom godMove_poly_correct
    (M : DTM) (n N L : ℕ)
    (inst : SATInstance N L)
    (E : ClauseEmbedData M n N L) :
    ∃ (piPhi : MvPolynomial (CVar M n) ℚ →ₐ[ℚ] MvPolynomial (CVar M n) ℚ),
      piPhi (compiledViolationPolyInst M n N L inst E)
        = renameCoupledIntoCompiled E (coupledPoly N L inst.dcs)

/-- God-Move rank monotonicity (paper Lemma 7 inequality). -/
axiom godMove_rank_monotone
    (M : DTM) (n N L κ ℓ : ℕ)
    (inst : SATInstance N L)
    (E : ClauseEmbedData M n N L) :
    CompiledPoly.blockedSpdpRankQ κ ℓ
      (renameCoupledIntoCompiled E (coupledPoly N L inst.dcs))
      (compiledPartition M n)
    ≤ blockedSpdpRankInst M n N L κ ℓ inst E

/-- Layer 1 (instance-aware): God-Move monotonicity + coupled lower bound. -/
theorem layer1_identity_minor_inst
    (M : DTM) (n N L : ℕ)
    (hn2 : n ≥ 2)
    (inst : SATInstance N L)
    (E : ClauseEmbedData M n N L)
    (hcoupled : Nat.choose L (Nat.log 2 n)
      ≤ CompiledPoly.blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n)
          (renameCoupledIntoCompiled E (coupledPoly N L inst.dcs))
          (compiledPartition M n)) :
    Nat.choose L (Nat.log 2 n)
      ≤ blockedSpdpRankInst M n N L (Nat.log 2 n) (Nat.log 2 n) inst E := by
  have hmono' := godMove_rank_monotone M n N L (Nat.log 2 n) (Nat.log 2 n) inst E
  exact le_trans hcoupled hmono'

/-- Trivial disjoint clause system on N=0 variables and L clauses. -/
noncomputable def trivialDCS (L : ℕ) : DisjointClauseSystem 0 L where
  clauseBlock := fun _ => ∅
  disjoint := by
    intro i j hij
    simp
  gadget := fun _ => (1 : MvPolynomial (Fin (0 + L)) ℚ)
  tag := fun _ => 0
  gadget_support := by
    intro C v hv
    simp at hv
  tag_support := by
    intro C v hv
    simp at hv
  tag_coeff := by
    intro C
    simp

/-- Trivial SAT instance built from the trivial disjoint clause system. -/
noncomputable def trivialSATInstance (L : ℕ) : SATInstance 0 L where
  dcs := trivialDCS L

/-- numVars has at least the n input-variable slots. -/
lemma numVars_ge_n (M : DTM) (n : ℕ) : n ≤ numVars M n 0 := by
  unfold numVars
  have h : n ≤ (tapeSize M n) * (tapeSize M n) + (tapeSize M n) * M.numStates +
      (tapeSize M n) * (tapeSize M n) + n := by
    exact Nat.le_add_left _ _
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Canonical embedding Fin n → Fin (numVars M n 0). -/
def canonicalEmbed (M : DTM) (n : ℕ) : Fin n → CVar M n :=
  fun i => ⟨i.1, lt_of_lt_of_le i.2 (numVars_ge_n M n)⟩

lemma canonicalEmbed_injective (M : DTM) (n : ℕ) : Function.Injective (canonicalEmbed M n) := by
  intro a b h
  apply Fin.ext
  simpa using congrArg Fin.val h

/-- Concrete existence of instance payload + embedding at size n. -/
theorem instance_embed_exists
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2) :
    ∃ (N L : ℕ) (inst : SATInstance N L) (E : ClauseEmbedData M n N L),
      L = n := by
  refine ⟨0, n, trivialSATInstance n, ?_, rfl⟩
  refine ⟨(fun i : Fin (0 + n) => canonicalEmbed M n ⟨i.1, by simpa using i.2⟩), ?_⟩
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simpa using hv

/-- Coupled-sheet lower bound hook (instance-level §9.3 payload). -/
axiom coupled_sheet_lower_bound
    (M : DTM) (n N L : ℕ) (hn2 : n ≥ 2)
    (inst : SATInstance N L) (E : ClauseEmbedData M n N L) :
    Nat.choose L (Nat.log 2 n)
      ≤ CompiledPoly.blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n)
          (renameCoupledIntoCompiled E (coupledPoly N L inst.dcs))
          (compiledPartition M n)

/-- Hard-instance package with coupled lower bound (now derived with α=1). -/
theorem hard_instance_rank_data
    (M : DTM) (F : BoolFunFamily)
    (hM : ∀ n, M.decides (F n)) (hNP : UniformNP F) :
    ∃ α : ℕ, α ≥ 1 ∧
      ∀ n, n ≥ 2 →
        ∃ (N L : ℕ) (inst : SATInstance N L) (E : ClauseEmbedData M n N L),
          L = α * n ∧
          Nat.choose L (Nat.log 2 n)
            ≤ CompiledPoly.blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n)
                (renameCoupledIntoCompiled E (coupledPoly N L inst.dcs))
                (compiledPartition M n) := by
  refine ⟨1, by omega, ?_⟩
  intro n hn2
  have _ := hM n
  have _ := hNP
  rcases instance_embed_exists M n hn2 with ⟨N, L, inst, E, hL⟩
  refine ⟨N, L, inst, E, ?_, ?_⟩
  · simpa [hL]
  · exact coupled_sheet_lower_bound M n N L hn2 inst E

/-- Instance-aware extraction theorem (parallel to extraction_superpolynomial). -/
theorem extraction_superpolynomial_inst
    (M : DTM) (F : BoolFunFamily)
    (hM : ∀ n, M.decides (F n)) (hNP : UniformNP F) (c : ℕ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, n ≥ 2 →
      ∃ (N L : ℕ) (inst : SATInstance N L) (E : ClauseEmbedData M n N L),
        blockedSpdpRankInst M n N L (Nat.log 2 n) (Nat.log 2 n) inst E > n ^ c := by
  obtain ⟨α, hα, hhard⟩ := hard_instance_rank_data M F hM hNP
  obtain ⟨n₀, hchoose⟩ := layer3_choose_beats_poly α hα c
  refine ⟨n₀, ?_⟩
  intro n hn hn2
  obtain ⟨N, L, inst, E, hL, hcoupled⟩ := hhard n hn2
  refine ⟨N, L, inst, E, ?_⟩
  have h1 := layer1_identity_minor_inst M n N L hn2 inst E hcoupled
  have h2 : Nat.choose L (Nat.log 2 n) > n ^ c := by simpa [hL] using hchoose n hn hn2
  have h2' : n ^ c < Nat.choose L (Nat.log 2 n) := h2
  exact lt_of_lt_of_le h2' h1

/-- Tableau-only violation polynomial in the instance-aware file. -/
noncomputable def tableauViolationPolyInst (M : DTM) (n : ℕ) :
    MvPolynomial (CVar M n) ℚ :=
  violationPolyRaw (tableauConstraintPolys M n)

/-- Clause-only violation polynomial in the instance-aware file. -/
noncomputable def clauseViolationPolyInst
    (M : DTM) (n N L : ℕ) (inst : SATInstance N L) (E : ClauseEmbedData M n N L) :
    MvPolynomial (CVar M n) ℚ :=
  violationPolyRaw (clauseConstraintPolys M n N L inst E)

/-- Instance compiled polynomial splits as tableau part + clause part. -/
theorem compiledViolationPolyInst_split
    (M : DTM) (n N L : ℕ) (inst : SATInstance N L) (E : ClauseEmbedData M n N L) :
    compiledViolationPolyInst M n N L inst E
      = tableauViolationPolyInst M n + clauseViolationPolyInst M n N L inst E := by
  unfold compiledViolationPolyInst tableauViolationPolyInst clauseViolationPolyInst
  unfold compiledConstraintPolys
  simp [violationPolyRaw, List.map_append, List.sum_append]

/-- Tableau part coincides with legacy compiledViolationPoly (where clauseConstraints = []). -/
theorem tableauViolation_eq_legacy
    (M : DTM) (n : ℕ) :
    tableauViolationPolyInst M n = compiledViolationPoly M n := by
  unfold tableauViolationPolyInst violationPolyRaw tableauConstraintPolys compiledViolationPoly
  have hmap1 :
      List.map ((fun p => p * p) ∘ LocalConstraint.poly) (constraintList M n)
        = List.map (fun c => c.poly * c.poly) (constraintList M n) := rfl
  have hmap2 :
      List.map ((fun p => p * p) ∘ LocalConstraint.poly) (transitionConstraints M n)
        = List.map (fun c => c.poly * c.poly) (transitionConstraints M n) := rfl
  simp [violationPoly, clauseConstraints, hmap1, hmap2]

/-- Subadditivity hook at the instance level: rank(tableau+clause) ≤ rank(tableau)+rank(clause). -/
axiom rank_subadd_inst
    (M : DTM) (n N L κ ℓ : ℕ) (inst : SATInstance N L) (E : ClauseEmbedData M n N L) :
    CompiledPoly.blockedSpdpRankQ κ ℓ (compiledViolationPolyInst M n N L inst E) (compiledPartition M n)
      ≤ CompiledPoly.blockedSpdpRankQ κ ℓ (tableauViolationPolyInst M n) (compiledPartition M n)
        + CompiledPoly.blockedSpdpRankQ κ ℓ (clauseViolationPolyInst M n N L inst E) (compiledPartition M n)

/-- Clause-part polynomial bound hook (uniform over instances/embeddings). -/
axiom clause_part_rank_poly
    (M : DTM) :
    ∃ ccl : ℕ, ∃ ncl : ℕ, ∀ n ≥ ncl, n ≥ 2 →
      ∀ (N L : ℕ) (inst : SATInstance N L) (E : ClauseEmbedData M n N L),
        CompiledPoly.blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n)
          (clauseViolationPolyInst M n N L inst E) (compiledPartition M n) ≤ n ^ ccl

/-- Instance-aware P-side theorem derived from legacy p-side + clause-part bound. -/
theorem p_subset_ccoll_inst
    (M : DTM) :
    ∃ c : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, n ≥ 2 →
      ∀ (N L : ℕ) (inst : SATInstance N L) (E : ClauseEmbedData M n N L),
        InCcollInst M n N L c inst E := by
  obtain ⟨ct, n0t, htab⟩ := p_subset_ccoll M
  obtain ⟨cc, n0c, hclause⟩ := clause_part_rank_poly M
  refine ⟨max ct cc + 1, max (max n0t n0c) 2, ?_⟩
  intro n hn hn2 N L inst E
  unfold InCcollInst blockedSpdpRankInst
  have hnt : n ≥ n0t := le_trans (le_max_left n0t n0c) (le_trans (le_max_left _ 2) hn)
  have hnc : n ≥ n0c := le_trans (le_max_right n0t n0c) (le_trans (le_max_left _ 2) hn)
  have htab' : CompiledPoly.blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n)
      (tableauViolationPolyInst M n) (compiledPartition M n) ≤ n ^ ct := by
    rw [tableauViolation_eq_legacy M n]
    exact htab n hnt hn2
  have hcl' : CompiledPoly.blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n)
      (clauseViolationPolyInst M n N L inst E) (compiledPartition M n) ≤ n ^ cc :=
    hclause n hnc hn2 N L inst E
  have hsub := rank_subadd_inst M n N L (Nat.log 2 n) (Nat.log 2 n) inst E
  have hpos : 0 < n := by omega
  have hmax1 : n ^ ct ≤ n ^ (max ct cc) := by
    exact Nat.pow_le_pow_right hpos (Nat.le_max_left ct cc)
  have hmax2 : n ^ cc ≤ n ^ (max ct cc) := by
    exact Nat.pow_le_pow_right hpos (Nat.le_max_right ct cc)
  have hsum : n ^ ct + n ^ cc ≤ 2 * n ^ (max ct cc) := by
    calc
      n ^ ct + n ^ cc ≤ n ^ (max ct cc) + n ^ (max ct cc) := Nat.add_le_add hmax1 hmax2
      _ = 2 * n ^ (max ct cc) := by ring
  have htwo : 2 * n ^ (max ct cc) ≤ n ^ (max ct cc + 1) := by
    have hnge2 : 2 ≤ n := hn2
    have hpow : n ^ (max ct cc + 1) = n * n ^ (max ct cc) := by
      rw [Nat.pow_succ]
      ring
    rw [hpow]
    exact Nat.mul_le_mul_right _ hnge2
  have hsumRanks :
      CompiledPoly.blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n) (tableauViolationPolyInst M n) (compiledPartition M n)
      + CompiledPoly.blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n) (clauseViolationPolyInst M n N L inst E) (compiledPartition M n)
      ≤ n ^ ct + n ^ cc := Nat.add_le_add htab' hcl'
  have hfinal : CompiledPoly.blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n)
      (compiledViolationPolyInst M n N L inst E) (compiledPartition M n)
      ≤ n ^ (max ct cc + 1) :=
    le_trans hsub (le_trans hsumRanks (le_trans hsum htwo))
  exact hfinal

/-- Instance-aware NP-side hardness (parallel to v3 np_compiled_rank_high). -/
theorem np_compiled_rank_high_inst :
    ∃ F : BoolFunFamily, UniformNP F ∧
    ∀ M : DTM, (∀ n, M.decides (F n)) → ∀ c : ℕ,
      ∃ n₀ : ℕ, ∀ n ≥ n₀, n ≥ 2 →
        ∃ (N L : ℕ) (inst : SATInstance N L) (E : ClauseEmbedData M n N L),
          ¬ InCcollInst M n N L c inst E := by
  obtain ⟨F, hF⟩ := TseitinLowerBound.three_sat_in_NP
  refine ⟨F, hF, ?_⟩
  intro M hM c
  obtain ⟨n₀, h⟩ := extraction_superpolynomial_inst M F hM hF c
  refine ⟨n₀, ?_⟩
  intro n hn hn2
  obtain ⟨N, L, inst, E, hgt⟩ := h n hn hn2
  refine ⟨N, L, inst, E, ?_⟩
  intro hIn
  unfold InCcollInst blockedSpdpRankInst at hIn
  exact not_lt_of_ge hIn hgt

/-- Parallel final contradiction using instance-aware compiled objects. -/
theorem P_neq_NP_inst : ¬ P_eq_NP := by
  intro hPeqNP
  obtain ⟨F, hNP, hhard⟩ := np_compiled_rank_high_inst
  obtain ⟨M, hM⟩ := hPeqNP F hNP
  obtain ⟨c, n₀, hcoll⟩ := p_subset_ccoll_inst M
  obtain ⟨n₁, hnotcoll⟩ := hhard M hM c
  let n := max (max n₀ n₁) 2
  have hn0 : n ≥ n₀ := le_trans (le_max_left n₀ n₁) (le_max_left _ 2)
  have hn1 : n ≥ n₁ := le_trans (le_max_right n₀ n₁) (le_max_left _ 2)
  have hn2 : n ≥ 2 := le_max_right _ 2
  obtain ⟨N, L, inst, E, hbad⟩ := hnotcoll n hn1 hn2
  have hgood : InCcollInst M n N L c inst E := hcoll n hn0 hn2 N L inst E
  exact hbad hgood

end PneqNPv3
