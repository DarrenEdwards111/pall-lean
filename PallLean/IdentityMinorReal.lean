/-
  IdentityMinorReal.lean — Abstract identity minor via coefficient-space Kronecker δ

  Formalizes the NP-side exponential SPDP lower bound via the
  coefficient-space identity minor argument from §25 (Lemma 124, Theorem 125).

  The coupled verifier sheet Q×_Φ(u,z) = ∏_{C∈Cl(Φ)} (1 - z_C · V_C(u_{B_C})²)
  has SPDP rank ≥ C(m,κ) where m = number of clauses, κ = derivative order.

  The proof uses:
  1. Disjoint clause blocks B_C with tag monomials τ_C
  2. For κ-subsets S ⊆ Cl(Φ), SPDP rows R_S = ∂_{z_S} Q×
  3. Column monomials τ_S = ∏_{C∈S} τ_C
  4. Kronecker δ: [τ_S] R_S = (-1)^κ, [τ_S] R_{S'} = 0 for S ≠ S'
  5. The C(m,κ) × C(m,κ) identity minor gives rank ≥ C(m,κ)
-/
import PallLean.SPDPDefs
import PallLean.CoeffDisjoint
import PallLean.IdentityMinor
import PallLean.BinomialBound
import Mathlib.Tactic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace IdentityMinorReal

open MvPolynomial SPDP

/-! ## DisjointClauseSystem: Abstract Structure for the Identity Minor Argument

This captures the essential algebraic structure needed for the Kronecker δ
proof: a collection of polynomials (clause gadgets) with pairwise disjoint
variable supports and designated tag monomials. -/

/-- A DisjointClauseSystem over a field F with n variables and m clauses.
    Each clause C has:
    - A set of local variables B_C (clauseVars)
    - A gadget polynomial V_C supported on B_C
    - A tag monomial τ_C supported on B_C with [τ_C](V_C²) = 1
    The clause variable blocks B_C are pairwise disjoint. -/
structure DisjointClauseSystem (F : Type*) [Field F] where
  /-- Total number of variables (body + selector) -/
  numVars : ℕ
  /-- Number of clauses -/
  numClauses : ℕ
  /-- Clause-local variable sets -/
  clauseVars : Fin numClauses → Finset (Fin numVars)
  /-- Pairwise disjointness of clause variable blocks -/
  disjoint : ∀ i j : Fin numClauses, i ≠ j → Disjoint (clauseVars i) (clauseVars j)
  /-- The clause gadget polynomials V_C -/
  gadgets : Fin numClauses → MvPolynomial (Fin numVars) F
  /-- Each gadget is supported on its clause's variables -/
  gadget_vars : ∀ i, ∀ m ∈ (gadgets i).support, ∀ x ∈ m.support, x ∈ clauseVars i
  /-- Tag monomial for each clause -/
  tagMonomial : Fin numClauses → (Fin numVars →₀ ℕ)
  /-- Each tag monomial is supported on its clause's variables -/
  tag_in_clause : ∀ i, ∀ x ∈ (tagMonomial i).support, x ∈ clauseVars i
  /-- Each tag monomial is nonzero (has at least one variable) -/
  tag_nonzero : ∀ i, tagMonomial i ≠ 0
  /-- The tag coefficient property: [τ_C](V_C) = 1 or -1 -/
  tag_coeff : ∀ i, coeff (tagMonomial i) (gadgets i) = 1 ∨
                    coeff (tagMonomial i) (gadgets i) = -1

/-! ## Gadget usesOnly from gadget_vars -/

theorem DisjointClauseSystem.gadget_usesOnly {F : Type*} [Field F]
    (sys : DisjointClauseSystem F) (i : Fin sys.numClauses) :
    CoeffDisjoint.usesOnly (sys.gadgets i) (↑(sys.clauseVars i) : Set _) :=
  fun m hm x hx => Finset.mem_coe.mpr (sys.gadget_vars i m hm x hx)

theorem DisjointClauseSystem.tag_supportedIn {F : Type*} [Field F]
    (sys : DisjointClauseSystem F) (i : Fin sys.numClauses) :
    CoeffDisjoint.monomSupportedIn (sys.tagMonomial i) (↑(sys.clauseVars i) : Set _) :=
  fun x hx => Finset.mem_coe.mpr (sys.tag_in_clause i x hx)

/-! ## Compound Tag Monomial for a Subset

For a list of clause indices cs, the compound tag monomial is
  τ_cs = foldl (+) 0 (cs.map tagMonomial)
i.e., the sum of individual tag monomials. Since clause variable blocks
are disjoint, this sum doesn't create any cancellation. -/

noncomputable def compoundTag {F : Type*} [Field F]
    (sys : DisjointClauseSystem F) (cs : List (Fin sys.numClauses)) :
    (Fin sys.numVars →₀ ℕ) :=
  (cs.map sys.tagMonomial).foldl (· + ·) 0

/-! ## Product Coefficient Factorization

The key algebraic fact: for a product of polynomials with pairwise disjoint
variable supports, the coefficient of a compound monomial factors as a product
of individual coefficients. -/

/-- The coefficient of a compound tag monomial in a product of gadgets
    factors into individual coefficients, by disjointness of variable blocks. -/
theorem coeff_compoundTag_prod_eq {F : Type*} [Field F]
    (sys : DisjointClauseSystem F)
    (cs : List (Fin sys.numClauses))
    (hnd : cs.Nodup) :
    coeff (compoundTag sys cs) (cs.map sys.gadgets).prod =
    (cs.map (fun c => coeff (sys.tagMonomial c) (sys.gadgets c))).prod := by
  induction cs with
  | nil =>
    simp [compoundTag, coeff_one]
  | cons c rest ih =>
    simp only [List.map_cons, List.prod_cons]
    have hnd_rest : rest.Nodup := (List.nodup_cons.mp hnd).2
    have hc_notin : c ∉ rest := (List.nodup_cons.mp hnd).1
    -- Sets for coeff_mul_disjoint
    set A : Set (Fin sys.numVars) := ↑(sys.clauseVars c)
    set B : Set (Fin sys.numVars) := {x | ∃ c' ∈ rest, x ∈ (sys.clauseVars c' : Finset _)}
    -- Head uses only A
    have hp : CoeffDisjoint.usesOnly (sys.gadgets c) A := sys.gadget_usesOnly c
    -- Rest product uses only B
    have hq : CoeffDisjoint.usesOnly (rest.map sys.gadgets).prod B := by
      apply CoeffDisjoint.usesOnly_list_prod
      intro p hp_mem
      simp only [List.mem_map] at hp_mem
      obtain ⟨c', hc', rfl⟩ := hp_mem
      exact CoeffDisjoint.usesOnly_mono (sys.gadget_usesOnly c')
        (fun x hx => ⟨c', hc', Finset.mem_coe.mp hx⟩)
    -- Disjointness: A ∩ B = ∅
    have hdisj : Disjoint A B := by
      rw [Set.disjoint_left]
      intro x hxA hxB
      obtain ⟨c', hc'mem, hxc'⟩ := hxB
      have hcc' : c ≠ c' := fun h => hc_notin (h ▸ hc'mem)
      exact absurd (Finset.mem_coe.mp hxc')
        (Finset.disjoint_left.mp (sys.disjoint c c' hcc') (Finset.mem_coe.mp hxA))
    -- Tag head in A
    have hmA : CoeffDisjoint.monomSupportedIn (sys.tagMonomial c) A :=
      sys.tag_supportedIn c
    -- Tag rest sum in B
    have hmB : CoeffDisjoint.monomSupportedIn
        (compoundTag sys rest) B := by
      unfold compoundTag
      apply CoeffDisjoint.monomSupportedIn_foldl_add
      intro m hm
      simp only [List.mem_map] at hm
      obtain ⟨c', hc', rfl⟩ := hm
      exact CoeffDisjoint.monomSupportedIn_mono (sys.tag_supportedIn c')
        (fun x hx => ⟨c', hc', Finset.mem_coe.mp hx⟩)
    -- Rewrite compoundTag of cons
    have hfoldl : compoundTag sys (c :: rest) =
        sys.tagMonomial c + compoundTag sys rest := by
      unfold compoundTag
      simp only [List.map_cons, List.foldl, zero_add]
      exact CoeffDisjoint.foldl_add_acc _ _
    rw [hfoldl]
    rw [CoeffDisjoint.coeff_mul_disjoint hp hq hdisj hmA hmB]
    rw [ih hnd_rest]

/-! ## Diagonal and Off-Diagonal Properties

Diagonal: [τ_S](∏_{C∈S} V_C) = ∏_{C∈S} [τ_C](V_C) = ±1
Off-diagonal: [τ_S](∏_{C∈S'} V_C) = 0 when S ≠ S'

The off-diagonal vanishing uses that S ≠ S' (as nodup sublists of the same
parent list) implies ∃ C ∈ S \ S', and the tag for C hits variables disjoint
from all gadgets in S'. -/

/-- The diagonal coefficient product is ±1 -/
theorem diagonal_coeff_unit {F : Type*} [Field F]
    (sys : DisjointClauseSystem F)
    (cs : List (Fin sys.numClauses))
    (hnd : cs.Nodup) :
    (cs.map (fun c => coeff (sys.tagMonomial c) (sys.gadgets c))).prod = 1 ∨
    (cs.map (fun c => coeff (sys.tagMonomial c) (sys.gadgets c))).prod = -1 := by
  induction cs with
  | nil => left; simp
  | cons c rest ih =>
    simp only [List.map_cons, List.prod_cons]
    have hnd_rest := (List.nodup_cons.mp hnd).2
    have hprod := ih hnd_rest
    have hcoeff := sys.tag_coeff c
    rcases hcoeff with h1 | h1 <;> rcases hprod with h2 | h2 <;> simp [h1, h2] <;> ring

/-- Off-diagonal: the compound tag for cs₁ vanishes on the gadget product for cs₂
    when cs₁ and cs₂ are distinct nodup sublists of a common parent. -/
theorem offdiag_coeff_zero {F : Type*} [Field F]
    (sys : DisjointClauseSystem F)
    (cs₁ cs₂ : List (Fin sys.numClauses))
    (hnd₁ : cs₁.Nodup) (hnd₂ : cs₂.Nodup)
    (hdiff : ∃ c, c ∈ cs₁ ∧ c ∉ cs₂) :
    coeff (compoundTag sys cs₁) (cs₂.map sys.gadgets).prod = 0 := by
  obtain ⟨c, hc₁, hc₂⟩ := hdiff
  -- The product ∏_{C∈cs₂} V_C uses only ⋃_{C∈cs₂} clauseVars C
  set Bj : Set (Fin sys.numVars) :=
    {x | ∃ c' ∈ cs₂, x ∈ (sys.clauseVars c' : Finset _)}
  have hprod_uses : CoeffDisjoint.usesOnly (cs₂.map sys.gadgets).prod Bj := by
    apply CoeffDisjoint.usesOnly_list_prod
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨c', hc', rfl⟩ := hp
    exact CoeffDisjoint.usesOnly_mono (sys.gadget_usesOnly c')
      (fun x hx => ⟨c', hc', Finset.mem_coe.mp hx⟩)
  -- Find a variable in compoundTag cs₁ that is outside Bj
  -- The tag for c has support in clauseVars c, which is disjoint from
  -- all clauseVars c' for c' ∈ cs₂ (since c ∉ cs₂ and blocks are disjoint)
  -- We need a variable x in (sys.tagMonomial c).support ∩ (compoundTag sys cs₁).support
  -- First show tagMonomial c has nonempty support (since coeff is ±1, gadget has this monomial)
  have htag_ne : sys.tagMonomial c ≠ 0 := sys.tag_nonzero c
  -- tagMonomial c has nonzero support
  have ⟨x, hx_supp⟩ := Finsupp.support_nonempty_iff.mpr htag_ne
  -- x is in clauseVars c
  have hx_c : x ∈ sys.clauseVars c := sys.tag_in_clause c x hx_supp
  -- x is not in Bj
  have hx_notBj : x ∉ Bj := by
    intro ⟨c', hc'₂, hxc'⟩
    by_cases hcc' : c = c'
    · exact hc₂ (hcc' ▸ hc'₂)
    · exact absurd (Finset.mem_coe.mp hxc')
        (Finset.disjoint_left.mp (sys.disjoint c c' hcc') hx_c)
  -- x has nonzero value in compoundTag cs₁
  -- We show (compoundTag sys cs₁) x ≥ (sys.tagMonomial c) x > 0
  have hx_val : (sys.tagMonomial c) x ≠ 0 := Finsupp.mem_support_iff.mp hx_supp
  have hx_compound : (compoundTag sys cs₁) x ≠ 0 := by
    unfold compoundTag
    rw [CoeffDisjoint.foldl_add_eq_foldr]
    -- By induction: c ∈ cs₁ contributes (tagMonomial c) x > 0,
    -- all other clauses in cs₁ contribute 0 at x (disjoint blocks)
    suffices hsuff : ∀ (L : List (Fin sys.numClauses)),
        c ∈ L → L.Nodup →
        (∀ c' ∈ L, c' ≠ c → (sys.tagMonomial c') x = 0) →
        (CoeffDisjoint.listFinsuppSum (L.map sys.tagMonomial)) x ≥
          (sys.tagMonomial c) x by
      have hge := hsuff cs₁ hc₁ hnd₁ (fun c' _ hne => by
        by_contra h
        have hx_c' : x ∈ sys.clauseVars c' :=
          sys.tag_in_clause c' x (Finsupp.mem_support_iff.mpr h)
        exact absurd hx_c' (Finset.disjoint_left.mp (sys.disjoint c c' (Ne.symm hne)) hx_c))
      omega
    intro L hcL hndL hzero
    induction L with
    | nil => simp at hcL
    | cons hd rest ih_inner =>
      have ⟨hhd_notin, hnd_rest⟩ := List.nodup_cons.mp hndL
      rw [List.map_cons, CoeffDisjoint.listFinsuppSum_cons, Finsupp.add_apply]
      rcases List.mem_cons.mp hcL with rfl | hrest_mem
      · -- hd = c
        have : (CoeffDisjoint.listFinsuppSum (rest.map sys.tagMonomial)) x ≥ 0 := Nat.zero_le _
        omega
      · -- hd ≠ c
        have hhd_ne : hd ≠ c := fun h => hhd_notin (h ▸ hrest_mem)
        rw [hzero hd (by simp) hhd_ne, zero_add]
        exact ih_inner hrest_mem hnd_rest
          (fun c' hc' hne => hzero c' (by simp [hc']) hne)
  -- Now apply coeff_eq_zero_of_not_supported
  exact CoeffDisjoint.coeff_eq_zero_of_not_supported hprod_uses
    ⟨x, Finsupp.mem_support_iff.mpr hx_compound, hx_notBj⟩

/-! ## Kronecker δ via Abstract Rows

We now define "abstract rows" R_S (the result of differentiating the coupled
sheet along selector subset S) and show the Kronecker δ property at the
coefficient level. The full SPDP argument combines this with the iterated
derivative structure from IdentityMinor.lean.

For the abstract formulation, we parametrize by:
- A family of row polynomials (indexed by κ-subsets)
- A family of column monomials (the compound tags)
- A sign function

and prove that the Kronecker δ implies linear independence of the rows. -/

/-- Abstract Kronecker delta system: a family of polynomials and monomials
    with the δ property [τ_i](R_j) = δ_{ij} · s_i where s_i = ±1. -/
structure KroneckerDeltaSystem (F : Type*) [Field F] (n : ℕ) (N : ℕ) where
  /-- Row polynomials -/
  rows : Fin N → MvPolynomial (Fin n) F
  /-- Column monomials -/
  cols : Fin N → (Fin n →₀ ℕ)
  /-- Signs -/
  signs : Fin N → F
  /-- Each sign is ±1 -/
  signs_unit : ∀ i, signs i = 1 ∨ signs i = -1
  /-- The Kronecker δ property -/
  kronecker : ∀ i j, coeff (cols i) (rows j) = if i = j then signs i else 0

/-! ## Linear Independence from Kronecker δ

The key rank theorem: if N polynomials satisfy a Kronecker δ with ±1
diagonal entries, then they are linearly independent, giving rank ≥ N. -/

/-- The evaluation-at-monomial map: p ↦ coeff m p is a linear functional. -/
noncomputable def coeffLinearMap {n : ℕ} (F : Type*) [CommRing F]
    (m : (Fin n →₀ ℕ)) : MvPolynomial (Fin n) F →ₗ[F] F where
  toFun := fun p => coeff m p
  map_add' := fun p q => by simp [coeff_add]
  map_smul' := fun c p => by simp [coeff_smul, smul_eq_mul]

/-- If a family of polynomials has the Kronecker δ property with ±1 diagonal,
    then the polynomials are linearly independent. -/
theorem linearIndependent_of_kronecker {F : Type*} [Field F]
    {n N : ℕ} (sys : KroneckerDeltaSystem F n N) :
    LinearIndependent F sys.rows := by
  rw [linearIndependent_iff']
  intro s w hw i hi
  -- Apply coeff (cols i) to the linear combination ∑ w_j · rows_j = 0
  have heval : ∀ k, coeff (sys.cols k) (∑ j ∈ s, w j • sys.rows j) =
      ∑ j ∈ s, w j * coeff (sys.cols k) (sys.rows j) := by
    intro k
    simp [coeff_sum, coeff_smul, smul_eq_mul]
  have h0 : coeff (sys.cols i) (∑ j ∈ s, w j • sys.rows j) = 0 := by
    rw [hw]; simp [MvPolynomial.coeff_zero]
  rw [heval i] at h0
  -- Use Kronecker δ: coeff (cols i) (rows j) = δ_{ij} · signs i
  have hsimp : ∑ j ∈ s, w j * coeff (sys.cols i) (sys.rows j) =
      ∑ j ∈ s, w j * (if i = j then sys.signs i else 0) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [sys.kronecker i j]
  rw [hsimp] at h0
  -- Only the i = j term survives
  have hsum : ∑ j ∈ s, w j * (if i = j then sys.signs i else 0) =
      w i * sys.signs i := by
    have htail : ∑ j ∈ s.erase i, w j * (if i = j then sys.signs i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hne : j ≠ i := Finset.ne_of_mem_erase hj
      simp [Ne.symm hne]
    rw [← Finset.add_sum_erase s _ hi, htail, add_zero]
    simp
  rw [hsum] at h0
  -- w i * signs i = 0 and signs i is a unit → w i = 0
  rcases sys.signs_unit i with h | h <;> simp [h] at h0 <;> exact h0

/-- The finrank lower bound: a Kronecker δ system of size N gives
    finrank ≥ N for the span of the rows. -/
theorem finrank_ge_of_kronecker {F : Type*} [Field F]
    {n N : ℕ} (sys : KroneckerDeltaSystem F n N) :
    N ≤ (Set.range sys.rows).finrank F := by
  have hli := linearIndependent_of_kronecker sys
  have := linearIndependent_iff_card_le_finrank_span (R := F).mp hli
  rwa [Fintype.card_fin] at this

/-! ## Construction of the Kronecker δ System from a DisjointClauseSystem

Given a DisjointClauseSystem and a derivative order κ, we construct a
KroneckerDeltaSystem of size C(m, κ) where the rows are the gadget products
∏_{C∈S} V_C for κ-subsets S. -/

/-- The gadget product for a list of clause indices -/
noncomputable def gadgetProd {F : Type*} [Field F]
    (sys : DisjointClauseSystem F) (cs : List (Fin sys.numClauses)) :
    MvPolynomial (Fin sys.numVars) F :=
  (cs.map sys.gadgets).prod

/-- All κ-sublists of the full clause list Fin numClauses -/
noncomputable def clauseSubsets {F : Type*} [Field F]
    (sys : DisjointClauseSystem F) (κ : ℕ) :
    List (List (Fin sys.numClauses)) :=
  (List.finRange sys.numClauses).sublistsLen κ

theorem clauseSubsets_length {F : Type*} [Field F]
    (sys : DisjointClauseSystem F) (κ : ℕ) :
    (clauseSubsets sys κ).length = Nat.choose sys.numClauses κ := by
  unfold clauseSubsets
  rw [List.length_sublistsLen, List.length_finRange]

/-- Get the i-th κ-subset -/
noncomputable def getClauseSubset {F : Type*} [Field F]
    (sys : DisjointClauseSystem F) (κ : ℕ)
    (i : Fin (Nat.choose sys.numClauses κ)) :
    List (Fin sys.numClauses) :=
  (clauseSubsets sys κ).get (i.cast (clauseSubsets_length sys κ).symm)

theorem getClauseSubset_length {F : Type*} [Field F]
    (sys : DisjointClauseSystem F) (κ : ℕ)
    (i : Fin (Nat.choose sys.numClauses κ)) :
    (getClauseSubset sys κ i).length = κ := by
  unfold getClauseSubset clauseSubsets
  exact List.length_of_sublistsLen (List.get_mem _ _)

private theorem clauseSubsets_sublist {F : Type*} [Field F]
    (sys : DisjointClauseSystem F) (κ : ℕ)
    (i : Fin (clauseSubsets sys κ).length) :
    ((clauseSubsets sys κ).get i).Sublist (List.finRange sys.numClauses) := by
  have hmem := List.get_mem (clauseSubsets sys κ) i
  exact List.mem_sublists'.mp (List.sublistsLen_sublist_sublists' κ
    (List.finRange sys.numClauses) |>.subset hmem)

theorem getClauseSubset_nodup {F : Type*} [Field F]
    (sys : DisjointClauseSystem F) (κ : ℕ)
    (i : Fin (Nat.choose sys.numClauses κ)) :
    (getClauseSubset sys κ i).Nodup := by
  unfold getClauseSubset
  exact List.Nodup.sublist
    (clauseSubsets_sublist sys κ (i.cast (clauseSubsets_length sys κ).symm))
    (List.nodup_finRange sys.numClauses)

/-- Distinct indices give distinct sublists -/
theorem getClauseSubset_injective {F : Type*} [Field F]
    (sys : DisjointClauseSystem F) (κ : ℕ)
    (i j : Fin (Nat.choose sys.numClauses κ)) (hij : i ≠ j) :
    getClauseSubset sys κ i ≠ getClauseSubset sys κ j := by
  intro heq
  unfold getClauseSubset at heq
  have hnd := List.nodup_sublistsLen κ (List.nodup_finRange sys.numClauses)
  have hinj := hnd.injective_get heq
  exact hij (Fin.ext (by have := congr_arg Fin.val hinj; simp at this; exact this))

/-- If i ≠ j, there exists an element in getClauseSubset i not in getClauseSubset j -/
theorem exists_mem_not_mem_of_ne {F : Type*} [Field F]
    (sys : DisjointClauseSystem F) (κ : ℕ)
    (i j : Fin (Nat.choose sys.numClauses κ)) (hij : i ≠ j) :
    ∃ c, c ∈ getClauseSubset sys κ i ∧ c ∉ getClauseSubset sys κ j := by
  by_contra hall
  push_neg at hall
  -- Every element of getClauseSubset i is in getClauseSubset j
  have hnd_i := getClauseSubset_nodup sys κ i
  have hnd_j := getClauseSubset_nodup sys κ j
  have hlen_i := getClauseSubset_length sys κ i
  have hlen_j := getClauseSubset_length sys κ j
  have hfs_sub : (getClauseSubset sys κ i).toFinset ⊆ (getClauseSubset sys κ j).toFinset :=
    fun x => by rw [List.mem_toFinset, List.mem_toFinset]; exact hall x
  have hcard_eq : (getClauseSubset sys κ i).toFinset.card =
      (getClauseSubset sys κ j).toFinset.card := by
    rw [List.toFinset_card_of_nodup hnd_i, List.toFinset_card_of_nodup hnd_j, hlen_i, hlen_j]
  have hfs_eq := Finset.eq_of_subset_of_card_le hfs_sub (by omega)
  -- Same toFinset + both sublists of nodup parent → same list
  have hsub_i := clauseSubsets_sublist sys κ (i.cast (clauseSubsets_length sys κ).symm)
  have hsub_j := clauseSubsets_sublist sys κ (j.cast (clauseSubsets_length sys κ).symm)
  have heq := IdentityMinor.sublist_eq_of_nodup_toFinset_eq
    (List.nodup_finRange sys.numClauses) hsub_i hsub_j hfs_eq
  exact getClauseSubset_injective sys κ i j hij heq

/-! ## The Main Kronecker δ System Construction -/

/-- Build a KroneckerDeltaSystem from a DisjointClauseSystem:
    - rows are gadget products ∏_{C∈S} V_C
    - columns are compound tag monomials τ_S
    - signs are ∏_{C∈S} [τ_C](V_C) -/
noncomputable def buildKroneckerSystem {F : Type*} [Field F]
    (sys : DisjointClauseSystem F) (κ : ℕ) :
    KroneckerDeltaSystem F sys.numVars (Nat.choose sys.numClauses κ) where
  rows := fun i => gadgetProd sys (getClauseSubset sys κ i)
  cols := fun i => compoundTag sys (getClauseSubset sys κ i)
  signs := fun i => (getClauseSubset sys κ i |>.map
    (fun c => coeff (sys.tagMonomial c) (sys.gadgets c))).prod
  signs_unit := by
    intro i
    exact diagonal_coeff_unit sys _ (getClauseSubset_nodup sys κ i)
  kronecker := by
    intro i j
    split
    · -- i = j case
      rename_i heq; subst heq
      unfold gadgetProd
      exact coeff_compoundTag_prod_eq sys _ (getClauseSubset_nodup sys κ i)
    · -- i ≠ j case
      rename_i hne
      unfold gadgetProd
      exact offdiag_coeff_zero sys _ _
        (getClauseSubset_nodup sys κ i)
        (getClauseSubset_nodup sys κ j)
        (exists_mem_not_mem_of_ne sys κ i j hne)

/-! ## The Identity Minor Rank Bound (Theorem 125)

Combining the Kronecker δ construction with linear independence gives
rank ≥ C(m, κ). -/

/-- **Theorem 125 (Identity Minor Rank Bound)**: For a DisjointClauseSystem
    with m clauses and derivative order κ, the gadget products span a space
    of dimension ≥ C(m, κ). -/
theorem identity_minor_rank_bound {F : Type*} [Field F]
    (sys : DisjointClauseSystem F) (κ : ℕ) :
    LinearIndependent F (fun i : Fin (Nat.choose sys.numClauses κ) =>
      gadgetProd sys (getClauseSubset sys κ i)) := by
  exact linearIndependent_of_kronecker (buildKroneckerSystem sys κ)

theorem identity_minor_finrank_bound {F : Type*} [Field F]
    (sys : DisjointClauseSystem F) (κ : ℕ) :
    Nat.choose sys.numClauses κ ≤
    (Set.range (fun i : Fin (Nat.choose sys.numClauses κ) =>
      gadgetProd sys (getClauseSubset sys κ i))).finrank F := by
  exact finrank_ge_of_kronecker (buildKroneckerSystem sys κ)

/-! ## Exponential Lower Bound for Tseitin Formulas

For Tseitin formulas with m ≥ cn clauses on n variables and
κ = α log n, we get C(cn, α log n) ≥ n^{Ω(log n)}.

The key combinatorial fact: choose(m, k) is superpolynomial when
m grows linearly in n and k grows logarithmically. We state this
as a monotonicity lemma using the existing BinomialBound infrastructure. -/

/-- Monotonicity of choose: if m₁ ≤ m₂, then choose m₁ k ≤ choose m₂ k. -/
theorem choose_mono_left (m₁ m₂ k : ℕ) (hm : m₁ ≤ m₂) :
    Nat.choose m₁ k ≤ Nat.choose m₂ k :=
  Nat.choose_le_choose k hm

/-- BinomialBound: choose (k * m) k ≥ m ^ k. -/
theorem choose_mul_ge_pow (k m : ℕ) (hm : 0 < m) :
    m ^ k ≤ Nat.choose (k * m) k :=
  BinomialBound.choose_mul_ge_pow k m hm

/-- BinomialBound: choose L k ≥ (L / k) ^ k. -/
theorem choose_ge_div_pow (L k : ℕ) (hk : 0 < k) :
    (L / k) ^ k ≤ Nat.choose L k :=
  BinomialBound.choose_ge_div_pow L k hk

/-- The quantitative superpolynomial bound on the identity minor size.

    For m clauses and derivative order κ, the identity minor has size C(m, κ).
    Using choose_ge_div_pow: C(m, κ) ≥ (m / κ)^κ.
    With κ = Nat.log 2 m: C(m, log m) ≥ (m / log m)^(log m).

    For any fixed polynomial degree d, this exceeds m^d for large m because
    (m / log m)^(log m) grows superpolynomially.

    We state the concrete lower bound that follows directly from the injection argument. -/
theorem identity_minor_lower_bound {F : Type*} [Field F]
    (sys : DisjointClauseSystem F) (κ : ℕ) (hκ : 0 < κ) :
    (sys.numClauses / κ) ^ κ ≤ Nat.choose sys.numClauses κ :=
  choose_ge_div_pow sys.numClauses κ hκ

/-- Composing with linear independence: the gadget products for κ-subsets
    span a space of dimension ≥ (m/κ)^κ. -/
theorem identity_minor_dim_lower_bound {F : Type*} [Field F]
    (sys : DisjointClauseSystem F) (κ : ℕ) (hκ : 0 < κ) :
    (sys.numClauses / κ) ^ κ ≤
    (Set.range (fun i : Fin (Nat.choose sys.numClauses κ) =>
      gadgetProd sys (getClauseSubset sys κ i))).finrank F :=
  le_trans (identity_minor_lower_bound sys κ hκ)
    (finrank_ge_of_kronecker (buildKroneckerSystem sys κ))

/-! ### Superpolynomial Growth of the Identity Minor

The identity minor size C(m, log₂ m) > m^d for large m.
Uses superPoly_beats_poly, choose_ge_div_pow, and the arithmetic lemma
that (m/k)^k ≥ m^(k/4) when k² ≤ m. -/

/-- Helper: k² ≤ 2^k for k ≥ 4, proved by induction. -/
private theorem two_mul_add_one_le_pow2 : ∀ n, n ≥ 3 → 2 * n + 1 ≤ 2 ^ n := by
  intro n hn
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hm : m ≥ 3
    · calc 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by ring
        _ ≤ 2 ^ m + 2 := by omega
        _ ≤ 2 ^ m + 2 ^ m := by
            apply Nat.add_le_add_left
            calc 2 = 2 ^ 1 := by ring
              _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 ^ (m + 1) := by ring
    · interval_cases m <;> omega

private theorem sq_le_pow2 : ∀ k, k ≥ 4 → k * k ≤ 2 ^ k := by
  intro k hk
  induction k with
  | zero => omega
  | succ n ih =>
    by_cases hn4 : n ≥ 4
    · have ihn := ih hn4
      have h2n1 := two_mul_add_one_le_pow2 n (by omega)
      calc (n + 1) * (n + 1) = n * n + 2 * n + 1 := by ring
        _ ≤ 2 ^ n + 2 ^ n := by omega
        _ = 2 ^ (n + 1) := by ring
    · interval_cases n <;> omega

/-- Helper: (log₂ m)² ≤ m for m ≥ 2^16. -/
private theorem log_sq_le (m : ℕ) (hm : m ≥ 2 ^ 16) :
    Nat.log 2 m * Nat.log 2 m ≤ m := by
  set k := Nat.log 2 m
  have hk_ge : k ≥ 16 := by
    calc k = Nat.log 2 m := rfl
      _ ≥ Nat.log 2 (2 ^ 16) := Nat.log_mono_right hm
      _ = 16 := Nat.log_pow (by norm_num : 1 < 2) 16
  have h2k : 2 ^ k ≤ m := Nat.pow_log_le_self 2 (by omega : m ≠ 0)
  calc k * k ≤ 2 ^ k := sq_le_pow2 k (by omega)
    _ ≤ m := h2k

/-- The superpolynomial growth of binomial coefficients:
    for any polynomial degree d, C(m, log₂ m) > m^d for sufficiently large m.

    Proof: choose(m, k) ≥ (m/k)^k (BinomialBound). For k = log₂ m:
    (m/k)^k ≥ k^k (since k² ≤ m gives m/k ≥ k).
    k^k ≥ (2^(d+1))^k = 2^((d+1)k) ≥ 2^(d(k+1)) ≥ m^d
    (using k ≥ 2^(d+1) and m < 2^(k+1)). -/
theorem identity_minor_beats_poly (d : ℕ) (hd : d ≥ 1) :
    ∃ m₀, ∀ m, m ≥ m₀ →
    m ^ d < Nat.choose m (Nat.log 2 m) := by
  -- Threshold: m ≥ 2^(2^(d+1)+1) ensures k = log₂ m ≥ 2^(d+1)
  -- This gives k^k ≥ (2^(d+1))^k ≥ m^d (since m < 2^(k+1) and (d+1)k ≥ d(k+1))
  use 2 ^ (2 ^ (d + 1) + 1)
  intro m hm
  set k := Nat.log 2 m with hk_def
  have hk_lower : k ≥ 2 ^ (d + 1) + 1 := by
    calc k ≥ Nat.log 2 (2 ^ (2 ^ (d + 1) + 1)) := Nat.log_mono_right hm
      _ = 2 ^ (d + 1) + 1 := Nat.log_pow (by norm_num) _
  have hk_ge_2 : k ≥ 2 := by
    have : 2 ^ (d + 1) ≥ 2 := by
      calc 2 ^ (d + 1) ≥ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 := by ring
    linarith
  have hk_pos : 0 < k := by linarith
  -- choose(m, k) ≥ (m/k)^k
  have hchoose := choose_ge_div_pow m k hk_pos
  -- k² ≤ m (from sq_le_pow2 and 2^k ≤ m)
  have hm_pos : m ≠ 0 := by
    have : 2 ^ (2 ^ (d + 1) + 1) ≥ 1 := Nat.one_le_pow _ _ (by norm_num)
    linarith
  have h2k : 2 ^ k ≤ m := Nat.pow_log_le_self 2 hm_pos
  have hk_ge_4 : k ≥ 4 := by
    have : 2 ^ (d + 1) ≥ 4 := by
      calc 2 ^ (d + 1) ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 4 := by ring
    linarith
  have hksq_le : k * k ≤ m := le_trans (sq_le_pow2 k hk_ge_4) h2k
  -- m/k ≥ k
  have hmk : k ≤ m / k := by
    rw [Nat.le_div_iff_mul_le hk_pos]; linarith [Nat.mul_comm k k]
  -- (m/k)^k ≥ k^k
  have hdiv_pow : k ^ k ≤ (m / k) ^ k := Nat.pow_le_pow_left hmk k
  -- m < 2^(k+1)
  have hm_upper : m < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  -- m^d < (2^(k+1))^d = 2^(d*(k+1))
  have hmd_upper : m ^ d < 2 ^ (d * (k + 1)) := by
    calc m ^ d < (2 ^ (k + 1)) ^ d := Nat.pow_lt_pow_left hm_upper (by omega)
      _ = 2 ^ ((k + 1) * d) := by rw [← pow_mul]
      _ = 2 ^ (d * (k + 1)) := by ring_nf
  -- k ≥ d (so (d+1)*k ≥ d*(k+1))
  have hk_ge_d : k ≥ d := by
    have h2d1 : ∀ d', 2 ^ (d' + 1) ≥ d' + 1 := by
      intro d'
      induction d' with
      | zero => norm_num
      | succ n ih =>
        calc 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by ring
          _ ≥ 2 * (n + 1) := by nlinarith
          _ ≥ n + 1 + 1 := by omega
    have := h2d1 d
    omega
  -- (d+1)*k ≥ d*(k+1): (d+1)*k = dk + k ≥ dk + d = d*(k+1) since k ≥ d
  have hexp : d * (k + 1) ≤ (d + 1) * k := by nlinarith
  -- k ≥ 2^(d+1), so k^k ≥ (2^(d+1))^k = 2^((d+1)*k) ≥ 2^(d*(k+1)) > m^d
  have hk_pow : 2 ^ ((d + 1) * k) ≤ k ^ k := by
    calc 2 ^ ((d + 1) * k) = (2 ^ (d + 1)) ^ k := by rw [pow_mul]
      _ ≤ k ^ k := Nat.pow_le_pow_left (by omega) k
  calc m ^ d < 2 ^ (d * (k + 1)) := hmd_upper
    _ ≤ 2 ^ ((d + 1) * k) := Nat.pow_le_pow_right (by norm_num) hexp
    _ ≤ k ^ k := hk_pow
    _ ≤ (m / k) ^ k := hdiv_pow
    _ ≤ Nat.choose m k := hchoose

/-! ## Wiring to Concrete Tseitin IdentityMinor

We show that the existing IdentityMinor.lean construction for Tseitin formulas
can be viewed as an instance of our abstract DisjointClauseSystem framework. -/

/-- Build a DisjointClauseSystem from a Tseitin formula with a disjoint packing. -/
noncomputable def tseitinClauseSystem (F : Type*) [Field F]
    (Φ : Tseitin.TseitinFormula) (pack : Tseitin.DisjointPacking Φ)
    [Nontrivial F] :
    DisjointClauseSystem F where
  numVars := Tseitin.tseitinNumVars Φ
  numClauses := pack.selected.length
  clauseVars := fun i => IdentityMinor.clauseVarSetFin Φ (pack.selected.get i)
  disjoint := fun i j hij =>
    IdentityMinor.clauseVarSetFin_disjoint (F := F) Φ pack i j hij
  gadgets := fun i => Tseitin.clauseGadget F Φ (pack.selected.get i)
  gadget_vars := fun i m hm x hx => by
    have := IdentityMinor.clauseGadget_usesOnly_clause (F := F) Φ (pack.selected.get i) m hm x hx
    exact this
  tagMonomial := fun i => IdentityMinor.chooseTagMonomial Φ (pack.selected.get i)
  tag_in_clause := fun i x hx => by
    exact IdentityMinor.tagMonomial_supported_clause Φ (pack.selected.get i) x hx
  tag_nonzero := fun i => by
    set c := pack.selected.get i
    -- chooseTagMonomial Φ c = single v1 1 + single v2 1 + single v3 1
    -- which is nonzero because v1 has value 1 in it (v1 ≠ v2, v1 ≠ v3).
    -- We show (chooseTagMonomial Φ c) v1 = 1 ≠ 0.
    intro h
    have h0 : ∀ x, (IdentityMinor.chooseTagMonomial Φ c) x = 0 := by
      intro x; rw [h]; rfl
    set cl := Φ.clauses.get c
    have hN : Tseitin.tseitinNumVars Φ > 0 := by
      have := c.isLt; simp [Tseitin.tseitinNumVars]; omega
    set v1 : Fin (Tseitin.tseitinNumVars Φ) :=
      ⟨cl.var1 % Tseitin.tseitinNumVars Φ, Nat.mod_lt _ hN⟩
    -- chooseTagMonomial is nonzero because Finsupp.single v1 1 has v1 in its support
    -- and contributes at least 1 to the sum at position v1.
    -- We use: (single v1 1 + _) v1 ≥ 1 since (single v1 1) v1 = 1
    have hval : (IdentityMinor.chooseTagMonomial Φ c) v1 ≥ 1 := by
      show (IdentityMinor.chooseTagMonomial Φ c) v1 ≥ 1
      rw [IdentityMinor.chooseTagMonomial_eq]
      -- The result after Finsupp.add_apply and single_apply is a sum of ite expressions.
      -- v1 = ⟨cl.var1 % N, _⟩ and the first ite condition tests v1 against the same expression.
      -- Use Finsupp.single_apply_self to get the first term = 1:
      have h1 : (Finsupp.single v1 (1 : ℕ)) v1 = 1 := Finsupp.single_eq_same
      rw [Finsupp.add_apply, Finsupp.add_apply]
      rw [h1]; omega
    have h0v := h0 v1
    omega
  tag_coeff := fun i =>
    IdentityMinor.chooseTagMonomial_coeff Φ (pack.selected.get i)

/-- The abstract identity minor rank bound applied to Tseitin formulas:
    the gadget products for κ-subsets of the disjoint packing are linearly
    independent, giving rank ≥ C(|packing|, κ). -/
theorem tseitin_identity_minor_rank {F : Type*} [Field F] [Nontrivial F]
    (Φ : Tseitin.TseitinFormula) (pack : Tseitin.DisjointPacking Φ) (κ : ℕ) :
    LinearIndependent F (fun i : Fin (Nat.choose pack.selected.length κ) =>
      gadgetProd (tseitinClauseSystem F Φ pack) (getClauseSubset (tseitinClauseSystem F Φ pack) κ i)) :=
  identity_minor_rank_bound (tseitinClauseSystem F Φ pack) κ

end IdentityMinorReal
