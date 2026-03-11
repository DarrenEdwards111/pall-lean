/-
Copyright (c) 2026 Darren Edwards. All rights reserved.
Released under Apache 2.0 license.
-/
import PallLean.MultilinearSPDP

/-!
# Profile Compression for Tseitin SPDP Rank (§9)

Goal: prove `tseitin_spdp_rank_bound`:
  mlBlockedSpdpRank (tseitinPartition n) κ κ (tseitinPoly ℚ n) ≤ n^10
for AdmissibleSpdpParams n κ (i.e., κ ≥ 5, κ ≤ log₂ n).

## Proof Architecture (7 Lemmas)

### Layer 1 — Structure (already proved in IdentityMinor.lean)
- `coupledVerifier_eq_prod`: tseitinPoly = ∏ cvFactor
- `pderiv_cvFactor_eq`: ∂_{z_c}(cvFactor c) = -clauseGadget c
- `pderiv_cvFactor_ne`: ∂_{z_c}(cvFactor d) = 0 for c ≠ d
- `iterDeriv_cvProd_eq`: multi-selector derivative factorization

### Layer 2 — Canonical Windows
Block-admissible derivative lists for tseitinPartition are (essentially)
lists of distinct selector variables. Every SPDP generator reduces to
a canonical selector window form.

### Layer 3 — Live Interfaces
After hitting κ selectors, the derivative depends only on a bounded
neighborhood of the hit clauses. The number of "live interfaces" is
O(κ) = O(log n).

### Layer 4 — Profile Histograms
Windows are classified by their interface-type histogram. The number
of realizable profiles is polynomial in n.

### Layer 5 — Within-Profile Dimension
Rows sharing a profile lie in a bounded-dimensional subspace.

### Layer 6 — Assembly
Sum dimensions over profiles to get the polynomial rank bound.
-/

namespace SPDP

open MvPolynomial Finset IdentityMinor Tseitin MultilinearSPDP NPWitness

-- ============================================================
-- §1. Abbreviations and key structural facts
-- ============================================================

/-- Short name for the Tseitin formula at parameter n -/
noncomputable abbrev Φn (n : ℕ) := tseitinAt n

/-- Number of clauses in the n-th Tseitin formula -/
noncomputable abbrev numClausesAt (n : ℕ) := (Φn n).clauses.length

/-- The clause factor (1 - z_c · gadget_c) for the n-th formula -/
noncomputable abbrev cvFactorAt (n : ℕ) (c : Fin (numClausesAt n)) :
    MvPolynomial (Fin (npNumVars n)) ℚ :=
  IdentityMinor.cvFactor ℚ (Φn n) c

/-- The clause gadget for clause c -/
noncomputable abbrev clauseGadgetAt (n : ℕ) (c : Fin (numClausesAt n)) :
    MvPolynomial (Fin (npNumVars n)) ℚ :=
  clauseGadget ℚ (Φn n) c

/-- Selector variable index for clause c -/
noncomputable abbrev selectorAt (n : ℕ) (c : Fin (numClausesAt n)) :
    Fin (npNumVars n) :=
  selectorIdx (Φn n) c

-- ============================================================
-- §2. Canonical Selector Windows
-- ============================================================

/-! ### Block structure of tseitinPartition

Key fact: In `tseitinPartition`, selector z_c is in block (c+1),
and ALL non-selector variables are in block 0.

Consequence: A block-admissible list of length κ can contain at most
ONE non-selector variable (from block 0). The remaining κ-1 (or all κ)
elements must be distinct selectors from distinct blocks.

For the rank bound, we can focus on pure-selector derivative lists,
since mixing in a block-0 variable only reduces the available
selector diversity (fewer distinct blocks). -/

/-- A canonical selector window: a set of κ distinct clauses whose
    selectors form a block-admissible derivative list. -/
structure CanonicalWindow (n κ : ℕ) where
  /-- The hit clause indices -/
  hitClauses : Finset (Fin (numClausesAt n))
  /-- Exactly κ clauses hit -/
  card_eq : hitClauses.card = κ

/-- The selector derivative list for a canonical window -/
noncomputable def CanonicalWindow.selectorList {n κ : ℕ}
    (w : CanonicalWindow n κ) : List (Fin (npNumVars n)) :=
  (w.hitClauses.val.toList).map (selectorAt n)

/-- The SPDP generator from a canonical window with shift monomial m:
    mlProj(m · iterDerivList(selectors, tseitinPoly)) -/
noncomputable def canonicalGenerator {n κ : ℕ}
    (w : CanonicalWindow n κ)
    (m : MvPolynomial (Fin (npNumVars n)) ℚ) :
    MvPolynomial (Fin (npNumVars n)) ℚ :=
  mlProj (m * iterDerivList w.selectorList (tseitinPoly ℚ n))

/-! ### Reduction to canonical windows

Every mlBlockedSpdpSubspace generator for tseitinPartition can be
expressed as a linear combination of canonical generators.

The key insight: block-admissible lists for tseitinPartition have
elements from distinct blocks. Since block 0 contains all non-selectors
and blocks 1..m contain one selector each, at most one element is
non-selector. The non-selector derivative either:
(a) hits a clause variable appearing in some gadget → bounded contribution
(b) hits nothing in the product → zero

In either case, the resulting generator lies in the span of canonical
(pure-selector) generators with slightly modified shift monomials. -/

/-- The subspace spanned by canonical window generators -/
noncomputable def canonicalSubspace (n κ : ℕ) :
    Submodule ℚ (MvPolynomial (Fin (npNumVars n)) ℚ) :=
  Submodule.span ℚ
    { q | ∃ (w : CanonicalWindow n κ)
            (m : MvPolynomial (Fin (npNumVars n)) ℚ),
        m.totalDegree ≤ κ ∧
        m.vars ⊆ w.selectorList.toFinset ∧
        q = canonicalGenerator w m }

/-! ### Key structural fact

In tseitinPartition, non-selector variables are all in block 0.
A block-admissible list of length κ has at most 1 non-selector,
with the remaining κ-1 (or all κ) being selectors from distinct blocks.

For the rank bound, we show the SPDP subspace (with general admissible
lists) is contained in the canonical (pure-selector) subspace.
If the list has a non-selector v in block 0, then pderiv v of the
Tseitin product gives a bounded linear combination (≤ 10 terms by
bounded occurrence) of products where one clause gadget is differentiated.
Each such term, after the remaining selector derivatives, produces a
generator in the canonical subspace (with the extra pderiv absorbed
into the shift monomial m). -/

/-- Non-selector variables are in block 0 of tseitinPartition -/
theorem tseitinPartition_nonSelector_block0 (n : ℕ)
    (v : Fin (npNumVars n))
    (hv : ∀ c : Fin (numClausesAt n), v ≠ selectorAt n c) :
    ((NPWitness.tseitinPartition n).assign v).val = 0 := by
  -- Unfold to the raw IdentityMinor definition
  show ((IdentityMinor.tseitinPartition (tseitinAt n)).assign v).val = 0
  simp only [IdentityMinor.tseitinPartition]
  split
  · rename_i h
    -- v is in the selector range → contradicts hv
    exfalso
    have hc : v.val - ((tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length) <
        (tseitinAt n).clauses.length := h.2
    let c : Fin (tseitinAt n).clauses.length :=
      ⟨v.val - ((tseitinAt n).graph.numEdges + 3 * (tseitinAt n).clauses.length), hc⟩
    have : v = selectorIdx (tseitinAt n) c := by
      ext; simp [selectorIdx, c]; omega
    exact hv c this
  · rfl

/-- Elements in block 0 of tseitinPartition are non-selectors -/
theorem tseitinPartition_block0_nonSelector (n : ℕ)
    (v : Fin (npNumVars n))
    (hv : ((NPWitness.tseitinPartition n).assign v).val = 0) :
    ∀ c : Fin (numClausesAt n), v ≠ selectorAt n c := by
  intro c hvc
  -- If v = selectorAt n c, then v is in block c+1, not block 0
  have := IdentityMinor.tseitinPartition_selectorIdx (tseitinAt n) c
  rw [hvc] at hv
  simp only [NPWitness.tseitinPartition] at hv
  rw [this] at hv
  simp at hv

/-- Block 0 of tseitinPartition has at most 1 element in any admissible list -/
theorem admissible_block0_le_one (n : ℕ)
    (S : List (Fin (npNumVars n)))
    (hadm : isBlockAdmissible (NPWitness.tseitinPartition n) S) :
    (S.filter (fun v => ((NPWitness.tseitinPartition n).assign v).val = 0)).length ≤ 1 := by
  have h := hadm.2 ⟨0, by
    simp only [NPWitness.tseitinPartition, IdentityMinor.tseitinPartition]
    omega⟩
  convert h using 1
  congr 1; ext v; simp [Fin.ext_iff]

/-- If v is in a non-zero block of tseitinPartition, then v is a selector -/
theorem tseitinPartition_nonzero_block_is_selector (n : ℕ)
    (v : Fin (npNumVars n))
    (hv : ((NPWitness.tseitinPartition n).assign v).val ≠ 0) :
    ∃ c : Fin (numClausesAt n), v = selectorAt n c := by
  -- The assign function: if v.val ≥ base ∧ v.val - base < numClauses,
  -- then block = v.val - base + 1 (≠ 0). Otherwise block = 0.
  -- Since block ≠ 0, v must be in the selector range.
  simp only [NPWitness.tseitinPartition, IdentityMinor.tseitinPartition] at hv
  -- After unfolding, the split gives block 0 in the else case
  -- So hv forces the if-condition to hold
  split at hv
  · rename_i h
    set Φ := tseitinAt n with hΦ
    set base := Φ.graph.numEdges + 3 * Φ.clauses.length with hbase
    refine ⟨⟨v.val - base, h.2⟩, ?_⟩
    apply Fin.ext
    simp only [selectorAt, selectorIdx, Fin.val_mk, ← hΦ, ← hbase]
    omega
  · simp at hv

/-- Inverse of selectorIdx: given v in the selector range, recover the clause index -/
noncomputable def selectorInv (n : ℕ) (v : Fin (npNumVars n))
    (hv : ((NPWitness.tseitinPartition n).assign v).val ≠ 0) :
    Fin (numClausesAt n) :=
  (tseitinPartition_nonzero_block_is_selector n v hv).choose

theorem selectorInv_spec (n : ℕ) (v : Fin (npNumVars n))
    (hv : ((NPWitness.tseitinPartition n).assign v).val ≠ 0) :
    v = selectorAt n (selectorInv n v hv) :=
  (tseitinPartition_nonzero_block_is_selector n v hv).choose_spec

theorem admissible_list_selector_decomp (n : ℕ)
    (S : List (Fin (npNumVars n)))
    (hadm : isBlockAdmissible (NPWitness.tseitinPartition n) S) :
    ∃ (sels : List (Fin (numClausesAt n))) (nonsels : List (Fin (npNumVars n))),
      S.Perm (sels.map (selectorAt n) ++ nonsels) ∧
      sels.Nodup ∧ nonsels.length ≤ 1 ∧
      (∀ v ∈ nonsels, ∀ c : Fin (numClausesAt n), v ≠ selectorAt n c) := by
  sorry

/-- Key rank reduction: the SPDP subspace for tseitinPartition equals the
    subspace generated by pure-selector admissible lists.
    Non-selector derivatives contribute generators that lie in the span
    of selector-based generators (via Leibniz + bounded occurrence). -/
theorem spdp_subspace_le_canonical (n κ : ℕ)
    (hparam : AdmissibleSpdpParams n κ) :
    mlBlockedSpdpSubspace (NPWitness.tseitinPartition n) κ κ (tseitinPoly ℚ n) ≤
    canonicalSubspace n κ := by
  sorry

-- ============================================================
-- §3. Factored Form of Canonical Generators
-- ============================================================

/-! ### Using iterDeriv_cvProd_eq

From IdentityMinor.lean, we have:
  iterDerivList (ks.map selectorIdx) (∏ cvFactor) =
    C((-1)^|ks|) * (ks.map clauseGadget).prod * (univ \ ks.toFinset).prod cvFactor

So a canonical generator with hit set C and shift m becomes:
  mlProj(m · C((-1)^κ) · ∏_{c∈C} gadget_c · ∏_{c∉C} factor_c)

The ∏_{c∉C} factor_c is the "unhit product" — the object that must be
compressed by locality/profile structure. -/

/-- The "hit gadget product" for a window -/
noncomputable def hitGadgetProd {n κ : ℕ} (w : CanonicalWindow n κ) :
    MvPolynomial (Fin (npNumVars n)) ℚ :=
  w.hitClauses.prod (clauseGadgetAt n)

/-- The "unhit factor product" for a window -/
noncomputable def unhitFactorProd {n κ : ℕ} (w : CanonicalWindow n κ) :
    MvPolynomial (Fin (npNumVars n)) ℚ :=
  (Finset.univ \ w.hitClauses).prod (cvFactorAt n)

/-- Factored form: selector derivative of tseitinPoly gives
    signed product of gadgets × unhit factors.
    This bridges IdentityMinor.iterDeriv_cvProd_eq to our ProfileCompression types.

    For a canonical window w with hit clauses C:
    iterDerivList(selectors of C, tseitinPoly) =
      C((-1)^κ) * hitGadgetProd w * unhitFactorProd w  -/
theorem canonical_generator_factored (n κ : ℕ)
    (cs : List (Fin (numClausesAt n))) (hnd : cs.Nodup)
    (hlen : cs.length = κ) :
    iterDerivList (cs.map (selectorAt n)) (tseitinPoly ℚ n) =
    C ((-1 : ℚ) ^ κ) * (cs.map (clauseGadgetAt n)).prod *
      (Finset.univ \ cs.toFinset).prod (cvFactorAt n) := by
  -- tseitinPoly = coupledVerifier = ∏ cvFactor (by definition)
  show iterDerivList (cs.map (selectorIdx (tseitinAt n)))
    (coupledVerifier ℚ (tseitinAt n)) = _
  rw [coupledVerifier_eq_prod]
  rw [iterDeriv_cvProd_eq (tseitinAt n) cs hnd Finset.univ (fun k _ => Finset.mem_univ k)]
  subst hlen
  rfl

-- ============================================================
-- §3.5. mlProj multiplicativity for disjoint variables
-- ============================================================

/-! ### mlProj distributes over products with disjoint variables

This is the key algebra lemma for the near/far factorization.
If vars(p) and vars(q) are disjoint, then a monomial of p*q is β+γ
where β is from p and γ is from q, with disjoint supports.
Then β+γ is multilinear iff both β and γ are multilinear.
So mlProj(p*q) = mlProj(p) * mlProj(q). -/

/-- Multilinear monomials with disjoint support compose: if α + β is multilinear
    and their supports are disjoint, then both α and β are multilinear. -/
theorem isMultilinear_of_add_disjoint {σ : Type*} [DecidableEq σ]
    (α β : σ →₀ ℕ) (hml : Finsupp.IsMultilinear (α + β))
    (hdisj : Disjoint α.support β.support) :
    Finsupp.IsMultilinear α ∧ Finsupp.IsMultilinear β := by
  constructor <;> intro i <;> {
    have := hml i
    simp [Finsupp.add_apply] at this
    omega
  }

/-- Converse: if both are multilinear and supports are disjoint, sum is multilinear -/
theorem isMultilinear_add_of_disjoint {σ : Type*} [DecidableEq σ]
    (α β : σ →₀ ℕ) (hα : Finsupp.IsMultilinear α) (hβ : Finsupp.IsMultilinear β)
    (hdisj : Disjoint α.support β.support) :
    Finsupp.IsMultilinear (α + β) := by
  intro i
  simp [Finsupp.add_apply]
  by_cases hi : i ∈ α.support
  · have hni : i ∉ β.support := Finset.disjoint_left.mp hdisj hi
    have : β i = 0 := by rwa [Finsupp.mem_support_iff, not_not] at hni
    rw [this, add_zero]; exact hα i
  · have : α i = 0 := by rwa [Finsupp.mem_support_iff, not_not] at hi
    rw [this, zero_add]; exact hβ i

/-- mlProj distributes over products with disjoint variables.
    If vars(p) ∩ vars(q) = ∅, then mlProj(p * q) = mlProj(p) * mlProj(q). -/
theorem mlProj_mul_disjoint_vars {σ : Type*} [DecidableEq σ]
    {F : Type*} [CommRing F]
    (p q : MvPolynomial σ F)
    (hdisj : Disjoint p.vars q.vars) :
    mlProj (p * q) = mlProj p * mlProj q := by
  -- Proof outline:
  -- 1. Write p = Σ monomial α (coeff α p), q = Σ monomial β (coeff β q)
  -- 2. p*q = Σ monomial (α+β) (coeff α p * coeff β q)
  -- 3. mlProj filters to multilinear monomials
  -- 4. For α ∈ support(p), β ∈ support(q): α.support ⊆ p.vars, β.support ⊆ q.vars
  --    so α.support ∩ β.support = ∅ (from hdisj)
  -- 5. IsMultilinear(α+β) ↔ IsMultilinear(α) ∧ IsMultilinear(β) (by disjoint supports)
  -- 6. Therefore mlProj(p*q) = Σ_{ML α, ML β} monomial(α+β)(coeff α * coeff β)
  --                          = mlProj(p) * mlProj(q)
  sorry

-- ============================================================
-- §4. Live Interfaces and Boundary Reduction
-- ============================================================

/-! ### The compression mechanism

The unhit product ∏_{c∉C} (1 - z_c · gadget_c) involves all m-κ
remaining clauses. Naively this is exponentially rich.

But after multilinear projection, only variables that appear in BOTH
the hit gadgets AND the unhit factors contribute non-trivially.
These shared variables form the "live interfaces."

For 3-SAT with bounded occurrence (each variable in ≤ O(1) clauses),
each hit clause c shares variables with at most O(1) neighboring
clauses. So the total number of "live" unhit clauses is O(κ).

The unhit clauses that share NO variables with any hit clause
contribute a factor that is independent of the hit set, and hence
contributes the same subspace for every window. This factor can
be absorbed into the profile machinery. -/

/-- Clauses neighboring the hit set: share at least one variable -/
noncomputable def neighborClauses {n κ : ℕ} (w : CanonicalWindow n κ) :
    Finset (Fin (numClausesAt n)) :=
  (Finset.univ \ w.hitClauses).filter (fun d =>
    ∃ c ∈ w.hitClauses, ∃ v,
      v ∈ clauseVarSet (tseitinAt n) c ∧ v ∈ clauseVarSet (tseitinAt n) d)

/-- Each hit clause neighbors at most O(1) other clauses.
    By `conflicting_card_le`, each clause conflicts with ≤ 30 others.
    With κ hit clauses, at most 30κ neighbors by union bound. -/
theorem neighbor_clauses_card_le {n κ : ℕ} (w : CanonicalWindow n κ) :
    (neighborClauses w).card ≤ 30 * κ := by
  -- neighborClauses ⊆ biUnion of conflicting sets
  have hsub : neighborClauses w ⊆
      w.hitClauses.biUnion (fun c => conflicting (tseitinAt n) c) := by
    intro d hd
    simp only [neighborClauses, Finset.mem_filter, Finset.mem_sdiff] at hd
    obtain ⟨⟨_, _⟩, c, hc, v, hvc, hvd⟩ := hd
    exact Finset.mem_biUnion.mpr ⟨c, hc, by
      simp only [conflicting, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Finset.not_disjoint_iff.mpr ⟨v, hvc, hvd⟩⟩
  calc (neighborClauses w).card
      ≤ (w.hitClauses.biUnion (fun c => conflicting (tseitinAt n) c)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ c ∈ w.hitClauses, (conflicting (tseitinAt n) c).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ w.hitClauses, 30 :=
        Finset.sum_le_sum (fun c _ => conflicting_card_le (tseitinAt n) c)
    _ = 30 * κ := by simp [Finset.sum_const, w.card_eq, mul_comm]

-- ============================================================
-- §5. Profile Histograms
-- ============================================================

/-! ### Local clause types

In the Tseitin construction, every clause gadget has the same
algebraic form: a product/sum of 3 literal polynomials.
The "type" of a clause relative to a hit set is determined by
how many of its variables are shared with hit clauses.

Since each clause has exactly 3 variables, the type is one of:
  0 shared, 1 shared, 2 shared, or 3 shared
giving |Σ| = 4 local types. -/

/-- Local interface type: number of variables shared with the hit set.
    For 3-SAT, this is 0, 1, 2, or 3. -/
abbrev LocalInterfaceType := Fin 4

/-- Profile histogram: for each local type, how many unhit neighbors
    have that type. -/
abbrev ProfileHist := LocalInterfaceType → ℕ

/-- The profile of a canonical window: histogram of neighbor types -/
noncomputable def windowProfile {n κ : ℕ} (w : CanonicalWindow n κ) :
    ProfileHist :=
  fun τ => ((neighborClauses w).filter (fun d =>
    -- Count shared variables between d and the hit set
    (Finset.univ.filter (fun c =>
      c ∈ w.hitClauses ∧
      ∃ v, v ∈ clauseVarSet (tseitinAt n) c ∧ v ∈ clauseVarSet (tseitinAt n) d
    )).card = τ.val
  )).card

/-- Total mass of a profile is at most the number of neighbors.
    Each neighbor clause is counted in exactly one type bucket,
    so the sum over types = |neighborClauses| ≤ 30κ. -/
theorem profile_total_mass_le {n κ : ℕ} (w : CanonicalWindow n κ) :
    ∑ τ : LocalInterfaceType, windowProfile w τ ≤ 30 * κ := by
  -- Each τ counts a disjoint subset of neighborClauses
  -- So sum ≤ |neighborClauses| ≤ 30κ
  sorry

/-- Number of realizable profiles with total mass ≤ R.
    Stars-and-bars: histograms over 4 types with total ≤ R
    have at most (R+1)^4 possibilities (each coordinate ∈ {0,...,R}). -/
theorem num_profiles_le (R : ℕ)
    (S : Finset ProfileHist) (hS : ∀ h ∈ S, ∑ τ, h τ ≤ R) :
    S.card ≤ (R + 1) ^ 4 := by
  -- Each h ∈ S has h(τ) ≤ R for all τ (since h(τ) ≤ ∑ h ≤ R)
  -- So h maps into Fin (R+1)^4, giving the bound
  -- Injection: h ↦ (⟨h 0, ...⟩, ..., ⟨h 3, ...⟩)
  have hcoord : ∀ h ∈ S, ∀ τ : Fin 4, h τ < R + 1 := by
    intro h hh τ
    have := hS h hh
    have : h τ ≤ ∑ τ, h τ := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ)
    omega
  -- Build injection into (Fin (R+1))^4
  let f : ProfileHist → (Fin 4 → Fin (R + 1)) := fun h τ =>
    if hlt : h τ < R + 1 then ⟨h τ, hlt⟩ else ⟨0, by omega⟩
  have hinj : Set.InjOn f ↑S := by
    intro a ha b hb hab
    ext τ
    have ha' := hcoord a ha τ
    have hb' := hcoord b hb τ
    have := congr_fun hab τ
    simp only [f, dif_pos ha', dif_pos hb', Fin.mk.injEq] at this
    exact this
  calc S.card
      ≤ (Finset.univ : Finset (Fin 4 → Fin (R + 1))).card :=
        Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) hinj
    _ = (R + 1) ^ 4 := by simp [Fintype.card_fin]

-- ============================================================
-- §6. Within-Profile Subspace Dimension
-- ============================================================

/-! ### Per-profile dimension bound

For each profile h, the generators from windows with that profile
lie in a subspace of dimension at most ∏_τ C(h(τ) + d_τ, d_τ)
where d_τ is the local derivative space dimension for type τ.

From TypeDecomp.lean: `localDerivSpace_finrank_le_16` gives d_τ ≤ 16
for width-4 clause gadgets.

The key structural insight: after fixing the profile, the only
degrees of freedom are:
1. Which specific clauses of each type are "active" (absorbed by profile)
2. The local derivative space contribution per active clause (dim ≤ 16)
3. The shift monomial (degree ≤ κ, support ⊆ hit selectors)

The shift monomial contributes at most C(κ + κ, κ) ≤ (2κ)^κ ≤ n
additional dimensions (since κ ≤ log₂ n).

Total per-profile dimension: ≤ 16^κ · n ≤ n · n^4 = n^5
(using 16^κ ≤ 16^(log₂ n) = n^4).
-/

/-- Per-profile dimension bound.
    For a fixed profile h with total mass R ≤ 30κ,
    the subspace of generators with that profile has dimension
    at most n^5. -/
theorem within_profile_dim_le (n κ : ℕ)
    (hparam : AdmissibleSpdpParams n κ)
    (h : ProfileHist) (hR : ∑ τ, h τ ≤ 30 * κ) :
    -- The subspace of generators from windows with profile h
    -- has finrank ≤ n^5
    True := by  -- placeholder for the real statement
  trivial

-- ============================================================
-- §7. Assembly: Sum Over Profiles
-- ============================================================

/-! ### Putting it all together

Total rank ≤ (number of profiles) × (per-profile dimension)
         ≤ (30κ + 1)^4 × n^5
         ≤ (9 log₂ n + 1)^4 × n^5
         ≤ n^5 × n^4       (for n ≥ 16, since (9 log n + 1)^4 ≤ n^4)
         ≤ n^9
         ≤ n^10

This gives the final bound matching the axiom. -/

/-- The assembly arithmetic: (Cκ)^D ≤ n^10 for κ ≤ log₂ n.
    The total rank is polynomial in κ (polylog in n), hence ≤ n^10.
    Exact constants TBD once per-profile dimension is established. -/
theorem polylog_le_poly (n κ C D : ℕ) (hn : n ≥ 2)
    (hκ : κ ≤ Nat.log 2 n) (hD : D ≤ 10) :
    (C * κ + 1) ^ D ≤ n ^ 10 := by
  sorry

/-! ### Main theorem (target: replace the axiom)

Once all layers are proved, this replaces `tseitin_spdp_rank_bound`. -/

-- theorem tseitin_spdp_rank_bound_proved (n : ℕ) (hn : n ≥ 4)
--     (κ : ℕ) (hparam : AdmissibleSpdpParams n κ) :
--     mlBlockedSpdpRank (tseitinPartition n) κ κ (tseitinPoly ℚ n) ≤ n ^ 10 := by
--   sorry

end SPDP
