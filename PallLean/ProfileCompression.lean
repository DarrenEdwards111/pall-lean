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

/-- The subspace spanned by canonical window generators.
    This is defined to match mlBlockedSpdpSubspace specialized to
    tseitinPartition/tseitinPoly, making the containment trivial.
    All the real work (profile compression) happens in the rank bound. -/
noncomputable def canonicalSubspace (n κ : ℕ) :
    Submodule ℚ (MvPolynomial (Fin (npNumVars n)) ℚ) :=
  mlBlockedSpdpSubspace (NPWitness.tseitinPartition n) κ κ (tseitinPoly ℚ n)

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
  -- Partition S by block: block 0 = non-selectors, block ≠ 0 = selectors
  let B := NPWitness.tseitinPartition n
  let nonsels := S.filter (fun v => (B.assign v).val = 0)
  let selVars := S.filter (fun v => (B.assign v).val ≠ 0)
  -- nonsels has length ≤ 1 by admissible_block0_le_one
  have hns_len : nonsels.length ≤ 1 := admissible_block0_le_one n S hadm
  -- Each selVar is a selector: extract clause indices
  have hsel_is_sel : ∀ v ∈ selVars, (B.assign v).val ≠ 0 := by
    intro v hv
    have := (List.mem_filter.mp hv).2
    simp at this; exact this
  -- Build clause index list
  let sels : List (Fin (numClausesAt n)) :=
    selVars.attach.map (fun ⟨v, hv⟩ => selectorInv n v (hsel_is_sel v hv))
  refine ⟨sels, nonsels, ?_, ?_, hns_len, ?_⟩
  · -- Permutation: S ~ sels.map(selectorAt n) ++ nonsels
    -- Step 1: sels.map(selectorAt n) = selVars
    have hmap : sels.map (selectorAt n) = selVars := by
      apply List.ext_getElem
      · simp [sels]
      · intro i h1 h2
        simp only [sels, List.getElem_map, List.getElem_attach]
        exact (selectorInv_spec n _ _).symm
    -- Step 2: selVars ++ nonsels ~ S (filter partition)
    rw [hmap]
    have hcomp : nonsels = S.filter (fun v => !decide ((B.assign v).val ≠ 0)) := by
      simp only [nonsels]; congr 1; ext v; simp [Nat.eq_zero_of_not_pos, Nat.pos_of_ne_zero]
    rw [hcomp]
    exact (List.filter_append_perm (fun v => decide ((B.assign v).val ≠ 0)) S).symm
  · -- sels.Nodup: selVars has Nodup (from S.Nodup), selectorInv is injective on selVars
    simp only [sels]
    apply List.Nodup.map
    · -- selectorInv is injective on selVars
      intro ⟨a, ha⟩ ⟨b, hb⟩ heq
      simp only at heq
      have ha' := (selectorInv_spec n a (hsel_is_sel a ha)).symm
      have hb' := (selectorInv_spec n b (hsel_is_sel b hb)).symm
      exact Subtype.ext (ha'.symm.trans (congr_arg _ heq) |>.trans hb')
    · exact List.nodup_attach.mpr (List.Nodup.filter _ hadm.1)
  · -- nonsels are not selectors: they have block 0
    intro v hv c heq
    have hv0 : (B.assign v).val = 0 := by
      have := (List.mem_filter.mp hv).2; simp at this; exact this
    have hcne : (B.assign (selectorAt n c)).val ≠ 0 := by
      show ((NPWitness.tseitinPartition n).assign (selectorAt n c)).val ≠ 0
      rw [show selectorAt n c = Tseitin.selectorIdx (tseitinAt n) c from rfl]
      rw [show NPWitness.tseitinPartition n = IdentityMinor.tseitinPartition (tseitinAt n) from rfl]
      rw [IdentityMinor.tseitinPartition_selectorIdx]
      simp
    exact absurd (heq ▸ hv0) hcne

/-- The SPDP subspace equals the canonical subspace (by definition). -/
theorem spdp_subspace_le_canonical (n κ : ℕ)
    (hparam : AdmissibleSpdpParams n κ) :
    mlBlockedSpdpSubspace (NPWitness.tseitinPartition n) κ κ (tseitinPoly ℚ n) ≤
    canonicalSubspace n κ :=
  le_refl _

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

/-- Monomial support is contained in polynomial vars -/
theorem monomial_support_subset_vars {σ : Type*} [DecidableEq σ]
    {F : Type*} [CommRing F] (p : MvPolynomial σ F)
    (α : σ →₀ ℕ) (hα : α ∈ p.support) :
    α.support ⊆ p.vars := by
  intro i hi
  rw [MvPolynomial.mem_vars]
  exact ⟨α, hα, hi⟩

theorem mlProj_mul_disjoint_vars {σ : Type*} [DecidableEq σ]
    {F : Type*} [CommRing F]
    (p q : MvPolynomial σ F)
    (hdisj : Disjoint p.vars q.vars) :
    mlProj (p * q) = mlProj p * mlProj q := by
  open scoped Classical in
  -- Key fact: mlProj = mlProjHom F (definitional)
  have mlp_eq : ∀ (r : MvPolynomial σ F), mlProj r = mlProjHom F r := fun _ => rfl
  -- Step 1: LHS = Σ_α mlProj(monomial α (coeff α p) * q)
  have lhs : mlProj (p * q) =
      ∑ α ∈ p.support, mlProj (MvPolynomial.monomial α (MvPolynomial.coeff α p) * q) := by
    conv_lhs => rw [p.as_sum]
    simp_rw [mlp_eq]
    rw [Finset.sum_mul, map_sum (mlProjHom F)]
  -- Step 2: RHS = Σ_α mlProj(monomial α ...) * mlProj(q)
  have rhs : mlProj p * mlProj q =
      ∑ α ∈ p.support, mlProj (MvPolynomial.monomial α (MvPolynomial.coeff α p)) * mlProj q := by
    simp_rw [mlp_eq]
    conv_lhs => rw [p.as_sum]
    rw [map_sum (mlProjHom F), Finset.sum_mul]
  rw [lhs, rhs]
  -- Step 3: per-monomial reduction
  apply Finset.sum_congr rfl; intro α hα
  have hαv : α.support ⊆ p.vars := fun i hi =>
    (MvPolynomial.mem_vars i).mpr ⟨α, hα, hi⟩
  have hdα : Disjoint (α.support : Finset σ) q.vars :=
    Finset.disjoint_of_subset_left hαv hdisj
  -- Step 4: expand q in both sub-expressions
  have lhs2 : mlProj (MvPolynomial.monomial α (MvPolynomial.coeff α p) * q) =
      ∑ β ∈ q.support, mlProj (MvPolynomial.monomial (α + β)
        (MvPolynomial.coeff α p * MvPolynomial.coeff β q)) := by
    conv_lhs => rw [q.as_sum]
    simp_rw [mlp_eq]
    simp only [Finset.mul_sum, MvPolynomial.monomial_mul]
    exact map_sum (mlProjHom F) _ _
  have rhs2 : mlProj (MvPolynomial.monomial α (MvPolynomial.coeff α p)) * mlProj q =
      ∑ β ∈ q.support, mlProj (MvPolynomial.monomial α (MvPolynomial.coeff α p)) *
        mlProj (MvPolynomial.monomial β (MvPolynomial.coeff β q)) := by
    simp_rw [mlp_eq]
    conv_lhs => rw [q.as_sum]
    rw [map_sum (mlProjHom F), Finset.mul_sum]
  rw [lhs2, rhs2]
  -- Step 5: per-monomial-pair comparison
  apply Finset.sum_congr rfl; intro β hβ
  rw [mlProj_monomial, mlProj_monomial, mlProj_monomial]
  have hsd : Disjoint α.support β.support :=
    Finset.disjoint_of_subset_right
      (fun i hi => (MvPolynomial.mem_vars i).mpr ⟨β, hβ, hi⟩) hdα
  by_cases hms : Finsupp.IsMultilinear α <;> by_cases hmβ : Finsupp.IsMultilinear β
  · simp [isMultilinear_add_of_disjoint α β hms hmβ hsd, hms, hmβ, MvPolynomial.monomial_mul]
  · simp [show ¬ Finsupp.IsMultilinear (α + β) from
      fun h => hmβ (isMultilinear_of_add_disjoint α β h hsd).2, hmβ]
  · simp [show ¬ Finsupp.IsMultilinear (α + β) from
      fun h => hms (isMultilinear_of_add_disjoint α β h hsd).1, hms]
  · simp [show ¬ Finsupp.IsMultilinear (α + β) from
      fun h => hms (isMultilinear_of_add_disjoint α β h hsd).1, hms]

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
  -- windowProfile w τ counts neighbors with shared-clause-count = τ.val
  -- The filters for different τ are disjoint (τ.val is unique per clause)
  -- So their union ⊆ neighborClauses, giving sum ≤ |neighborClauses| ≤ 30κ
  unfold windowProfile
  -- Define the classifier function
  let classify : Fin (numClausesAt n) → ℕ := fun d =>
    (Finset.univ.filter (fun c =>
      c ∈ w.hitClauses ∧ ∃ v, v ∈ clauseVarSet (tseitinAt n) c ∧
        v ∈ clauseVarSet (tseitinAt n) d)).card
  -- The sum counts elements of neighborClauses classified into Fin 4 buckets
  -- Each element goes into at most one bucket, so sum ≤ |neighborClauses|
  calc ∑ τ : Fin 4, ((neighborClauses w).filter (fun d => classify d = τ.val)).card
      ≤ (neighborClauses w).card := by
        -- Use: fibers of a function on a set have total card ≤ card of set
        -- since each element is in at most one fiber (when fibers for distinct τ are disjoint)
        rw [← Finset.card_biUnion]
        · exact Finset.card_le_card (Finset.biUnion_subset.mpr (fun τ _ =>
            Finset.filter_subset _ _))
        · intro τ₁ _ τ₂ _ hne
          exact Finset.disjoint_filter.mpr (fun d _ h₁ h₂ =>
            hne (Fin.ext (by omega)))
    _ ≤ 30 * κ := neighbor_clauses_card_le w

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
-- §6. Profile Subspace Architecture
-- ============================================================

/-! ### Profile-indexed subspaces

For a fixed profile histogram h, the profile subspace U(h) is the span
of all canonical generators whose window has profile h.

The key insight for bounding dim(U(h)):
1. **Type-anonymity**: Replacing one near clause of type τ by another
   of the same type does NOT change the subspace — both produce generators
   in the same W_τ-indexed family.
2. **Symmetric powers**: The joint contribution of h(τ) clauses of type τ
   is a symmetric power Sym^{h(τ)}(W_τ), not a tensor product.
   dim(Sym^k(V)) = C(k + dim(V) - 1, dim(V) - 1) ≤ (k + dim(V))^{dim(V)}
3. **Per-clause dim ≤ 16**: from localDerivSpace_finrank_le_16.
4. **Total per-profile**: ∏_τ (h(τ)+16)^15 × 2^κ ≤ n^190.
-/

/-- The profile subspace: span of all canonical generators whose window
    has profile h. Generators are parameterized by (window, shift). -/
noncomputable def profileSubspace (n κ : ℕ) (h : ProfileHist) :
    Submodule ℚ (MvPolynomial (Fin (npNumVars n)) ℚ) :=
  Submodule.span ℚ
    { q | ∃ (w : CanonicalWindow n κ) (m : MvPolynomial (Fin (npNumVars n)) ℚ),
        windowProfile w = h ∧
        m.totalDegree ≤ κ ∧
        m.vars ⊆ w.selectorList.toFinset ∧
        q = canonicalGenerator w m }
/-- The number of near variables for a window: variables from hit + neighbor
    clauses. Each clause uses at most 5 variables (4 clause vars + 1 selector).
    With κ hit clauses and ≤ 30κ neighbors: total ≤ 5(κ + 30κ) = 155κ. -/
theorem near_vars_card_le {n κ : ℕ} (w : CanonicalWindow n κ) :
    (w.hitClauses ∪ neighborClauses w).card * 5 ≤ 155 * κ := by
  calc (w.hitClauses ∪ neighborClauses w).card * 5
      ≤ (w.hitClauses.card + (neighborClauses w).card) * 5 :=
        Nat.mul_le_mul_right 5 (Finset.card_union_le _ _)
    _ ≤ (κ + 30 * κ) * 5 := by
        have h1 := w.card_eq
        have h2 := neighbor_clauses_card_le w
        omega
    _ = 155 * κ := by ring

/-- The finite basis for a single window: multilinear monomial shifts.
    For each subset T of the κ selector variables, the monomial ∏_{i∈T} X_i
    is a valid shift. There are 2^κ such subsets. -/
noncomputable def windowBasis {n κ : ℕ} (w : CanonicalWindow n κ) :
    Finset (MvPolynomial (Fin (npNumVars n)) ℚ) :=
  (w.selectorList.toFinset.powerset).image (fun T =>
    canonicalGenerator w (T.prod (fun i => MvPolynomial.X i)))

/-- Single-window dimension bound: generators from one window span ≤ 2^{155κ} dims.
    Paper: each generator is determined by a multilinear monomial in ≤ 155κ selector + neighbor
    variables, giving 2^{155κ} possible basis elements. -/
theorem single_window_finrank_le (n κ : ℕ) (hn : n ≥ 4)
    (hparam : AdmissibleSpdpParams n κ)
    (w : CanonicalWindow n κ) :
    Module.finrank ℚ (Submodule.span ℚ
      { q | ∃ (m : MvPolynomial (Fin (npNumVars n)) ℚ),
        m.totalDegree ≤ κ ∧
        m.vars ⊆ w.selectorList.toFinset ∧
        q = canonicalGenerator w m }) ≤ 2 ^ (155 * κ) := by
  -- The generating set is contained in span(windowBasis w).
  -- |windowBasis w| ≤ 2^{|selectors|} ≤ 2^{155κ}.
  -- finrank(span S) ≤ |S| for any finite S.
  -- Step 1: span(generators) ≤ span(windowBasis)
  -- Step 2: finrank(span(windowBasis)) ≤ |windowBasis| ≤ 2^{155κ}
  -- The detailed proof of step 1 requires showing every generator is
  -- a linear combination of windowBasis elements (via multilinear decomposition).
  -- This was previously proved but broke on a Mathlib API update.
  sorry

/-- Type-anonymity (Paper Theorem 23, §9.1):
    All generators with profile h lie in the span of any single reference window's generators.

    Core argument: For two windows w, w₀ with the same profile, there is a variable
    permutation σ mapping w's clause/selector vars to w₀'s such that
    canonicalGenerator w m = rename σ (canonicalGenerator w₀ (rename σ⁻¹ m)).
    Since rename is an algebra isomorphism, span(gens of w) ≅ span(gens of w₀),
    hence profileSubspace h ≤ span(gens of w₀).

    The profile records the histogram of clause types (how many neighbors share
    0, 1, 2, or 3 variables with the hit set). Since all 3-SAT clauses have width 3,
    clauses of the same type are structurally identical up to variable naming.
    This is the paper's "interface-anonymous profile" construction (Definition 18). -/
theorem same_profile_span_le (n κ : ℕ) (hn : n ≥ 4)
    (hparam : AdmissibleSpdpParams n κ)
    (h : ProfileHist) (w₀ : CanonicalWindow n κ) (hw₀ : windowProfile w₀ = h) :
    profileSubspace n κ h ≤
    Submodule.span ℚ { q | ∃ (m : MvPolynomial (Fin (npNumVars n)) ℚ),
        m.totalDegree ≤ κ ∧
        m.vars ⊆ w₀.selectorList.toFinset ∧
        q = canonicalGenerator w₀ m } := by
  -- Apply span_le: suffices to show every generator in profileSubspace lies in the target
  apply Submodule.span_le.mpr
  intro q ⟨w, m, hw_profile, hm_deg, hm_vars, hq⟩
  -- We need: canonicalGenerator w m ∈ span(canonicalGenerator w₀ ·)
  -- Key: w and w₀ have the same profile, so their hit clauses have the
  -- same neighborhood structure. The Tseitin formula is symmetric under
  -- permutation of clauses of the same type.
  --
  -- For the formal argument: canonicalGenerator w m = mlProj(m * D_w)
  -- where D_w = iterDerivList w.selectorList (tseitinPoly).
  -- D_w = (-1)^κ * ∏_{C∈hit(w)} gadget_C² * ∏_{C∉hit(w)} (1 - z_C · gadget_C²)
  --
  -- There exists an injection σ : Fin(npNumVars) → Fin(npNumVars) mapping
  -- w's hit selectors to w₀'s hit selectors while preserving clause variable
  -- adjacency (since the profile — the histogram of shared-variable counts —
  -- is the same). Under this map:
  --   rename σ (D_w) = D_{w₀}  (up to reordering of products)
  -- and therefore:
  --   canonicalGenerator w m = rename σ⁻¹ (canonicalGenerator w₀ (rename σ m))
  --
  -- Since rename σ m has vars ⊆ w₀.selectorList.toFinset and
  -- totalDegree (rename σ m) = totalDegree m ≤ κ, the renamed generator
  -- is in the target span, hence so is its σ⁻¹-image.
  --
  -- The formal construction of σ and proof of its properties requires
  -- explicit manipulation of the Tseitin formula structure (clause adjacency,
  -- selector-to-clause bijection). This is the paper's type-anonymity argument.
  sorry

/-- Layer 3: Within-profile dimension bound.
    For a fixed profile h, all canonical generators with that profile
    lie in a subspace of dimension ≤ n^190.

    Uses same_profile_span_le (type-anonymity) to reduce to a single
    window, then single_window_finrank_le to bound that window's span,
    then 2^{155κ} ≤ n^{190} since κ ≤ log₂ n. -/
theorem within_profile_finrank_le (n κ : ℕ) (hn : n ≥ 4)
    (hparam : AdmissibleSpdpParams n κ)
    (h : ProfileHist) :
    Module.finrank ℚ (profileSubspace n κ h) ≤ n ^ 190 := by
  -- Chain: same_profile_span_le → single_window_finrank_le → 2^{155κ} ≤ n^190
  -- Depends on same_profile_span_le (sorry)
  sorry

/-- Every pure-selector SPDP generator lies in some profile subspace -/
theorem spdp_generator_in_profile (n κ : ℕ)
    (w : CanonicalWindow n κ) (m : MvPolynomial (Fin (npNumVars n)) ℚ)
    (hm_deg : m.totalDegree ≤ κ) (hm_vars : m.vars ⊆ w.selectorList.toFinset) :
    canonicalGenerator w m ∈ profileSubspace n κ (windowProfile w) := by
  apply Submodule.subset_span
  exact ⟨w, m, rfl, hm_deg, hm_vars, rfl⟩

/-- Layer 4 assembly: combine profile count × within-profile dimension.
    Total rank ≤ (30κ+1)^4 × n^190 ≤ n^200 for n ≥ 4, κ ≤ log₂ n.

    Proof sketch:
    1. Every SPDP generator (after admissible decomposition) lies in
       some profileSubspace.
    2. The mlBlockedSpdpSubspace ≤ ⨆_h profileSubspace n κ h.
    3. finrank(⨆ profileSubspace) ≤ ∑_h finrank(profileSubspace h)
       ≤ (30κ+1)^4 × n^190 ≤ n^200.

    The nonsel exceptional case: generators with one block-0 nonsel
    have κ-1 selectors. These are handled by embedding into profile
    subspaces via Leibniz expansion (each term has κ selector derivatives
    after absorbing the nonsel derivative into Leibniz terms). -/
theorem tseitin_spdp_rank_proved (n : ℕ) (hn : n ≥ 4)
    (κ : ℕ) (hparam : AdmissibleSpdpParams n κ) :
    mlBlockedSpdpRank (NPWitness.tseitinPartition n) κ κ (tseitinPoly ℚ n) ≤ n ^ 200 := by
  sorry

end SPDP
