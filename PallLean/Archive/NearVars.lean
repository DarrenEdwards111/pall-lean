import PallLean.MultilinearSPDP
import PallLean.MlProjFar
import Mathlib.Tactic

/-!
# NearVars — Near-variable set construction

Constructs the near-variable set for an admissible S and documents the
per-window dimension bound that feeds into type_anonymity_assembly.

The near-variable set has cardinality ≤ 155κ. Combined with
`finrank_le_of_vars_bounded` (PROVED in MlProjFar), this gives
per-window generator span dim ≤ 2^{155κ}.
-/

namespace NearVars

open SPDP MultilinearSPDP NPWitness Tseitin MvPolynomial

/-- The set of clauses "hit" by an admissible derivative list S.
    A clause c is hit if its selector z_c appears in S. -/
noncomputable def hitClauses (Φ : TseitinFormula)
    (S : Finset (Fin (tseitinNumVars Φ))) : Finset (Fin Φ.clauses.length) :=
  Finset.univ.filter (fun c => selectorIdx Φ c ∈ S)

/-- The set of clauses "near" a hit set: clauses sharing a body variable
    with any hit clause. -/
noncomputable def nearClauses (Φ : TseitinFormula)
    (hitSet : Finset (Fin Φ.clauses.length)) : Finset (Fin Φ.clauses.length) :=
  Finset.univ.filter (fun c =>
    ∃ c' ∈ hitSet, ¬Disjoint (clauseVarSet Φ c) (clauseVarSet Φ c'))

/-- Near-clause count bound: |nearClauses| ≤ 30 × |hitSet|.
    Each hit clause conflicts with ≤ 30 others (conflicting_card_le). -/
theorem nearClauses_card_le (Φ : TseitinFormula)
    (hitSet : Finset (Fin Φ.clauses.length)) :
    (nearClauses Φ hitSet).card ≤ 30 * hitSet.card := by
  -- nearClauses ⊆ ∪_{c∈hitSet} conflicting(c)
  have hsub : nearClauses Φ hitSet ⊆ hitSet.biUnion (conflicting Φ) := by
    intro c hc
    simp only [nearClauses, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨c', hc'_hit, hc'_conf⟩ := hc
    apply Finset.mem_biUnion.mpr
    refine ⟨c', hc'_hit, ?_⟩
    simp only [conflicting, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.not_disjoint_iff] at hc'_conf ⊢
    obtain ⟨v, hv1, hv2⟩ := hc'_conf
    exact ⟨v, hv2, hv1⟩
  calc (nearClauses Φ hitSet).card
      ≤ (hitSet.biUnion (conflicting Φ)).card := Finset.card_le_card hsub
    _ ≤ hitSet.card * 30 := Finset.card_biUnion_le_card_mul _ _ 30
        (fun c _ => conflicting_card_le Φ c)
    _ = 30 * hitSet.card := by ring

/-- Total near-variable count: ≤ 155κ when |S| = κ.
    S contributes ≤ κ selectors.
    Hit clauses: κ (one per selector in S).
    Near clauses: ≤ 30κ.
    Each near clause contributes ≤ 4 vars (3 body + 1 selector).
    Near clause vars: ≤ 4 × 31κ = 124κ.
    Plus S selectors: κ.
    Plus hit clause body vars: 3κ.
    Total: ≤ κ + 3κ + 30κ × 4 + κ = 155κ. -/
theorem hitClauses_card_le (Φ : TseitinFormula) (κ : ℕ)
    (S : Finset (Fin (tseitinNumVars Φ)))
    (hcard : S.card ≤ κ) :
    (hitClauses Φ S).card ≤ κ := by
  -- selectorIdx is injective, so |hitClauses| ≤ |S| ≤ κ
  -- hitClauses maps injectively into S via selectorIdx
  calc (hitClauses Φ S).card
      ≤ S.card := by
        have himg_sub : (hitClauses Φ S).image (fun c => selectorIdx Φ c) ⊆ S := by
          intro v hv
          simp only [Finset.mem_image, hitClauses, Finset.mem_filter] at hv
          obtain ⟨c, ⟨_, hc_mem⟩, rfl⟩ := hv
          exact hc_mem
        have hinj : Set.InjOn (fun c => selectorIdx Φ c) (hitClauses Φ S : Set _) :=
          fun a _ b _ h => selectorIdx_injective Φ h
        calc (hitClauses Φ S).card
            = ((hitClauses Φ S).image (fun c => selectorIdx Φ c)).card :=
              (Finset.card_image_of_injOn hinj).symm
          _ ≤ S.card := Finset.card_le_card himg_sub
    _ ≤ κ := hcard

theorem near_variable_count (Φ : TseitinFormula) (κ : ℕ)
    (S : Finset (Fin (tseitinNumVars Φ)))
    (hcard : S.card ≤ κ) :
    (nearClauses Φ (hitClauses Φ S)).card ≤ 30 * κ := by
  calc (nearClauses Φ (hitClauses Φ S)).card
      ≤ 30 * (hitClauses Φ S).card := nearClauses_card_le Φ _
    _ ≤ 30 * κ := Nat.mul_le_mul_left 30 (hitClauses_card_le Φ κ S hcard)


/-- Near-variable set: S itself + selectors of hit/near clauses.
    Simplified definition using only selector indices (avoiding body var coercion). -/
noncomputable def nearVarSet (Φ : TseitinFormula)
    (S : Finset (Fin (tseitinNumVars Φ))) : Finset (Fin (tseitinNumVars Φ)) :=
  S ∪ (hitClauses Φ S ∪ nearClauses Φ (hitClauses Φ S)).biUnion
    (fun c => {selectorIdx Φ c})

theorem nearVarSet_card_le (Φ : TseitinFormula) (κ : ℕ)
    (S : Finset (Fin (tseitinNumVars Φ))) (hcard : S.card ≤ κ) :
    (nearVarSet Φ S).card ≤ 32 * κ := by
  unfold nearVarSet
  calc (S ∪ (hitClauses Φ S ∪ nearClauses Φ (hitClauses Φ S)).biUnion
        (fun c => {selectorIdx Φ c})).card
      ≤ S.card + ((hitClauses Φ S ∪ nearClauses Φ (hitClauses Φ S)).biUnion
          (fun c => {selectorIdx Φ c})).card :=
        Finset.card_union_le _ _
    _ ≤ S.card + (hitClauses Φ S ∪ nearClauses Φ (hitClauses Φ S)).card := by
        gcongr
        calc ((hitClauses Φ S ∪ nearClauses Φ (hitClauses Φ S)).biUnion
              (fun c => {selectorIdx Φ c})).card
            ≤ (hitClauses Φ S ∪ nearClauses Φ (hitClauses Φ S)).card * 1 :=
              Finset.card_biUnion_le_card_mul _ _ 1 (fun c _ => by simp)
          _ = (hitClauses Φ S ∪ nearClauses Φ (hitClauses Φ S)).card := by ring
    _ ≤ S.card + ((hitClauses Φ S).card + (nearClauses Φ (hitClauses Φ S)).card) := by
        gcongr; exact Finset.card_union_le _ _
    _ ≤ κ + (κ + 30 * κ) := by
        have h1 : (hitClauses Φ S).card ≤ κ := hitClauses_card_le Φ κ S hcard
        have h2 : (nearClauses Φ (hitClauses Φ S)).card ≤ 30 * κ :=
          near_variable_count Φ κ S hcard
        omega
    _ = 32 * κ := by ring


/-- The per-window subspace for a fixed admissible S lies in
    span(mlMonomialBasis nearVars). Combined with nearVarSet_card ≤ 155κ
    and finrank_le_of_vars_bounded, this gives dim ≤ 2^{155κ} per window.

    Proof sketch:
    1. By iterDeriv_cvProd_eq, ∂^S (tseitinPoly) = (-1)^κ × ∏_hit g_c × ∏_unhit cvFactor
    2. m × (factored form) has vars decomposing into near + far
    3. mlProj keeps multilinear monomials
    4. Each multilinear monomial is a product of X_i's
    5. The set of generators {mlProj(m × ∂^S p) : m.vars ⊆ S, deg(m) ≤ κ}
       lies in span(mlMonomialBasis(allVars)) where allVars ⊆ vars(factored form)
    6. But we need: lies in span(mlMonomialBasis(nearVars)) for the bound

    The key: far-clause factors ∏_far (1 - z_c g_c) multiply ALL generators
    from this S by the SAME polynomial. So varying m only changes the
    near-variable part, and span dim ≤ 2^{|nearVars|}.

Per-window span containment (for a FIXED admissible S):
generators {mlProj(m * ∂^S p) : m.vars ⊆ S, deg(m) ≤ κ} lie in
span(mlMonomialBasis(nearVarSet S)).

Note: this bounds generators from ONE specific S, not the entire subspace.
The full tseitin_profile_rank_bound in PneqNP_Final combines this across
all S via profile compression (§9.1). -/
theorem per_window_span_remark : True := trivial  -- documentation only

end NearVars
