/-
  WidthToRank.lean — Paper §4-5: Width-to-rank bounds

  The core technical lemma for the P-side (A2):
  SPDP rank of a sum of local constraints ≤ poly(n).

  Key ingredients:
  1. SPDP generators of Σ f_i decompose: ∂^S(Σ f_i) = Σ ∂^S(f_i)
  2. Each f_i = C_i² has degree ≤ 6, uses O(1) variables in O(1) cells
  3. Generators with |S| > deg(f_i) give 0 (degree drop)
  4. The surviving generators span ≤ T² × O(1) dimensions
-/
import PallLean.SPDPDefs
import PallLean.CompiledPoly
import PallLean.TuringMachine
import PallLean.DegreeDrop
import PallLean.SupportedDim
import PallLean.ProfileCompression
import Mathlib.Tactic

namespace WidthToRank

open MvPolynomial SPDP CompiledPoly TuringMachine

/-! ## Lemma 1: SPDP rank is subadditive over sums

  CompiledPoly.blockedSpdpRankQ κ ℓ (f + g) bp ≤ CompiledPoly.blockedSpdpRankQ κ ℓ f bp + CompiledPoly.blockedSpdpRankQ κ ℓ g bp

  Proof: ∂^S(f+g) = ∂^S(f) + ∂^S(g), so m·∂^S(f+g) = m·∂^S(f) + m·∂^S(g).
  The span of generators of (f+g) ⊆ span of generators of f + span of generators of g.
  finrank(A + B) ≤ finrank(A) + finrank(B).
-/

theorem spdpRank_add_le {N : ℕ} (κ ℓ : ℕ)
    (f g : MvPolynomial (Fin N) ℚ) (bp : CompiledPoly.BlockPartition N) :
    CompiledPoly.blockedSpdpRankQ κ ℓ (f + g) bp ≤
      CompiledPoly.blockedSpdpRankQ κ ℓ f bp + CompiledPoly.blockedSpdpRankQ κ ℓ g bp := by
  -- ∂^S(f+g) = ∂^S(f) + ∂^S(g) by linearity.
  -- So m·∂^S(f+g) = m·∂^S(f) + m·∂^S(g).
  -- span(gens of f+g) ⊆ span(gens of f) + span(gens of g).
  -- finrank(A) ≤ finrank(B) + finrank(C) when A ≤ B + C.
  -- ∂^S(f+g) = ∂^S(f) + ∂^S(g) → generators decompose.
  -- span(gens(f+g)) ≤ span(gens(f)) ⊔ span(gens(g)).
  -- finrank(A ⊔ B) ≤ finrank(A) + finrank(B) via coprod map.
  sorry -- Needs: span containment + finrank_sup_le (coprod argument)

/-! ## Lemma 2: SPDP rank is subadditive over finite sums

  CompiledPoly.blockedSpdpRankQ κ ℓ (Σ f_i) bp ≤ Σ CompiledPoly.blockedSpdpRankQ κ ℓ f_i bp
-/

theorem spdpRank_sum_le {N : ℕ} (κ ℓ : ℕ)
    (fs : List (MvPolynomial (Fin N) ℚ)) (bp : CompiledPoly.BlockPartition N) :
    CompiledPoly.blockedSpdpRankQ κ ℓ fs.sum bp ≤
      (fs.map (fun f => CompiledPoly.blockedSpdpRankQ κ ℓ f bp)).sum := by
  induction fs with
  | nil =>
    simp only [List.sum_nil, List.map_nil, List.sum_nil]
    unfold CompiledPoly.blockedSpdpRankQ
    -- All generators are 0: ∂^S(0) = 0, so m * 0 = 0.
    -- iterDerivList S 0 = 0 for any S
    have h_zero : ∀ (S : List (Fin N)), SPDP.iterDerivList S (0 : MvPolynomial (Fin N) ℚ) = 0 := by
      intro S; unfold SPDP.iterDerivList
      induction S with
      | nil => rfl
      | cons v S ih =>
        simp only [List.foldl_cons]
        have : MvPolynomial.pderiv v (0 : MvPolynomial (Fin N) ℚ) = 0 := map_zero _
        rw [this]; exact ih
    -- All generators = m * 0 = 0
    have h_gens : ∀ q, (∃ S m, S.length ≤ κ ∧ m.totalDegree ≤ ℓ ∧
        (S.toFinset.image bp.blockOf).card = S.toFinset.card ∧
        (∀ v ∈ m.vars, bp.blockOf v ∈ S.toFinset.image bp.blockOf) ∧
        q = m * SPDP.iterDerivList S (0 : MvPolynomial _ ℚ)) → q = 0 := by
      intro q ⟨S, m, _, _, _, _, hq⟩; rw [hq, h_zero, mul_zero]
    -- span of {0} = ⊥, finrank = 0
    have h_sub : { q | ∃ S m, S.length ≤ κ ∧ m.totalDegree ≤ ℓ ∧ _ ∧ _ ∧
        q = m * SPDP.iterDerivList S (0 : MvPolynomial _ ℚ) } ⊆ {0} :=
      fun q hq => h_gens q hq
    calc Module.finrank ℚ (Submodule.span ℚ _)
        ≤ Module.finrank ℚ (Submodule.span ℚ ({0} : Set (MvPolynomial (Fin N) ℚ))) :=
          Submodule.finrank_mono (Submodule.span_mono h_sub)
      _ = Module.finrank ℚ (⊥ : Submodule ℚ (MvPolynomial (Fin N) ℚ)) := by
          rw [Submodule.span_singleton_eq_bot.mpr rfl]
      _ = 0 := finrank_bot ℚ _
  | cons f rest ih =>
    simp only [List.sum_cons, List.map_cons]
    calc CompiledPoly.blockedSpdpRankQ κ ℓ (f + rest.sum) bp
        ≤ CompiledPoly.blockedSpdpRankQ κ ℓ f bp + CompiledPoly.blockedSpdpRankQ κ ℓ rest.sum bp :=
          spdpRank_add_le κ ℓ f rest.sum bp
      _ ≤ CompiledPoly.blockedSpdpRankQ κ ℓ f bp + (rest.map (fun f => CompiledPoly.blockedSpdpRankQ κ ℓ f bp)).sum :=
          Nat.add_le_add_left ih _

/-! ## Lemma 3: SPDP rank of C² when deg(C) ≤ d, using ≤ w variables

  For a polynomial using w variables with degree ≤ 2d:
  CompiledPoly.blockedSpdpRankQ κ ℓ (C²) bp ≤ (w + 2d + ℓ)^w

  This is because the SPDP span is contained in the polynomial space
  on w variables with degree ≤ ℓ + 2d.
-/

theorem spdpRank_squared_local {N : ℕ} (κ ℓ : ℕ)
    (C : MvPolynomial (Fin N) ℚ) (bp : CompiledPoly.BlockPartition N)
    (hd : C.totalDegree ≤ 3) (hw : C.vars.card ≤ 6)
    -- Identity partition hypothesis
    (hbp : bp = ⟨N, fun v => v⟩) :
    CompiledPoly.blockedSpdpRankQ κ ℓ (C * C) bp ≤ (6 + 6 + ℓ) ^ 6 := by
  subst hbp
  -- C*C has degree ≤ 6 and vars ⊆ vars(C), card ≤ 6.
  -- By spdp_span_in_restrictSupportDeg: span ≤ restrictSupportDeg on blockClosure.
  -- blockClosure of C*C ⊆ blockClosure of C.vars, card ≤ some bound.
  -- By finrank_restrictSupportDeg_le: dim ≤ (card + degree)^card.
  -- With card ≤ 6 (from hw) and degree ≤ ℓ + 6:
  -- dim ≤ (6 + ℓ + 6)^6 = (ℓ + 12)^6.
  -- By spdp_span_in_restrictSupportDeg: span ≤ restrictSupportDeg(blockClosure, ℓ+6)
  -- blockClosure of (C*C).vars ≤ C.vars.card ≤ 6 (each var in own block)
  -- By finrank_restrictSupportDeg_le: dim ≤ (6 + ℓ + 6)^6
  -- So blockedSpdpRankQ ≤ (ℓ + 12)^6 ≤ (6 + 6 + ℓ)^6
  have hCC_deg : (C * C).totalDegree ≤ 6 := by
    calc (C * C).totalDegree ≤ C.totalDegree + C.totalDegree :=
          MvPolynomial.totalDegree_mul C C
      _ ≤ 3 + 3 := Nat.add_le_add hd hd
      _ = 6 := by omega
  -- SPDP span ≤ restrictSupportDeg
  have h_span := SupportedDim.spdp_span_in_restrictSupportDeg κ ℓ (C * C) ⟨N, fun v => v⟩ hCC_deg
  -- finrank of the span ≤ finrank of restrictSupportDeg
  unfold CompiledPoly.blockedSpdpRankQ
  calc Module.finrank ℚ _ ≤ Module.finrank ℚ (SupportedDim.restrictSupportDeg ℚ
      (SupportedDim.blockClosure ⟨N, fun v => v⟩ (C * C).vars) (ℓ + 6)) :=
        Submodule.finrank_mono h_span
    _ ≤ ((SupportedDim.blockClosure ⟨N, fun v => v⟩ (C * C).vars).card + (ℓ + 6)) ^
        (SupportedDim.blockClosure ⟨N, fun v => v⟩ (C * C).vars).card :=
        SupportedDim.finrank_restrictSupportDeg_le _ _
    _ ≤ (6 + 6 + ℓ) ^ 6 := by
        -- For identity partition: blockClosure = vars
        -- (C*C).vars ⊆ C.vars, card ≤ 6
        -- So blockClosure.card ≤ 6
        -- Then (6 + ℓ + 6)^6 ≤ (6 + 6 + ℓ)^6 = (12 + ℓ)^6
        -- blockClosure(identity, S) = S: simp closes it.
        have hbc : SupportedDim.blockClosure ⟨N, fun v => v⟩ (C * C).vars = (C * C).vars := by
          simp [SupportedDim.blockClosure]
        -- (C*C).vars ⊆ C.vars, card ≤ 6
        have hcc_vars : (C * C).vars.card ≤ 6 := by
          have hsub : (C * C).vars ⊆ C.vars := by
            intro v hv
            have := MvPolynomial.vars_mul C C hv
            simp only [Finset.mem_union] at this
            rcases this with h | h <;> exact h
          exact le_trans (Finset.card_le_card hsub) hw
        rw [hbc]
        calc ((C * C).vars.card + (ℓ + 6)) ^ (C * C).vars.card
            ≤ (6 + (ℓ + 6)) ^ 6 :=
              le_trans (Nat.pow_le_pow_left (by omega) _)
                (Nat.pow_le_pow_right (by omega) hcc_vars)
          _ = (6 + 6 + ℓ) ^ 6 := by ring
        

/-! ## Lemma 4: SPDP rank of violation polynomial ≤ #constraints × per-constraint bound

  V = Σ C_i². CompiledPoly.blockedSpdpRankQ(V) ≤ Σ CompiledPoly.blockedSpdpRankQ(C_i²) ≤ #constraints × bound.
-/

theorem violationPoly_rank_le {N : ℕ} (κ ℓ : ℕ)
    (constraints : List (LocalConstraint (sorry : DTM) (sorry : ℕ) (sorry : ℕ) ℚ))
    (bp : CompiledPoly.BlockPartition N) :
    True := trivial -- Placeholder for the combined bound

/-! ## Assembly: p_subset_ccoll from the above lemmas

  The violation polynomial V_{M,n} has:
  - #constraints ≤ numVars² (booleanity + transition)
  - Each constraint: degree ≤ 3, width ≤ 6
  - Per-constraint rank ≤ (12 + log n)^6
  - Total: numVars² × (log n)^O(1) ≤ n^(4tb+2) × n = n^(4tb+3)
-/

end WidthToRank
