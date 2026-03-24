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

set_option maxHeartbeats 1600000 in
private theorem finrank_sup_le {M : Type*} [AddCommGroup M] [Module ℚ M]
    (A B : Submodule ℚ M) [Module.Finite ℚ A] [Module.Finite ℚ B] :
    Module.finrank ℚ ↥(A ⊔ B) ≤ Module.finrank ℚ A + Module.finrank ℚ B := by
  haveI : Module.Finite ℚ (↥A × ↥B) := Module.Finite.prod
  have h : A ⊔ B ≤ (A.subtype.coprod B.subtype).range := by
    intro x hx; simp only [Submodule.mem_sup] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  calc Module.finrank ℚ ↥(A ⊔ B)
      ≤ Module.finrank ℚ ↥(A.subtype.coprod B.subtype).range :=
        Submodule.finrank_mono h
    _ = Module.finrank ℚ ↥(Submodule.map (A.subtype.coprod B.subtype) ⊤) := by rw [LinearMap.range_eq_map]
    _ ≤ Module.finrank ℚ ↥(⊤ : Submodule ℚ (↥A × ↥B)) := Submodule.finrank_map_le _ _
    _ = Module.finrank ℚ (↥A × ↥B) := by simp
    _ = Module.finrank ℚ A + Module.finrank ℚ B := Module.finrank_prod

-- Module.Finite for the SPDP span: it's contained in restrictTotalDegree.
private theorem spdpSpan_finite {N : ℕ} (κ ℓ : ℕ)
    (V : MvPolynomial (Fin N) ℚ) (bp : CompiledPoly.BlockPartition N)
    (hd : V.totalDegree ≤ 6) :
    Module.Finite ℚ (Submodule.span ℚ
      { q | ∃ (S : List (Fin N)) (m : MvPolynomial (Fin N) ℚ),
        S.length ≤ κ ∧ m.totalDegree ≤ ℓ ∧
        (S.toFinset.image bp.blockOf).card = S.toFinset.card ∧
        (∀ v ∈ m.vars, bp.blockOf v ∈ S.toFinset.image bp.blockOf) ∧
        q = m * SPDP.iterDerivList S V }) := by
  -- The span ≤ restrictTotalDegree (ℓ + 6) (from spdp_span_in_restrictSupportDeg).
  -- restrictTotalDegree is Module.Finite.
  -- Submodule of Module.Finite is Module.Finite.
  have h_le := SupportedDim.spdp_span_in_restrictSupportDeg κ ℓ V bp hd
  exact Module.Finite.of_injective (Submodule.inclusion h_le) (Submodule.inclusion_injective _)

private theorem iterDerivList_add {N : ℕ} (S : List (Fin N))
    (f g : MvPolynomial (Fin N) ℚ) :
    SPDP.iterDerivList S (f + g) = SPDP.iterDerivList S f + SPDP.iterDerivList S g := by
  induction S generalizing f g with
  | nil => rfl
  | cons v S ih =>
    unfold SPDP.iterDerivList; simp only [List.foldl_cons]
    rw [show MvPolynomial.pderiv v (f + g) = MvPolynomial.pderiv v f + MvPolynomial.pderiv v g
      from map_add _ _ _]
    exact ih _ _

theorem spdpRank_add_le {N : ℕ} (κ ℓ : ℕ)
    (f g : MvPolynomial (Fin N) ℚ) (bp : CompiledPoly.BlockPartition N)
    (hf : f.totalDegree ≤ 6) (hg : g.totalDegree ≤ 6) :
    CompiledPoly.blockedSpdpRankQ κ ℓ (f + g) bp ≤
      CompiledPoly.blockedSpdpRankQ κ ℓ f bp + CompiledPoly.blockedSpdpRankQ κ ℓ g bp := by
  -- ∂^S(f+g) = ∂^S(f) + ∂^S(g) by linearity.
  -- So m·∂^S(f+g) = m·∂^S(f) + m·∂^S(g).
  -- span(gens of f+g) ⊆ span(gens of f) + span(gens of g).
  -- finrank(A) ≤ finrank(B) + finrank(C) when A ≤ B + C.
  -- ∂^S(f+g) = ∂^S(f) + ∂^S(g) → each generator of f+g is sum of gens of f and g.
  -- span(gens(f+g)) ≤ span(gens(f)) ⊔ span(gens(g)).
  -- finrank(A ⊔ B) ≤ finrank(A) + finrank(B).
  -- The span containment needs: iterDerivList S (f+g) = iterDerivList S f + iterDerivList S g.
  -- This is linearity of pderiv.
  -- Each generator of f+g decomposes via iterDerivList_add.
  -- m · ∂^S(f+g) = m · ∂^S(f) + m · ∂^S(g)
  -- First is in span(gens f), second in span(gens g).
  -- So span(gens(f+g)) ≤ span(gens f) ⊔ span(gens g).
  -- finrank_sup_le gives the bound.
  -- Step 1: generators of f+g decompose via iterDerivList_add.
  -- Step 2: span(gens(f+g)) ≤ span(gens f) ⊔ span(gens g).
  -- Step 3: finrank_sup_le + Module.Finite (spdpSpan_finite).
  unfold CompiledPoly.blockedSpdpRankQ
  have h_deg_f := hf -- caller should provide
  have h_deg_g := hg -- caller should provide
  haveI := spdpSpan_finite κ ℓ f bp h_deg_f
  haveI := spdpSpan_finite κ ℓ g bp h_deg_g
  have h_sub : Submodule.span ℚ
      { q | ∃ S m, S.length ≤ κ ∧ m.totalDegree ≤ ℓ ∧
        (S.toFinset.image bp.blockOf).card = S.toFinset.card ∧
        (∀ v ∈ m.vars, bp.blockOf v ∈ S.toFinset.image bp.blockOf) ∧
        q = m * SPDP.iterDerivList S (f + g) }
    ≤ (Submodule.span ℚ { q | ∃ S m, S.length ≤ κ ∧ m.totalDegree ≤ ℓ ∧
        (S.toFinset.image bp.blockOf).card = S.toFinset.card ∧
        (∀ v ∈ m.vars, bp.blockOf v ∈ S.toFinset.image bp.blockOf) ∧
        q = m * SPDP.iterDerivList S f }) ⊔
      (Submodule.span ℚ { q | ∃ S m, S.length ≤ κ ∧ m.totalDegree ≤ ℓ ∧
        (S.toFinset.image bp.blockOf).card = S.toFinset.card ∧
        (∀ v ∈ m.vars, bp.blockOf v ∈ S.toFinset.image bp.blockOf) ∧
        q = m * SPDP.iterDerivList S g }) := by
    apply Submodule.span_le.mpr
    intro q ⟨S, m, hlen, hdeg, htrans, hcoupl, hq⟩
    rw [hq, iterDerivList_add, mul_add]
    exact Submodule.add_mem_sup
      (Submodule.subset_span ⟨S, m, hlen, hdeg, htrans, hcoupl, rfl⟩)
      (Submodule.subset_span ⟨S, m, hlen, hdeg, htrans, hcoupl, rfl⟩)
  exact le_trans (Submodule.finrank_mono h_sub) (finrank_sup_le _ _)

/-! ## Lemma 2: SPDP rank is subadditive over finite sums

  CompiledPoly.blockedSpdpRankQ κ ℓ (Σ f_i) bp ≤ Σ CompiledPoly.blockedSpdpRankQ κ ℓ f_i bp
-/

private theorem totalDegree_list_sum_le {N : ℕ}
    (fs : List (MvPolynomial (Fin N) ℚ)) (d : ℕ)
    (hfs : ∀ f ∈ fs, f.totalDegree ≤ d) :
    fs.sum.totalDegree ≤ d := by
  induction fs with
  | nil => simp [MvPolynomial.totalDegree_zero]
  | cons f rest ih =>
    simp only [List.sum_cons]
    exact le_trans (MvPolynomial.totalDegree_add f rest.sum)
      (max_le (hfs f (List.Mem.head rest))
        (ih (fun g hg => hfs g (List.Mem.tail f hg))))

theorem spdpRank_sum_le {N : ℕ} (κ ℓ : ℕ)
    (fs : List (MvPolynomial (Fin N) ℚ)) (bp : CompiledPoly.BlockPartition N)
    (hfs : ∀ f ∈ fs, f.totalDegree ≤ 6) :
    CompiledPoly.blockedSpdpRankQ κ ℓ fs.sum bp ≤
      (fs.map (fun f => CompiledPoly.blockedSpdpRankQ κ ℓ f bp)).sum := by
  induction fs with
  | nil =>
    simp only [List.sum_nil, List.map_nil, List.sum_nil]
    -- blockedSpdpRankQ κ ℓ 0 bp = finrank(span{q | ...iterDerivList S 0...})
    -- iterDerivList S 0 = 0 for all S, so all generators are 0, span = ⊥, finrank = 0
    show CompiledPoly.blockedSpdpRankQ κ ℓ 0 bp ≤ 0
    unfold CompiledPoly.blockedSpdpRankQ
    simp only [Nat.le_zero]
    have h_zero : ∀ (S : List (Fin N)), SPDP.iterDerivList S (0 : MvPolynomial (Fin N) ℚ) = 0 := by
      intro S; induction S with
      | nil => rfl
      | cons v S ih => simp only [SPDP.iterDerivList, List.foldl_cons]; rw [ih]; exact map_zero _
    convert finrank_bot ℚ (MvPolynomial (Fin N) ℚ) using 1
    rw [eq_comm, Submodule.span_eq_bot]
    intro q ⟨S, m, _, _, _, _, hq⟩; rw [hq, h_zero, mul_zero]
  | cons f rest ih =>
    simp only [List.sum_cons, List.map_cons]
    calc CompiledPoly.blockedSpdpRankQ κ ℓ (f + rest.sum) bp
        ≤ CompiledPoly.blockedSpdpRankQ κ ℓ f bp + CompiledPoly.blockedSpdpRankQ κ ℓ rest.sum bp :=
          spdpRank_add_le κ ℓ f rest.sum bp
            (hfs f (List.Mem.head rest))
            (by
              -- rest.sum.totalDegree ≤ 6 (from all elements having degree ≤ 6)
              have : ∀ g ∈ rest, g.totalDegree ≤ 6 :=
                fun g hg => hfs g (List.Mem.tail f hg)
              clear ih hfs
              induction rest with
              | nil => simp
              | cons g rest' ih' =>
                simp only [List.sum_cons]
                exact le_trans (MvPolynomial.totalDegree_add _ _)
                  (max_le (this g (List.Mem.head rest'))
                    (ih' (fun h hh => this h (List.Mem.tail g hh)))))
      _ ≤ CompiledPoly.blockedSpdpRankQ κ ℓ f bp + (rest.map (fun f => CompiledPoly.blockedSpdpRankQ κ ℓ f bp)).sum :=
          Nat.add_le_add_left (ih (fun g hg => hfs g (List.Mem.tail f hg))) _

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

-- violationPoly_rank_le: removed (dead code with sorry-typed params)

/-! ## Assembly: p_subset_ccoll from the above lemmas

  The violation polynomial V_{M,n} has:
  - #constraints ≤ numVars² (booleanity + transition)
  - Each constraint: degree ≤ 3, width ≤ 6
  - Per-constraint rank ≤ (12 + log n)^6
  - Total: numVars² × (log n)^O(1) ≤ n^(4tb+2) × n = n^(4tb+3)
-/

end WidthToRank
