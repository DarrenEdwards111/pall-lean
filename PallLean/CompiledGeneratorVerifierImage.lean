import PallLean.CompiledGeneratorVerifierZero

/-!
# CompiledGeneratorVerifierImage

Verifier-side control for the complementary case: when the derivative list lies
entirely inside the witness image, the verifier contribution is itself the rename
of a Tseitin-side SPDP generator.
-/

namespace CompiledGeneratorTransportFrontier

open CompiledAssemblyRoadmap
open LatentFullBridge LatentCompiler MultilinearSPDP NPWitness Compiler TuringMachine
open MvPolynomial SPDP

private lemma preimage_list_public {n m : ℕ}
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (S : List (Fin m)) (hS : ∀ v ∈ S, v ∈ Set.range f) :
    ∃ S' : List (Fin n), S'.map f = S := by
  induction S with
  | nil => exact ⟨[], rfl⟩
  | cons a rest ih =>
    have ha : a ∈ Set.range f := hS a (by simp)
    obtain ⟨i, rfl⟩ := ha
    have ih' := ih (fun v hv => hS v (by simp [hv]))
    obtain ⟨rest', hrest'⟩ := ih'
    exact ⟨i :: rest', by rw [List.map_cons, hrest']⟩

private lemma rename_restrictPoly_of_vars_range_public {n m : ℕ} {F : Type*} [CommRing F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (mult : MvPolynomial (Fin m) F) (h : ↑mult.vars ⊆ Set.range f) :
    MvPolynomial.rename f (restrictPoly F f hf mult) = mult := by
  have heq : ((MvPolynomial.rename f).comp (restrictPoly F f hf)) =
      MvPolynomial.aeval (fun j => if (j ∈ Set.range f) then MvPolynomial.X j else (0 : MvPolynomial (Fin m) F)) := by
    ext j
    simp only [AlgHom.comp_apply, restrictPoly_X, MvPolynomial.aeval_X]
    by_cases hj : ∃ i, f i = j
    · rw [dif_pos hj, MvPolynomial.rename_X, if_pos ⟨hj.choose, hj.choose_spec⟩]
      simp [hj.choose_spec]
    · rw [dif_neg hj, map_zero]
      rw [if_neg]
      intro ⟨i, hi⟩
      exact hj ⟨i, hi⟩
  rw [show MvPolynomial.rename f (restrictPoly F f hf mult) =
    ((MvPolynomial.rename f).comp (restrictPoly F f hf)) mult from rfl, heq]
  exact MvPolynomial.aeval_ite_mem_eq_self mult h

private lemma isBlockAdmissible_pullback_public {n m : ℕ}
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (B : BlockPartition m) (S' : List (Fin n))
    (hadm : isBlockAdmissible B (S'.map f)) :
    isBlockAdmissible (pullbackPartition B f) S' := by
  constructor
  · exact ((List.nodup_map_iff hf).mp (And.left hadm))
  · intro b
    have hlen : ∀ (L : List (Fin n)), ((L.map f).filter (fun j => B.assign j = b)).length =
        (L.filter (fun i => B.assign (f i) = b)).length := by
      intro L
      induction L with
      | nil => simp
      | cons a rest ih =>
        simp only [List.map_cons, List.filter_cons]
        by_cases h : B.assign (f a) = b <;> simp [h, ih]
    have hS' : (S'.filter (fun i => B.assign (f i) = b)).length ≤ 1 := by
      rw [← hlen S']
      exact hadm.2 b
    simpa [pullbackPartition] using hS'

private lemma restrictPoly_vars_subset_public {n m : ℕ} {F : Type*} [CommRing F]
    (f : Fin n → Fin m) (hf : Function.Injective f)
    (mult : MvPolynomial (Fin m) F) (S' : List (Fin n))
    (hvars : mult.vars ⊆ (S'.map f).toFinset) :
    (restrictPoly F f hf mult).vars ⊆ S'.toFinset := by
  intro i hi
  have h_range : ↑mult.vars ⊆ Set.range f := by
    intro v hv
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp (hvars (Finset.mem_coe.mpr hv)))
    exact ⟨j, rfl⟩
  have h_eq := rename_restrictPoly_of_vars_range_public f hf mult h_range
  have h_fi_mem : f i ∈ mult.vars := by
    rw [← h_eq]
    rw [MvPolynomial.mem_vars] at hi ⊢
    obtain ⟨d, hd_supp, hd_i⟩ := hi
    refine ⟨Finsupp.mapDomain f d, ?_, ?_⟩
    · rw [MvPolynomial.mem_support_iff]
      rw [show MvPolynomial.coeff (Finsupp.mapDomain f d) (MvPolynomial.rename f (restrictPoly F f hf mult)) =
        MvPolynomial.coeff d (restrictPoly F f hf mult) from
        MvPolynomial.coeff_rename_mapDomain f hf _ d]
      rwa [← MvPolynomial.mem_support_iff]
    · rw [Finsupp.mem_support_iff]
      rw [Finsupp.mapDomain_apply hf]
      rwa [← Finsupp.mem_support_iff]
  have h_fi_S := hvars h_fi_mem
  rw [List.mem_toFinset, List.mem_map] at h_fi_S
  obtain ⟨j, hj_mem, hj_eq⟩ := h_fi_S
  rw [List.mem_toFinset]
  exact hf hj_eq ▸ hj_mem

/-- Inside the witness image, a verifier contribution is exactly the rename of a
Tseitin-side SPDP generator, with pulled-back derivative list and multiplier. -/
theorem compiled_generator_verifier_transport_of_inside_witness_range
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (S : List (Fin (numVars M n (Nat.log 2 n))))
    (m : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hlen : S.length = Nat.log 2 n)
    (hdeg : m.totalDegree ≤ Nat.log 2 n)
    (hvars : m.vars ⊆ S.toFinset)
    (hadm : SPDP.isBlockAdmissible (compiledPartition M n) S)
    (hS : ∀ v ∈ S, v ∈ Set.range (witnessInclusion M n h_le)) :
    ∃ (S' : List (Fin (npNumVars n)))
      (m' : MvPolynomial (Fin (npNumVars n)) ℚ),
      S'.length = Nat.log 2 n ∧
      m'.totalDegree ≤ Nat.log 2 n ∧
      m'.vars ⊆ S'.toFinset ∧
      SPDP.isBlockAdmissible (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le)) S' ∧
      mlProj (m * SPDP.iterDerivList S (verifierSheetOf ℚ M n h_le)) =
        MvPolynomial.rename (witnessInclusion M n h_le)
          (mlProj (m' * SPDP.iterDerivList S' (tseitinPoly ℚ n))) := by
  have hf := witnessInclusion_injective M n h_le
  obtain ⟨S', hS'⟩ := preimage_list_public (witnessInclusion M n h_le) hf S hS
  let m' := restrictPoly ℚ (witnessInclusion M n h_le) hf m
  refine ⟨S', m', ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hS', List.length_map] at hlen
    exact hlen
  · exact le_trans (restrictPoly_totalDegree_le ℚ (witnessInclusion M n h_le) hf m) hdeg
  · rw [show m' = restrictPoly ℚ (witnessInclusion M n h_le) hf m from rfl]
    exact restrictPoly_vars_subset_public (witnessInclusion M n h_le) hf m S' (by simpa [hS'] using hvars)
  · rw [← hS'] at hadm
    exact isBlockAdmissible_pullback_public (witnessInclusion M n h_le) hf (compiledPartition M n) S' hadm
  · unfold verifierSheetOf
    have h_iter : iterDerivList S (MvPolynomial.rename (witnessInclusion M n h_le) (tseitinPoly ℚ n)) =
        MvPolynomial.rename (witnessInclusion M n h_le) (iterDerivList S' (tseitinPoly ℚ n)) := by
      rw [← hS', iterDerivList_rename (witnessInclusion M n h_le) hf S' (tseitinPoly ℚ n)]
    have h_range : ↑m.vars ⊆ Set.range (witnessInclusion M n h_le) := by
      intro v hv
      exact hS v (List.mem_toFinset.mp (hvars (Finset.mem_coe.mpr hv)))
    have h_mult : MvPolynomial.rename (witnessInclusion M n h_le) m' = m := by
      dsimp [m']
      exact rename_restrictPoly_of_vars_range_public (witnessInclusion M n h_le) hf m h_range
    rw [h_iter, ← h_mult, ← map_mul (MvPolynomial.rename (witnessInclusion M n h_le)), mlProj_rename (witnessInclusion M n h_le) hf]

/-- Packaging lemma: every verifier-side compiled generator lies in the sum of
`⊥` and the rename-image of the Tseitin-side SPDP subspace over the pullback
partition. The proof is exactly the case split on whether `S` is fully inside
witness-image. -/
theorem compiled_generator_verifier_mem_bot_sup_rename_tseitin
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (S : List (Fin (numVars M n (Nat.log 2 n))))
    (m : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hlen : S.length = Nat.log 2 n)
    (hdeg : m.totalDegree ≤ Nat.log 2 n)
    (hvars : m.vars ⊆ S.toFinset)
    (hadm : SPDP.isBlockAdmissible (compiledPartition M n) S) :
    mlProj (m * SPDP.iterDerivList S (verifierSheetOf ℚ M n h_le)) ∈
      (⊥ : Submodule ℚ (MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)) ⊔
      Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
        (mlBlockedSpdpSubspace
          (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
          (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n)) := by
  classical
  by_cases hS : ∀ v ∈ S, v ∈ Set.range (witnessInclusion M n h_le)
  · rcases compiled_generator_verifier_transport_of_inside_witness_range
      M n h_le S m hlen hdeg hvars hadm hS with
      ⟨S', m', hlen', hdeg', hvars', hadm', hEq⟩
    have hGen :
        mlProj (m' * SPDP.iterDerivList S' (tseitinPoly ℚ n)) ∈
          mlBlockedSpdpSubspace
            (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
            (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n) :=
      Submodule.subset_span ⟨S', m', hlen', hdeg', hvars', hadm', rfl⟩
    have hMap :
        mlProj (m * SPDP.iterDerivList S (verifierSheetOf ℚ M n h_le)) ∈
          Submodule.map (MvPolynomial.rename (witnessInclusion M n h_le)).toLinearMap
            (mlBlockedSpdpSubspace
              (pullbackPartition (compiledPartition M n) (witnessInclusion M n h_le))
              (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly ℚ n)) := by
      refine ⟨mlProj (m' * SPDP.iterDerivList S' (tseitinPoly ℚ n)), hGen, ?_⟩
      simpa [hEq] using rfl
    exact Submodule.mem_sup_right hMap
  · push_neg at hS
    have hZero :
        mlProj (m * SPDP.iterDerivList S (verifierSheetOf ℚ M n h_le)) = 0 :=
      compiled_generator_verifier_zero_of_outside_witness_range M n h_le S m hS
    have hBot :
        mlProj (m * SPDP.iterDerivList S (verifierSheetOf ℚ M n h_le)) ∈
          (⊥ : Submodule ℚ (MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)) := by
      rw [hZero]
      exact Submodule.zero_mem _
    exact Submodule.mem_sup_left hBot

end CompiledGeneratorTransportFrontier
