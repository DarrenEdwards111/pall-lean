import PallLean.CompiledAssemblyRoadmap

/-!
# CompiledGeneratorTransportFrontier

This file isolates the exact next mathematical step in the compiled-side endgame:
prove generator-level transport from the compiled SPDP generators into the latent
SPDP generators. Once this is done, the elementwise transport target and the
reverse-transfer / fine-bound chain are already wired in `CompiledAssemblyRoadmap`.
-/

namespace CompiledGeneratorTransportFrontier

open CompiledAssemblyRoadmap
open LatentFullBridge LatentCompiler MultilinearSPDP NPWitness Compiler TuringMachine
open MvPolynomial

/-- Explicit frontier alias: the generator-level transport theorem is the exact
next proof-bearing obligation for the compiled-to-latent transfer route. -/
def generatorTransportFrontier
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ) : Prop :=
  ∀ (S : List (Fin (numVars M n (Nat.log 2 n))))
    (m : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ),
    S.length = Nat.log 2 n →
    m.totalDegree ≤ Nat.log 2 n →
    m.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible (compiledPartition M n) S →
    ∃ (S' : List (Fin (latentNumVars M n)))
      (m' : MvPolynomial (Fin (latentNumVars M n)) ℚ),
      S'.length = Nat.log 2 n ∧
      m'.totalDegree ≤ Nat.log 2 n ∧
      m'.vars ⊆ S'.toFinset ∧
      SPDP.isBlockAdmissible (latentPartition M n) S' ∧
      mlProj (m * SPDP.iterDerivList S (fullCompiledPoly ℚ M n h_le)) =
        T (mlProj (m' * SPDP.iterDerivList S' (latentCompiledPoly M n)))

/-- The roadmap target `compiled_generator_transport_target` is exactly this
frontier proposition. -/
theorem generatorTransportFrontier_iff_roadmap_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ) :
    generatorTransportFrontier M n h_le T ↔
      (∀ (S : List (Fin (numVars M n (Nat.log 2 n))))
        (m : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ),
        S.length = Nat.log 2 n →
        m.totalDegree ≤ Nat.log 2 n →
        m.vars ⊆ S.toFinset →
        SPDP.isBlockAdmissible (compiledPartition M n) S →
        ∃ (S' : List (Fin (latentNumVars M n)))
          (m' : MvPolynomial (Fin (latentNumVars M n)) ℚ),
          S'.length = Nat.log 2 n ∧
          m'.totalDegree ≤ Nat.log 2 n ∧
          m'.vars ⊆ S'.toFinset ∧
          SPDP.isBlockAdmissible (latentPartition M n) S' ∧
          mlProj (m * SPDP.iterDerivList S (fullCompiledPoly ℚ M n h_le)) =
            T (mlProj (m' * SPDP.iterDerivList S' (latentCompiledPoly M n)))) := by
  rfl

/-- Generator-level frontier for the violation branch, in the direction that
actually matches the bridge map `B.toLatent : compiled → latent`.

This is the natural analogue of `generatorTransportFrontier`, but specialized to
`violationPolyOf` and the renamed latent-side target polynomial that already
appears in the staged pipeline target. -/
def violationGeneratorTransportFrontier
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ) : Prop :=
  ∀ (S : List (Fin (numVars M n (Nat.log 2 n))))
    (m : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ),
    S.length = Nat.log 2 n →
    m.totalDegree ≤ Nat.log 2 n →
    m.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible (compiledPartition M n) S →
    ∃ (S' : List (Fin (latentNumVars M n)))
      (m' : MvPolynomial (Fin (latentNumVars M n)) ℚ),
      S'.length = Nat.log 2 n ∧
      m'.totalDegree ≤ Nat.log 2 n ∧
      m'.vars ⊆ S'.toFinset ∧
      SPDP.isBlockAdmissible (latentPartition M n) S' ∧
      mlProj (m * SPDP.iterDerivList S (violationPolyOf ℚ M n)) =
        T (mlProj (m' * SPDP.iterDerivList S' (MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n))))

/-- Subspace-level violation frontier in the same direction. This is the honest
missing statement behind the staged violation target in
`CompiledGeneratorPipeline`. -/
def violationBranchTransportFrontier
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ) : Prop :=
  mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (violationPolyOf ℚ M n)
    ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n)))

/-- The generator-level violation frontier is exactly the elementwise generator
transport statement one would use to derive the subspace-level frontier by the
same span-lift pattern as elsewhere in the file family. -/
theorem violationGeneratorTransportFrontier_iff_generator_target
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ) :
    violationGeneratorTransportFrontier M n B T ↔
      (∀ (S : List (Fin (numVars M n (Nat.log 2 n))))
        (m : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ),
        S.length = Nat.log 2 n →
        m.totalDegree ≤ Nat.log 2 n →
        m.vars ⊆ S.toFinset →
        SPDP.isBlockAdmissible (compiledPartition M n) S →
        ∃ (S' : List (Fin (latentNumVars M n)))
          (m' : MvPolynomial (Fin (latentNumVars M n)) ℚ),
          S'.length = Nat.log 2 n ∧
          m'.totalDegree ≤ Nat.log 2 n ∧
          m'.vars ⊆ S'.toFinset ∧
          SPDP.isBlockAdmissible (latentPartition M n) S' ∧
          mlProj (m * SPDP.iterDerivList S (violationPolyOf ℚ M n)) =
            T (mlProj (m' * SPDP.iterDerivList S' (MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n))))) := by
  rfl

/-- Semantic generator-level package for the violation branch. This is now the
single explicit remaining proof obligation on the violation side. -/
def ViolationGeneratorSemanticTransport
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ) : Prop :=
  (∀ i : Fin (numVars M n (Nat.log 2 n)),
    (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i)) ∧
  ∀ (S : List (Fin (numVars M n (Nat.log 2 n))))
    (m : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ),
    S.length = Nat.log 2 n →
    m.totalDegree ≤ Nat.log 2 n →
    m.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible (compiledPartition M n) S →
    ∃ (S' : List (Fin (latentNumVars M n)))
      (m' : MvPolynomial (Fin (latentNumVars M n)) ℚ),
      S'.length = Nat.log 2 n ∧
      m'.totalDegree ≤ Nat.log 2 n ∧
      m'.vars ⊆ S'.toFinset ∧
      SPDP.isBlockAdmissible (latentPartition M n) S' ∧
      mlProj (m * SPDP.iterDerivList S (violationPolyOf ℚ M n)) =
        T (mlProj (m' * SPDP.iterDerivList S' (MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n))))

/-- Compiled-witness reformulation of the semantic violation transport: instead
of asking directly for a latent witness polynomial, package a compiled witness
whose image under `mapFullToLatentPoly` supplies the latent-side generator.

This matches the orientation of concrete reconstruction facts such as
`restrictPoly_mapFullToLatentPoly`, which naturally start from compiled inputs. -/
def ViolationGeneratorSemanticTransportCompiledWitness
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ) : Prop :=
  (∀ i : Fin (numVars M n (Nat.log 2 n)),
    (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i)) ∧
  ∀ (S : List (Fin (numVars M n (Nat.log 2 n))))
    (m : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ),
    S.length = Nat.log 2 n →
    m.totalDegree ≤ Nat.log 2 n →
    m.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible (compiledPartition M n) S →
    ∃ mc : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ,
      mc.totalDegree ≤ Nat.log 2 n ∧
      mc.vars ⊆ S.toFinset ∧
      mlProj (m * SPDP.iterDerivList S (violationPolyOf ℚ M n)) =
        T (mlProj ((mapFullToLatentPoly M n B mc) *
          SPDP.iterDerivList (S.map B.toLatent)
            (MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n))))

/-- The compiled-witness semantic package implies the original latent-witness
formulation by choosing the mapped witness list and polynomial. -/
private theorem map_filter_length_eq_filter_length
    {α β : Type*} (f : α → β) (p : β → Bool) :
    ∀ S : List α,
      ((S.map f).filter p).length = (S.filter (fun a => p (f a))).length := by
  intro S
  induction S with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.filter_cons]
    by_cases h : p (f a)
    · simp [h, ih]
    · simp [h, ih]

private theorem filter_length_eq_of_pointwise
    {α : Type*} (p q : α → Bool)
    (hpoint : ∀ a, p a = q a) :
    ∀ S : List α, (S.filter p).length = (S.filter q).length := by
  intro S
  induction S with
  | nil => simp
  | cons a rest ih =>
    simp only [List.filter_cons]
    rw [hpoint a]
    split <;> simp [ih]

theorem violationGeneratorTransportFrontier_of_compiledWitnessSemantic
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hSem : ViolationGeneratorSemanticTransportCompiledWitness M n B T) :
    violationGeneratorTransportFrontier M n B T := by
  intro S m hLen hdeg hvars hadm
  rcases hSem.2 S m hLen hdeg hvars hadm with ⟨mc, hdegc, hvarsc, hEq⟩
  refine ⟨S.map B.toLatent, mapFullToLatentPoly M n B mc, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hLen
  · exact le_trans (MvPolynomial.totalDegree_rename_le B.toLatent mc) hdegc
  ·
    show (mapFullToLatentPoly M n B mc).vars ⊆ (S.map B.toLatent).toFinset
    simpa [mapFullToLatentPoly] using
      (show (MvPolynomial.rename B.toLatent mc).vars ⊆ (S.map B.toLatent).toFinset from by
        intro i hi
        have hsub := MvPolynomial.vars_rename B.toLatent mc
        rcases Finset.mem_image.mp (hsub hi) with ⟨j, hj, rfl⟩
        exact Finset.mem_coe.mpr <| List.mem_toFinset.mpr <| List.mem_map.mpr ⟨j, List.mem_toFinset.mp (hvarsc hj), rfl⟩)
  ·
    constructor
    · exact List.Nodup.map B.inj hadm.1
    · intro b
      have hpoint :
          ∀ i : Fin (numVars M n (Nat.log 2 n)),
            decide ((latentPartition M n).assign (B.toLatent i) = b) =
              decide ((compiledPartition M n).assign i = b) := by
        intro i
        by_cases h : (latentPartition M n).assign (B.toLatent i) = b
        · have hc : (compiledPartition M n).assign i = b := by
            calc
              (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i) := hSem.1 i
              _ = b := h
          simp [h, hc]
        · have hc : ¬ (compiledPartition M n).assign i = b := by
            intro hc
            apply h
            calc
              (latentPartition M n).assign (B.toLatent i) = (compiledPartition M n).assign i := (hSem.1 i).symm
              _ = b := hc
          simp [h, hc]
      calc
        ((S.map B.toLatent).filter (fun j => decide ((latentPartition M n).assign j = b))).length
            = (S.filter (fun i => decide ((latentPartition M n).assign (B.toLatent i) = b))).length :=
              map_filter_length_eq_filter_length B.toLatent
                (fun j => decide ((latentPartition M n).assign j = b)) S
        _ = (S.filter (fun i => decide ((compiledPartition M n).assign i = b))).length :=
              filter_length_eq_of_pointwise
                (fun i => decide ((latentPartition M n).assign (B.toLatent i) = b))
                (fun i => decide ((compiledPartition M n).assign i = b))
                hpoint S
        _ ≤ 1 := hadm.2 b
  · simpa [mapFullToLatentPoly] using hEq

/-- The semantic violation theorem is exactly the generator frontier. -/
theorem violationGeneratorTransportFrontier_of_semantic
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hSem : ViolationGeneratorSemanticTransport M n B T) :
    violationGeneratorTransportFrontier M n B T :=
  hSem.2

/-- The staged violation target in `CompiledGeneratorPipeline` is exactly this
frontier proposition. Keeping it named here makes the remaining obstruction
explicit without pretending the proof already exists. -/
theorem violationBranchTransportFrontier_iff_pipeline_target
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ) :
    violationBranchTransportFrontier M n B T ↔
      mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (violationPolyOf ℚ M n)
      ≤ Submodule.map T
          (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
            (MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n))) := by
  rfl

/-- Span-lift for the violation branch: once each compiled SPDP generator for
`violationPolyOf` transports into a latent SPDP generator after renaming by the
bridge, the full violation subspace transport follows. This reduces the
remaining violation gap to the generator-level frontier only. -/
theorem violationBranchTransportFrontier_of_generatorFrontier
    (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hGen : violationGeneratorTransportFrontier M n B T) :
    violationBranchTransportFrontier M n B T := by
  rw [violationBranchTransportFrontier, mlBlockedSpdpSubspace, Submodule.span_le]
  intro q hq
  obtain ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩ := hq
  rcases hGen S m hlen hdeg hvars hadm with ⟨S', m', hlen', hdeg', hvars', hadm', hEq⟩
  have hGen' :
      mlProj (m' * SPDP.iterDerivList S' (MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n))) ∈
        mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n)) :=
    Submodule.subset_span ⟨S', m', hlen', hdeg', hvars', hadm', rfl⟩
  refine ⟨mlProj (m' * SPDP.iterDerivList S' (MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n))), hGen', ?_⟩
  exact hEq.symm

/-- One-line handoff: once generator transport is proved, the roadmap's exact
minimal elementwise transport target is immediately available. -/
theorem compiled_subspace_element_transport_of_generator_frontier
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hGen : generatorTransportFrontier M n h_le T) :
    ∀ q : MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ,
      q ∈ mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
            (fullCompiledPoly ℚ M n h_le) →
      ∃ r : MvPolynomial (Fin (latentNumVars M n)) ℚ,
        r ∈ mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
              (latentCompiledPoly M n)
          ∧ q = T r :=
  compiled_subspace_element_transport_target M n h_le T hGen

end CompiledGeneratorTransportFrontier
