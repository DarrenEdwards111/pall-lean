import PallLean.LatentCompiler
import PallLean.MultilinearSPDP
import Mathlib.Tactic

/-!
# LatentFullBridge

Typed interface layer between the paper `fullCompiledPoly` route
(`numVars` universe, `compiledPartition`) and the latent route
(`latentNumVars` universe, `latentPartition`).

This file intentionally starts as an interface skeleton: it records the exact
map/transport obligations needed for the final rank-transfer proof, without
pretending those obligations are already discharged.
-/

namespace LatentFullBridge

open LatentCompiler MultilinearSPDP NPWitness Compiler TuringMachine
open MvPolynomial

/-- Interface witness for transporting full-compiled objects into the latent
variable universe. `toLatent` is the index map used by renaming/restriction. -/
structure FullToLatentBridge (M : DTM) (n : ℕ) where
  toLatent : Fin (numVars M n (Nat.log 2 n)) → Fin (latentNumVars M n)
  inj : Function.Injective toLatent

/-- Canonical bridge object from a variable-count inequality.

This discharges the existence part of the embedding assumption whenever we can
prove `numVars ≤ latentNumVars` for the instance. -/
noncomputable def fullToLatentBridgeOfLe (M : DTM) (n : ℕ)
    (hLe : numVars M n (Nat.log 2 n) ≤ latentNumVars M n) :
    FullToLatentBridge M n where
  toLatent := Fin.castLEEmb hLe
  inj := (Fin.castLEEmb hLe).inj'

/-- Step-1 global constructor: if compiler semantics provides a global variable-count
inequality `numVars ≤ latentNumVars`, we get a concrete bridge object for every
instance. -/
noncomputable def globalFullToLatentBridgeOfGlobalLe
    (hLe : ∀ (M : DTM) (n : ℕ),
      numVars M n (Nat.log 2 n) ≤ latentNumVars M n) :
    ∀ (M : DTM) (n : ℕ), FullToLatentBridge M n :=
  fun M n => fullToLatentBridgeOfLe M n (hLe M n)

/-- Step-1 semantic fact: latent variable universe is a 4x expansion of the base
compiler variable universe, hence the canonical inequality needed by bridge
construction holds globally. -/
theorem global_numVars_le_latentNumVars :
    ∀ (M : DTM) (n : ℕ),
      numVars M n (Nat.log 2 n) ≤ latentNumVars M n := by
  intro M n
  unfold latentNumVars latentBaseVars
  omega

/-- Step-1 witness packaging (assumption-driven): if NP witness-variable count is
bounded by the tape-square core term, then the exact downstream `hLeWitness`
shape follows immediately. -/
theorem global_hLeWitness_of_npNumVars_le_tapeSquare
    (hNP : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      npNumVars n ≤ (n ^ M.timeBound + 1) ^ 2) :
    ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      npNumVars n ≤ numVars M n (Nat.log 2 n) := by
  intro M n hn hn804
  have hcore : (n ^ M.timeBound + 1) ^ 2 ≤ numVars M n (Nat.log 2 n) := by
    unfold numVars tapeSize timeSteps
    set S : ℕ := n ^ M.timeBound + 1
    have hadd : S * S ≤ S * S + (S * M.numStates + S * S + n + Nat.log 2 n) :=
      Nat.le_add_right (S * S) (S * M.numStates + S * S + n + Nat.log 2 n)
    simpa [S, pow_two, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hadd
  exact le_trans (hNP M n hn hn804) hcore

/-- Concrete NP-side tape-square bound at contradiction scale for even `n`.
This is a fully proved (non-placeholder) version of `hNP` under parity,
matching the available `tseitinAt_vertices` theorem. -/
theorem hNP_concrete_even
    (M : DTM) (n : ℕ)
    (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804)
    (heven : 2 ∣ n) :
    npNumVars n ≤ (n ^ M.timeBound + 1) ^ 2 := by
  have hn6 : n ≥ 6 := by
    have h6 : (6 : ℕ) ≤ 2 ^ 804 := by native_decide
    exact le_trans h6 hn804
  have hverts : (tseitinAt n).graph.numVertices = n :=
    tseitinAt_vertices n hn6 heven
  have hedges : (tseitinAt n).graph.numEdges ≤ n * 10 := by
    have h0 := (tseitinAt n).graph.edges_bound
    have h1 : (tseitinAt n).graph.degree ≤ 10 := (tseitinAt n).graph.degree_bound
    rw [hverts] at h0
    have : n * (tseitinAt n).graph.degree ≤ n * 10 := Nat.mul_le_mul_left _ h1
    exact le_trans h0 this
  have hclauses : (tseitinAt n).clauses.length ≤ 10 * n := by
    have h0 := (tseitinAt n).num_clauses_upper
    rw [hverts] at h0
    exact h0
  have hnp_linear : npNumVars n ≤ 50 * n := by
    unfold npNumVars Tseitin.tseitinNumVars
    omega
  have h50 : 50 ≤ n := by
    have h : (50 : ℕ) ≤ 2 ^ 804 := by native_decide
    exact le_trans h hn804
  have hlin_sq : 50 * n ≤ n ^ 2 := by
    have hmul : 50 * n ≤ n * n := by
      exact Nat.mul_le_mul_right n h50
    simpa [pow_two, Nat.mul_comm] using hmul
  have hn1 : 1 ≤ n := by
    have h : (1 : ℕ) ≤ 2 ^ 804 := by native_decide
    exact le_trans h hn804
  have hpow : n ≤ n ^ M.timeBound := by
    have h1 : n ^ 1 ≤ n ^ M.timeBound := Nat.pow_le_pow_right hn1 M.hTimeBound
    simpa using h1
  have hsq : n ^ 2 ≤ (n ^ M.timeBound + 1) ^ 2 := by
    have hstep : n ≤ n ^ M.timeBound + 1 := le_trans hpow (Nat.le_succ _)
    exact Nat.pow_le_pow_left hstep 2
  exact le_trans hnp_linear (le_trans hlin_sq hsq)

/-- Concrete global `hNP` from a single structural vertex bound.

This packages the remaining parity/generalization gap into one explicit
graph-size condition: if `(tseitinAt n).graph.numVertices ≤ n + 1`, then the
required tape-square bound follows at contradiction scale. -/
theorem hNP_concrete_of_vertex_bound
    (M : DTM) (n : ℕ)
    (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804)
    (hV : (tseitinAt n).graph.numVertices ≤ n + 1) :
    npNumVars n ≤ (n ^ M.timeBound + 1) ^ 2 := by
  have hedges : (tseitinAt n).graph.numEdges ≤ 10 * ((tseitinAt n).graph.numVertices) := by
    have h0 := (tseitinAt n).graph.edges_bound
    have h1 : (tseitinAt n).graph.degree ≤ 10 := (tseitinAt n).graph.degree_bound
    have hmul : (tseitinAt n).graph.numVertices * (tseitinAt n).graph.degree ≤
        (tseitinAt n).graph.numVertices * 10 := Nat.mul_le_mul_left _ h1
    have hmul' : (tseitinAt n).graph.numVertices * 10 ≤ 10 * (tseitinAt n).graph.numVertices := by
      simpa [Nat.mul_comm]
    exact le_trans h0 (le_trans hmul hmul')
  have hclauses : (tseitinAt n).clauses.length ≤ 10 * ((tseitinAt n).graph.numVertices) := by
    have h0 := (tseitinAt n).num_clauses_upper
    exact le_trans h0 (by omega)
  have hnp_linearV : npNumVars n ≤ 50 * ((tseitinAt n).graph.numVertices) := by
    unfold npNumVars Tseitin.tseitinNumVars
    omega
  have hnp_linearN : npNumVars n ≤ 50 * (n + 1) := by
    exact le_trans hnp_linearV (Nat.mul_le_mul_left _ hV)
  have h50 : 50 ≤ n := by
    have h : (50 : ℕ) ≤ 2 ^ 804 := by native_decide
    exact le_trans h hn804
  have hlin_sq : 50 * (n + 1) ≤ n ^ 2 := by
    have hnp : n + 1 ≤ 2 * n := by omega
    have hmul : 50 * (n + 1) ≤ 50 * (2 * n) := Nat.mul_le_mul_left _ hnp
    have h100 : 50 * (2 * n) = 100 * n := by ring
    rw [h100] at hmul
    have h100n : 100 * n ≤ n * n := by
      have h100le : 100 ≤ n := by
        have h : (100 : ℕ) ≤ 2 ^ 804 := by native_decide
        exact le_trans h hn804
      exact Nat.mul_le_mul_right n h100le
    exact le_trans hmul (by simpa [pow_two, Nat.mul_comm] using h100n)
  have hn1 : 1 ≤ n := by
    have h : (1 : ℕ) ≤ 2 ^ 804 := by native_decide
    exact le_trans h hn804
  have hpow : n ≤ n ^ M.timeBound := by
    have h1 : n ^ 1 ≤ n ^ M.timeBound := Nat.pow_le_pow_right hn1 M.hTimeBound
    simpa using h1
  have hsq : n ^ 2 ≤ (n ^ M.timeBound + 1) ^ 2 := by
    have hstep : n ≤ n ^ M.timeBound + 1 := le_trans hpow (Nat.le_succ _)
    exact Nat.pow_le_pow_left hstep 2
  exact le_trans hnp_linearN (le_trans hlin_sq hsq)

/-- Concrete global `hNP` theorem (unconditional): at contradiction scale,
`npNumVars n` is bounded by the tape-square target with no parity assumption. -/
theorem hNP_concrete_global
    (M : DTM) (n : ℕ)
    (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804) :
    npNumVars n ≤ (n ^ M.timeBound + 1) ^ 2 := by
  have hn6 : n ≥ 6 := by
    have h6 : (6 : ℕ) ≤ 2 ^ 804 := by native_decide
    exact le_trans h6 hn804
  exact hNP_concrete_of_vertex_bound M n hn hn804
    (tseitinAt_vertices_le_succ n hn6)

/-- Polynomial transport (paper/full -> latent) induced by an index embedding. -/
noncomputable def mapFullToLatentPoly (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n) :
    MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ →ₐ[ℚ]
      MvPolynomial (Fin (latentNumVars M n)) ℚ :=
  rename B.toLatent

/-- Partition-compatibility obligation for rank transport.

This states that latent blocks coarsen the pushed-forward compiled blocks under
`toLatent`.
-/
def bridgePartitionCompatible (M : DTM) (n : ℕ) (B : FullToLatentBridge M n) : Prop :=
  ∀ i j : Fin (numVars M n (Nat.log 2 n)),
    (compiledPartition M n).assign i = (compiledPartition M n).assign j →
    (latentPartition M n).assign (B.toLatent i) = (latentPartition M n).assign (B.toLatent j)

/-- Polynomial-identification obligation at the bridge boundary.

This is the semantic statement that transported paper/full compiled polynomial
matches the latent compiled polynomial.
-/
def bridgePolyIdentifiesLatent (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n) : Prop :=
  mapFullToLatentPoly M n B (fullCompiledPoly ℚ M n h_le) = latentCompiledPoly M n

/-- Generator-term mapping lemma (verifier sheet): transporting `verifierSheetOf`
across the bridge is exactly renaming `tseitinPoly` by the composed inclusion map. -/
theorem map_verifierSheetOf (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n) :
    mapFullToLatentPoly M n B (verifierSheetOf ℚ M n h_le)
      = MvPolynomial.rename (Function.comp B.toLatent (witnessInclusion M n h_le))
          (tseitinPoly ℚ n) := by
  unfold mapFullToLatentPoly verifierSheetOf
  simpa [Function.comp] using
    (MvPolynomial.rename_rename (witnessInclusion M n h_le) B.toLatent (tseitinPoly ℚ n))

/-- Generator-term mapping lemma (violation polynomial): transport is just rename. -/
theorem map_violationPolyOf (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n) :
    mapFullToLatentPoly M n B (violationPolyOf ℚ M n)
      = MvPolynomial.rename B.toLatent (violationPolyOf ℚ M n) :=
  rfl

/-- Generator decomposition under transport: transported full polynomial is the sum
of transported verifier-sheet and transported violation polynomial. -/
theorem map_fullCompiledPoly_generators (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n) :
    mapFullToLatentPoly M n B (fullCompiledPoly ℚ M n h_le)
      = mapFullToLatentPoly M n B (verifierSheetOf ℚ M n h_le)
        + mapFullToLatentPoly M n B (violationPolyOf ℚ M n) := by
  unfold fullCompiledPoly
  simp [mapFullToLatentPoly]

/-- Step-3 lifting lemma (algebra-hom extensionality/composition style):
if each generator term is identified after transport and those identified
generators recombine to `latentCompiledPoly`, then full polynomial
identification follows. -/
theorem bridgePolyIdentifiesLatent_of_generatorIdentities
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (V W : MvPolynomial (Fin (latentNumVars M n)) ℚ)
    (hVer : mapFullToLatentPoly M n B (verifierSheetOf ℚ M n h_le) = V)
    (hViol : mapFullToLatentPoly M n B (violationPolyOf ℚ M n) = W)
    (hLatent : latentCompiledPoly M n = V + W) :
    bridgePolyIdentifiesLatent M n h_le B := by
  unfold bridgePolyIdentifiesLatent
  calc
    mapFullToLatentPoly M n B (fullCompiledPoly ℚ M n h_le)
        = mapFullToLatentPoly M n B (verifierSheetOf ℚ M n h_le)
          + mapFullToLatentPoly M n B (violationPolyOf ℚ M n) :=
            map_fullCompiledPoly_generators M n h_le B
    _ = V + W := by rw [hVer, hViol]
    _ = latentCompiledPoly M n := by simpa [hLatent] using (Eq.symm hLatent)

/-- Global packaged hPolyId constructor from generator-identification equalities.
This is the concrete recombination theorem used in step (3): once verifier-sheet
and violation terms are each identified after transport, full polynomial
identification follows globally. -/
theorem globalPolyId_of_generatorIdentities
    (hLeVar : ∀ (M : DTM) (n : ℕ),
      numVars M n (Nat.log 2 n) ≤ latentNumVars M n)
    (hLeWitness : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hVerId : ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      mapFullToLatentPoly M n (fullToLatentBridgeOfLe M n (hLeVar M n))
        (verifierSheetOf ℚ M n (hLeWitness M n hn hn804))
      = MvPolynomial.rename
          (Function.comp (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
            (witnessInclusion M n (hLeWitness M n hn hn804)))
          (tseitinPoly ℚ n))
    (hViolId : ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      mapFullToLatentPoly M n (fullToLatentBridgeOfLe M n (hLeVar M n))
        (violationPolyOf ℚ M n)
      = MvPolynomial.rename (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
          (violationPolyOf ℚ M n))
    (hLatentDecomp : ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      latentCompiledPoly M n
        = MvPolynomial.rename
            (Function.comp (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
              (witnessInclusion M n (hLeWitness M n hn hn804)))
            (tseitinPoly ℚ n)
          + MvPolynomial.rename (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
              (violationPolyOf ℚ M n)) :
    ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      bridgePolyIdentifiesLatent M n (hLeWitness M n hn hn804)
        (fullToLatentBridgeOfLe M n (hLeVar M n)) := by
  intro M n hn hn804
  refine bridgePolyIdentifiesLatent_of_generatorIdentities M n
    (hLeWitness M n hn hn804)
    (fullToLatentBridgeOfLe M n (hLeVar M n))
    _ _ (hVerId M n hn hn804) (hViolId M n hn hn804) (hLatentDecomp M n hn hn804)

/-- Step-3 concrete `hVerId` constructor in the active API shape.

Instantiates the transported verifier-sheet identity exactly at the canonical
bridge/witness indexing used by the final route. -/
theorem globalVerId_of_mapVerifier
    (hLeVar : ∀ (M : DTM) (n : ℕ),
      numVars M n (Nat.log 2 n) ≤ latentNumVars M n)
    (hLeWitness : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      mapFullToLatentPoly M n (fullToLatentBridgeOfLe M n (hLeVar M n))
        (verifierSheetOf ℚ M n (hLeWitness M n hn hn804))
      = MvPolynomial.rename
          (Function.comp (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
            (witnessInclusion M n (hLeWitness M n hn hn804)))
          (tseitinPoly ℚ n) := by
  intro M n hn hn804
  exact map_verifierSheetOf M n (hLeWitness M n hn hn804)
    (fullToLatentBridgeOfLe M n (hLeVar M n))

/-- Step-3 concrete `hViolId` constructor in the active API shape.

Instantiates the transported violation-polynomial identity exactly at the
canonical bridge used by the final route. -/
theorem globalViolId_of_mapViolation
    (hLeVar : ∀ (M : DTM) (n : ℕ),
      numVars M n (Nat.log 2 n) ≤ latentNumVars M n) :
    ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      mapFullToLatentPoly M n (fullToLatentBridgeOfLe M n (hLeVar M n))
        (violationPolyOf ℚ M n)
      = MvPolynomial.rename (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
          (violationPolyOf ℚ M n) := by
  intro M n hn hn804
  exact map_violationPolyOf M n (fullToLatentBridgeOfLe M n (hLeVar M n))

/-- Step-3 concrete `hLatentDecomp` API wrapper.

Current route keeps this decomposition as an explicit semantic input; this theorem
packages that input in the exact witness/indexing shape consumed by
`globalPolyId_of_generatorIdentities`. -/
theorem globalLatentDecompAPI_ofAssumption
    (hLeVar : ∀ (M : DTM) (n : ℕ),
      numVars M n (Nat.log 2 n) ≤ latentNumVars M n)
    (hLeWitness : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hLatentDecomp : ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      latentCompiledPoly M n
        = MvPolynomial.rename
            (Function.comp (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
              (witnessInclusion M n (hLeWitness M n hn hn804)))
            (tseitinPoly ℚ n)
          + MvPolynomial.rename (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
              (violationPolyOf ℚ M n)) :
    ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      latentCompiledPoly M n
        = MvPolynomial.rename
            (Function.comp (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
              (witnessInclusion M n (hLeWitness M n hn hn804)))
            (tseitinPoly ℚ n)
          + MvPolynomial.rename (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
              (violationPolyOf ℚ M n) :=
  hLatentDecomp

/-- Concrete constructor for `hLatentDecomp` from two semantic sub-obligations:
(1) transported verifier term vanishes, and
(2) transported violation term equals `latentCompiledPoly`.

This isolates the actual semantic work while keeping the final API shape fixed. -/
theorem globalLatentDecomp_ofVerifierVanish_andViolationMatches
    (hLeVar : ∀ (M : DTM) (n : ℕ),
      numVars M n (Nat.log 2 n) ≤ latentNumVars M n)
    (hLeWitness : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hVerVanish : ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      MvPolynomial.rename
          (Function.comp (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
            (witnessInclusion M n (hLeWitness M n hn hn804)))
          (tseitinPoly ℚ n) = 0)
    (hViolMatches : ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      MvPolynomial.rename (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
          (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      latentCompiledPoly M n
        = MvPolynomial.rename
            (Function.comp (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
              (witnessInclusion M n (hLeWitness M n hn hn804)))
            (tseitinPoly ℚ n)
          + MvPolynomial.rename (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
              (violationPolyOf ℚ M n) := by
  intro M n hn hn804
  calc
    latentCompiledPoly M n
        = 0 + latentCompiledPoly M n := by simp
    _ = MvPolynomial.rename
          (Function.comp (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
            (witnessInclusion M n (hLeWitness M n hn hn804)))
          (tseitinPoly ℚ n)
        + MvPolynomial.rename (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
            (violationPolyOf ℚ M n) := by
          rw [hVerVanish M n hn hn804, hViolMatches M n hn hn804]

/-- Step-3 closure helper: with the concrete global `hVerId` and `hViolId`
constructors, plus a supplied latent decomposition witness in active API shape,
produce concrete global `hPolyId`. -/
theorem globalPolyId_of_mapVerifier_mapViolation_and_latentDecomp
    (hLeVar : ∀ (M : DTM) (n : ℕ),
      numVars M n (Nat.log 2 n) ≤ latentNumVars M n)
    (hLeWitness : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hLatentDecomp : ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      latentCompiledPoly M n
        = MvPolynomial.rename
            (Function.comp (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
              (witnessInclusion M n (hLeWitness M n hn hn804)))
            (tseitinPoly ℚ n)
          + MvPolynomial.rename (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
              (violationPolyOf ℚ M n)) :
    ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      bridgePolyIdentifiesLatent M n (hLeWitness M n hn hn804)
        (fullToLatentBridgeOfLe M n (hLeVar M n)) :=
  globalPolyId_of_generatorIdentities hLeVar hLeWitness
    (globalVerId_of_mapVerifier hLeVar hLeWitness)
    (globalViolId_of_mapViolation hLeVar)
    (globalLatentDecompAPI_ofAssumption hLeVar hLeWitness hLatentDecomp)

/-- Rank-domination obligation exported by a bridge at one `(M,n)` instance. -/
def bridgeRankDomination (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n) : Prop :=
  mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (latentCompiledPoly M n)
    ≤ mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n h_le)

/-- Decomposed Step-2 obligation: domination where the latent side is written as
transported full polynomial via the bridge map. -/
def bridgeRankDominationMapped (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n) : Prop :=
  mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (mapFullToLatentPoly M n B (fullCompiledPoly ℚ M n h_le))
    ≤ mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n h_le)

/-- Step-2 reduction lemma: to prove `bridgeRankDomination`, it suffices to prove
mapped domination plus polynomial identification (`full` transported = latent). -/
theorem bridgeRankDomination_ofMappedAndPolyId (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (hMapDom : bridgeRankDominationMapped M n h_le B)
    (hPolyId : bridgePolyIdentifiesLatent M n h_le B) :
    bridgeRankDomination M n h_le B := by
  unfold bridgeRankDomination at *
  unfold bridgeRankDominationMapped at hMapDom
  rw [hPolyId] at hMapDom
  exact hMapDom

/-- Concrete mapped-domination constructor from pointwise assignment
correspondence between compiled and pullback(latent) partitions.

This avoids requiring record-level partition equality and instead uses the exact
semantic condition needed for SPDP-rank transfer. -/
theorem bridgeRankDominationMapped_of_assignEq (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (hAssign : ∀ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i =
        (pullbackPartition (latentPartition M n) B.toLatent).assign i) :
    bridgeRankDominationMapped M n h_le B := by
  let Bc := compiledPartition M n
  let Bp := pullbackPartition (latentPartition M n) B.toLatent
  have href_bc_to_bp : ∀ i j : Fin (numVars M n (Nat.log 2 n)),
      Bc.assign i = Bc.assign j → Bp.assign i = Bp.assign j := by
    intro i j hij
    calc
      Bp.assign i = Bc.assign i := (hAssign i).symm
      _ = Bc.assign j := hij
      _ = Bp.assign j := hAssign j
  have href_bp_to_bc : ∀ i j : Fin (numVars M n (Nat.log 2 n)),
      Bp.assign i = Bp.assign j → Bc.assign i = Bc.assign j := by
    intro i j hij
    calc
      Bc.assign i = Bp.assign i := hAssign i
      _ = Bp.assign j := hij
      _ = Bc.assign j := (hAssign j).symm
  have hsub1 : mlBlockedSpdpSubspace Bp (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
      ≤ mlBlockedSpdpSubspace Bc (Nat.log 2 n) (Nat.log 2 n)
          (fullCompiledPoly ℚ M n h_le) :=
    mlBlockedSpdpSubspace_mono_partition Bc Bp (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le) href_bc_to_bp
  have hsub2 : mlBlockedSpdpSubspace Bc (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
      ≤ mlBlockedSpdpSubspace Bp (Nat.log 2 n) (Nat.log 2 n)
          (fullCompiledPoly ℚ M n h_le) :=
    mlBlockedSpdpSubspace_mono_partition Bp Bc (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le) href_bp_to_bc
  have hrEq : mlBlockedSpdpRank Bp (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
      = mlBlockedSpdpRank Bc (Nat.log 2 n) (Nat.log 2 n)
          (fullCompiledPoly ℚ M n h_le) := by
    unfold mlBlockedSpdpRank
    apply le_antisymm
    · exact Submodule.finrank_mono hsub1
    · exact Submodule.finrank_mono hsub2
  unfold bridgeRankDominationMapped
  have hrename := mlBlockedSpdpRank_rename_le B.toLatent B.inj
      (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
  -- Bp is definitional pullback(latent,toLatent)
  simpa [mapFullToLatentPoly, Bp, Bc, hrEq] using hrename

/-- Step-2 global constructor: package a global bridge-rank assumption into the
exact API shape consumed by the final route (`hDom` over concrete bridge objects).

This is the canonical handoff point for the forthcoming semantic proof that
establishes domination from partition-compatibility + polynomial identification. -/
theorem globalBridgeRankDominationOfGlobalAssumption
    (hLeVar : ∀ (M : DTM) (n : ℕ),
      numVars M n (Nat.log 2 n) ≤ latentNumVars M n)
    (hLeWitness : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hDomAssumption : ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      bridgeRankDomination M n (hLeWitness M n hn hn804)
        (fullToLatentBridgeOfLe M n (hLeVar M n))) :
    ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      bridgeRankDomination M n (hLeWitness M n hn hn804)
        ((globalFullToLatentBridgeOfGlobalLe hLeVar) M n) := by
  intro M n hn hn804
  simpa [globalFullToLatentBridgeOfGlobalLe] using hDomAssumption M n hn hn804

/-- Step-2 packaged API constructor: from a global domination assumption on the
canonical cast bridge, produce both API components used by final closure:
`hBridgeObj` and `hDom`. -/
theorem globalBridgeAPI_ofGlobalDomination
    (hLeVar : ∀ (M : DTM) (n : ℕ),
      numVars M n (Nat.log 2 n) ≤ latentNumVars M n)
    (hLeWitness : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hDomAssumption : ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      bridgeRankDomination M n (hLeWitness M n hn hn804)
        (fullToLatentBridgeOfLe M n (hLeVar M n))) :
    ∃ hBridgeObj : (∀ (M : DTM) (n : ℕ), FullToLatentBridge M n),
      ∀ (M : DTM) (n : ℕ),
        (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
        bridgeRankDomination M n (hLeWitness M n hn hn804)
          (hBridgeObj M n) := by
  refine ⟨globalFullToLatentBridgeOfGlobalLe hLeVar, ?_⟩
  intro M n hn hn804
  exact globalBridgeRankDominationOfGlobalAssumption hLeVar hLeWitness hDomAssumption M n hn hn804

/-- Local equivalence helper: a direct pointwise assignment equation
`compiled.assign i = latent.assign (toLatent i)` implies the pullback-form
pointwise equation consumed by `bridgeRankDominationMapped_of_assignEq`. -/
theorem bridgeAssignEq_of_assignToLatent (M : DTM) (n : ℕ)
    (B : FullToLatentBridge M n)
    (hAssignToLatent : ∀ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i = (latentPartition M n).assign (B.toLatent i)) :
    ∀ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i =
        (pullbackPartition (latentPartition M n) B.toLatent).assign i := by
  intro i
  simpa [pullbackPartition] using hAssignToLatent i

/-- Global packaged Step-(2) mapped-domination constructor from pointwise
compiled-vs-pullback assignment correspondence (instancewise). -/
theorem globalMapDom_of_globalAssignEq
    (hLeVar : ∀ (M : DTM) (n : ℕ),
      numVars M n (Nat.log 2 n) ≤ latentNumVars M n)
    (hLeWitness : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hAssign : ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804)
      (i : Fin (numVars M n (Nat.log 2 n))),
      (compiledPartition M n).assign i =
        (pullbackPartition (latentPartition M n)
          (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent).assign i) :
    ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      bridgeRankDominationMapped M n (hLeWitness M n hn hn804)
        (fullToLatentBridgeOfLe M n (hLeVar M n)) := by
  intro M n hn hn804
  exact bridgeRankDominationMapped_of_assignEq M n
    (hLeWitness M n hn hn804)
    (fullToLatentBridgeOfLe M n (hLeVar M n))
    (hAssign M n hn hn804)

/-- Equivalent Step-(2) global constructor using the more semantic pointwise
condition `compiled.assign i = latent.assign (toLatent i)`.

This is often the natural endpoint of compiler/embedding semantics, and is
immediately converted to `globalMapDom_of_globalAssignEq`. -/
theorem globalMapDom_of_globalAssignToLatent
    (hLeVar : ∀ (M : DTM) (n : ℕ),
      numVars M n (Nat.log 2 n) ≤ latentNumVars M n)
    (hLeWitness : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hAssignToLatent : ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804)
      (i : Fin (numVars M n (Nat.log 2 n))),
      (compiledPartition M n).assign i =
        (latentPartition M n).assign
          ((fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent i)) :
    ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      bridgeRankDominationMapped M n (hLeWitness M n hn hn804)
        (fullToLatentBridgeOfLe M n (hLeVar M n)) := by
  intro M n hn hn804
  exact bridgeRankDominationMapped_of_assignEq M n
    (hLeWitness M n hn hn804)
    (fullToLatentBridgeOfLe M n (hLeVar M n))
    (bridgeAssignEq_of_assignToLatent M n (fullToLatentBridgeOfLe M n (hLeVar M n))
      (hAssignToLatent M n hn hn804))

theorem globalBridgeDomination_ofMappedAndPolyId
    (hLeVar : ∀ (M : DTM) (n : ℕ),
      numVars M n (Nat.log 2 n) ≤ latentNumVars M n)
    (hLeWitness : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hMapDom : ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      bridgeRankDominationMapped M n (hLeWitness M n hn hn804)
        (fullToLatentBridgeOfLe M n (hLeVar M n)))
    (hPolyId : ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      bridgePolyIdentifiesLatent M n (hLeWitness M n hn hn804)
        (fullToLatentBridgeOfLe M n (hLeVar M n))) :
    ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      bridgeRankDomination M n (hLeWitness M n hn hn804)
        (fullToLatentBridgeOfLe M n (hLeVar M n)) := by
  intro M n hn hn804
  exact bridgeRankDomination_ofMappedAndPolyId M n
    (hLeWitness M n hn hn804)
    (fullToLatentBridgeOfLe M n (hLeVar M n))
    (hMapDom M n hn hn804)
    (hPolyId M n hn hn804)

/-- Step-2 packaged API constructor directly from mapped-domination + poly-id.
This is the canonical constructor used by final-route closure theorems when the
semantic proof is split into these two sub-obligations. -/
theorem globalBridgeAPI_ofMappedAndPolyId
    (hLeVar : ∀ (M : DTM) (n : ℕ),
      numVars M n (Nat.log 2 n) ≤ latentNumVars M n)
    (hLeWitness : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hMapDom : ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      bridgeRankDominationMapped M n (hLeWitness M n hn hn804)
        (fullToLatentBridgeOfLe M n (hLeVar M n)))
    (hPolyId : ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      bridgePolyIdentifiesLatent M n (hLeWitness M n hn hn804)
        (fullToLatentBridgeOfLe M n (hLeVar M n))) :
    ∃ hBridgeObj : (∀ (M : DTM) (n : ℕ), FullToLatentBridge M n),
      ∀ (M : DTM) (n : ℕ),
        (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
        bridgeRankDomination M n (hLeWitness M n hn hn804)
          (hBridgeObj M n) :=
  globalBridgeAPI_ofGlobalDomination hLeVar hLeWitness
    (globalBridgeDomination_ofMappedAndPolyId hLeVar hLeWitness hMapDom hPolyId)


/-- Parameterized Step-3 API constructor (preferred): given `hLeWitness`, package
any global full rank160 theorem in the exact shape consumed downstream. -/
theorem globalFullRank160API_ofAssumption_withWitness
    (hLeWitness : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hFullAssumption : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n (hLeWitness M n hn hn804)) ≤ n ^ 160) :
    ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n (hLeWitness M n hn hn804)) ≤ n ^ 160 :=
  hFullAssumption

/-- Arithmetic helper: the contradiction-scale side condition `hn804 : n ≥ 2^804`
implies the paper-side threshold `n ≥ 32`. -/
theorem n32_of_hn804 (n : ℕ) (hn804 : n ≥ 2 ^ 804) : n ≥ 32 := by
  have hpow : (32 : ℕ) ≤ 2 ^ 804 := by
    native_decide
  exact le_trans hpow hn804

/-- Step-3 canonical API wrapper for the paper-side full rank theorem.

Keep this theorem parameterized by the active full-side statement so it remains
stable even if theorem names/signatures evolve across files. -/
theorem globalFullRank160API_ofPside
    (hLeWitness : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hPside : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n (hLeWitness M n hn hn804)) ≤ n ^ 160) :
    ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n (hLeWitness M n hn hn804)) ≤ n ^ 160 :=
  hPside

/-- Step-3 helper wrapper for paper-style theorems that require only `n ≥ 32`
(and `h_le`) rather than full contradiction-scale side conditions. -/
theorem globalFullRank160API_ofCore32
    (hLeWitness : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hCore : ∀ (M : DTM) (n : ℕ),
      n ≥ 32 →
      (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) →
      mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n h_le) ≤ n ^ 160) :
    ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n (hLeWitness M n hn hn804)) ≤ n ^ 160 := by
  intro M n hn hn804
  exact hCore M n (n32_of_hn804 n hn804) (hLeWitness M n hn hn804)

/-- Transport wrapper: once rank domination is established, we can read it as a
usable inequality theorem directly. -/
theorem latent_rank_le_full_rank_of_bridge (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (hDom : bridgeRankDomination M n h_le B) :
    mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (latentCompiledPoly M n)
    ≤ mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n h_le) :=
  hDom

/-- Transport-to-bound wrapper: combine bridge domination with any full-compiled
rank bound to obtain the corresponding latent rank bound. -/
theorem latent_rank_bound_of_full_rank_bound_of_bridge (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (hDom : bridgeRankDomination M n h_le B)
    (hFull : mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le) ≤ n ^ 160) :
    mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (latentCompiledPoly M n) ≤ n ^ 160 :=
  le_trans hDom hFull

end LatentFullBridge
