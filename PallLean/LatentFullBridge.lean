import PallLean.LatentCompiler
import PallLean.MultilinearSPDP
import PallLean.ProfileCompression
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

/-- Diagnostic equivalence for the route-2 semantic obligation `hVerVanish`.
For the canonical cast bridge, transported verifier-sheet vanishing is equivalent
to `tseitinPoly = 0`, because the transport map is injective. -/
theorem verifierTransport_vanish_iff_tseitin_zero
    (hLeVar : ∀ (M : DTM) (n : ℕ),
      numVars M n (Nat.log 2 n) ≤ latentNumVars M n)
    (hLeWitness : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      npNumVars n ≤ numVars M n (Nat.log 2 n))
    (M : DTM) (n : ℕ)
    (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804) :
    (MvPolynomial.rename
      (Function.comp (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
        (witnessInclusion M n (hLeWitness M n hn hn804)))
      (tseitinPoly ℚ n) = 0)
    ↔ (tseitinPoly ℚ n = 0) := by
  let f := Function.comp (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
    (witnessInclusion M n (hLeWitness M n hn hn804))
  have hf : Function.Injective f := by
    intro x y hxy
    exact (witnessInclusion_injective M n (hLeWitness M n hn hn804))
      ((fullToLatentBridgeOfLe M n (hLeVar M n)).inj hxy)
  constructor
  · intro hvanish
    have h' : MvPolynomial.rename f (tseitinPoly ℚ n) = MvPolynomial.rename f 0 := by
      simpa using hvanish
    exact (MvPolynomial.rename_injective f hf) h'
  · intro hzero
    simpa [hzero]

/-- Diagnostic consequence for route-2 `hViolMatches` under the canonical cast
bridge: if transported violation equals `latentCompiledPoly`, then latent compiled
polynomial has total degree ≤ 4 (inherited from `violationPolyOf`). -/
theorem latent_totalDegree_le_four_of_hViolMatches
    (hLeVar : ∀ (M : DTM) (n : ℕ),
      numVars M n (Nat.log 2 n) ≤ latentNumVars M n)
    (M : DTM) (n : ℕ)
    (hViolMatches : MvPolynomial.rename
      (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
      (violationPolyOf ℚ M n) = latentCompiledPoly M n) :
    (latentCompiledPoly M n).totalDegree ≤ 4 := by
  rw [← hViolMatches]
  exact le_trans
    (MvPolynomial.totalDegree_rename_le
      (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
      (violationPolyOf ℚ M n))
    (violationPolyOf_totalDegree ℚ M n)

/-- Contradiction extractor for route-2 `hViolMatches`: any witnessed monomial
of latent compiled polynomial with degree strictly greater than 4 refutes
`hViolMatches` (under the canonical cast bridge). -/
theorem no_hViolMatches_of_high_degree_coeff
    (hLeVar : ∀ (M : DTM) (n : ℕ),
      numVars M n (Nat.log 2 n) ≤ latentNumVars M n)
    (M : DTM) (n : ℕ)
    (d : (Fin (latentNumVars M n)) →₀ ℕ)
    (hd : 4 < ∑ i ∈ d.support, d i)
    (hcoeff : MvPolynomial.coeff d (latentCompiledPoly M n) ≠ 0) :
    ¬ (MvPolynomial.rename
      (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
      (violationPolyOf ℚ M n) = latentCompiledPoly M n) := by
  intro hViolMatches
  have hdeg : (latentCompiledPoly M n).totalDegree ≤ 4 :=
    latent_totalDegree_le_four_of_hViolMatches hLeVar M n hViolMatches
  have hlt : (latentCompiledPoly M n).totalDegree < ∑ i ∈ d.support, d i :=
    lt_of_le_of_lt hdeg hd
  have hzero : MvPolynomial.coeff d (latentCompiledPoly M n) = 0 :=
    MvPolynomial.coeff_eq_zero_of_totalDegree_lt hlt
  exact hcoeff hzero

/-- Sheet-split witness lift: a high-degree nonzero coefficient in `selConSheet`
that is absent from `machCopySheet` and `copyConSheet` induces a high-degree
nonzero coefficient in `latentCompiledPoly`. -/
theorem latent_high_degree_coeff_of_selCon_sheet_split
    (M : DTM) (n : ℕ)
    (d : (Fin (latentNumVars M n)) →₀ ℕ)
    (hd : 4 < ∑ i ∈ d.support, d i)
    (hsel : MvPolynomial.coeff d (selConSheet M n) ≠ 0)
    (hmach : MvPolynomial.coeff d (machCopySheet M n) = 0)
    (hcopy : MvPolynomial.coeff d (copyConSheet M n) = 0) :
    MvPolynomial.coeff d (latentCompiledPoly M n) ≠ 0 := by
  intro hzero
  have hcoeff : MvPolynomial.coeff d (latentCompiledPoly M n)
      = MvPolynomial.coeff d (machCopySheet M n)
      + MvPolynomial.coeff d (copyConSheet M n)
      + MvPolynomial.coeff d (selConSheet M n) := by
    unfold latentCompiledPoly
    simp [MvPolynomial.coeff_add, add_assoc, add_left_comm, add_comm]
  rw [hzero] at hcoeff
  rw [hmach, hcopy] at hcoeff
  simp at hcoeff
  exact hsel hcoeff.symm

/-- Immediate route-2 contradiction corollary from the sheet-split witness form. -/
theorem no_hViolMatches_of_selCon_sheet_split_witness
    (hLeVar : ∀ (M : DTM) (n : ℕ),
      numVars M n (Nat.log 2 n) ≤ latentNumVars M n)
    (M : DTM) (n : ℕ)
    (d : (Fin (latentNumVars M n)) →₀ ℕ)
    (hd : 4 < ∑ i ∈ d.support, d i)
    (hsel : MvPolynomial.coeff d (selConSheet M n) ≠ 0)
    (hmach : MvPolynomial.coeff d (machCopySheet M n) = 0)
    (hcopy : MvPolynomial.coeff d (copyConSheet M n) = 0) :
    ¬ (MvPolynomial.rename
      (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
      (violationPolyOf ℚ M n) = latentCompiledPoly M n) :=
  no_hViolMatches_of_high_degree_coeff hLeVar M n d hd
    (latent_high_degree_coeff_of_selCon_sheet_split M n d hd hsel hmach hcopy)

/-- Canonical candidate high-degree monomial for the sel/con sheet witness path:
one sel-slot and one con-slot exponent for every base index. -/
noncomputable def allSelConMono (M : DTM) (n : ℕ) :
    (Fin (latentNumVars M n)) →₀ ℕ :=
  (Finset.univ : Finset (Fin (latentBaseVars M n))).sum
    (fun i => Finsupp.single (selSlot M n i) 1 + Finsupp.single (conSlot M n i) 1)

/-- Fully concrete route-2 contradiction wrapper at the canonical sel/con witness
monomial. This isolates the remaining sheet-level coefficient obligations as
explicit, checkable lemmas. -/
theorem no_hViolMatches_of_allSelCon_witness
    (hLeVar : ∀ (M : DTM) (n : ℕ),
      numVars M n (Nat.log 2 n) ≤ latentNumVars M n)
    (M : DTM) (n : ℕ)
    (hdeg : 4 < ∑ i ∈ (allSelConMono M n).support, (allSelConMono M n) i)
    (hsel : MvPolynomial.coeff (allSelConMono M n) (selConSheet M n) ≠ 0)
    (hmach : MvPolynomial.coeff (allSelConMono M n) (machCopySheet M n) = 0)
    (hcopy : MvPolynomial.coeff (allSelConMono M n) (copyConSheet M n) = 0) :
    ¬ (MvPolynomial.rename
      (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
      (violationPolyOf ℚ M n) = latentCompiledPoly M n) :=
  no_hViolMatches_of_selCon_sheet_split_witness hLeVar M n (allSelConMono M n)
    hdeg hsel hmach hcopy

/-- Single-gadget target coefficient for the sel/con witness monomial. -/
theorem coeff_selConGadget_target_mono (M : DTM) (n : ℕ)
    (i : Fin (latentBaseVars M n)) :
    MvPolynomial.coeff
      ((Finsupp.single (selSlot M n i) (1 : ℕ)) + (Finsupp.single (conSlot M n i) (1 : ℕ)))
      (selConGadget M n i) = (-1 : ℚ) := by
  let s := selSlot M n i
  let c := conSlot M n i
  have hsc : s ≠ c := by
    intro h
    simp [s, c, selSlot, conSlot, slot, Fin.ext_iff] at h
  have hsub :
      ((Finsupp.single s (1 : ℕ)) + (Finsupp.single c (1 : ℕ)) - Finsupp.single s 1)
        = Finsupp.single c 1 := by
    ext x
    by_cases hx : x = s
    · subst hx
      simp [hsc]
    · by_cases hxc : x = c
      · subst hxc
        simp [hsc]
      · simp [hx, hxc]
  unfold selConGadget Xsel Xcon
  rw [MvPolynomial.coeff_sub]
  have hmono_ne_zero : (Finsupp.single s 1 + Finsupp.single c 1 : (Fin (latentNumVars M n)) →₀ ℕ) ≠ 0 := by
    intro hz
    have : (Finsupp.single s 1 + Finsupp.single c 1 : (Fin (latentNumVars M n)) →₀ ℕ) s = 0 := by
      simpa [hz]
    simp [hsc] at this
  have h1 : MvPolynomial.coeff (Finsupp.single s 1 + Finsupp.single c 1)
      (1 : MvPolynomial (Fin (latentNumVars M n)) ℚ) = 0 := by
    rw [MvPolynomial.coeff_one]
    by_cases hzero : (Finsupp.single s 1 + Finsupp.single c 1 : (Fin (latentNumVars M n)) →₀ ℕ) = 0
    · exact (hmono_ne_zero hzero).elim
    · have hzero' : ¬ (0 : (Fin (latentNumVars M n)) →₀ ℕ) = (Finsupp.single s 1 + Finsupp.single c 1) :=
        fun h => hzero h.symm
      simp [hzero']
  have h2 : MvPolynomial.coeff (Finsupp.single s 1 + Finsupp.single c 1)
      ((X s : MvPolynomial (Fin (latentNumVars M n)) ℚ) * X c) = 1 := by
    rw [MvPolynomial.coeff_X_mul]
    simpa [hsub] using (MvPolynomial.coeff_X (R := ℚ) c)
  simpa [h1, h2]

/-- Single-gadget `usesOnly` for route-2 coefficient factorization.
`selConGadget M n i` depends only on `{selSlot i, conSlot i}`. -/
theorem selConGadget_usesOnly_selConPair (M : DTM) (n : ℕ)
    (i : Fin (latentBaseVars M n)) :
    CoeffDisjoint.usesOnly (selConGadget M n i)
      ({selSlot M n i, conSlot M n i} : Set (Fin (latentNumVars M n))) := by
  intro m hm x hx
  have hvars : x ∈ (selConGadget M n i).vars :=
    (MvPolynomial.mem_vars _).mpr ⟨m, hm, hx⟩
  -- variables of gadget are contained in vars of X(sel)*X(con)
  have hsub := (MvPolynomial.vars_sub_subset
    (p := (1 : MvPolynomial (Fin (latentNumVars M n)) ℚ))
    (q := (X (selSlot M n i) * X (conSlot M n i) :
      MvPolynomial (Fin (latentNumVars M n)) ℚ)))
  have hprod : x ∈ (X (selSlot M n i) * X (conSlot M n i) :
      MvPolynomial (Fin (latentNumVars M n)) ℚ).vars := by
    have hunion : x ∈ (1 : MvPolynomial (Fin (latentNumVars M n)) ℚ).vars ∪
      (X (selSlot M n i) * X (conSlot M n i) :
        MvPolynomial (Fin (latentNumVars M n)) ℚ).vars := by
      simpa [selConGadget, Xsel, Xcon] using hsub hvars
    have hnotC : x ∉ (1 : MvPolynomial (Fin (latentNumVars M n)) ℚ).vars := by
      simpa using (MvPolynomial.not_mem_vars_C (1 : ℚ) x)
    exact (Finset.mem_union.mp hunion).resolve_left hnotC
  have hmul := (MvPolynomial.vars_mul (X (selSlot M n i)) (X (conSlot M n i))) hprod
  have hxpair : x = selSlot M n i ∨ x = conSlot M n i := by
    simpa [MvPolynomial.vars_X, Finset.mem_union, Finset.mem_singleton] using hmul
  rcases hxpair with rfl | rfl <;> simp

/-- Per-block witness monomial is supported exactly on the sel/con pair. -/
theorem mono_selConPair_supported (M : DTM) (n : ℕ)
    (i : Fin (latentBaseVars M n)) :
    CoeffDisjoint.monomSupportedIn
      ((Finsupp.single (selSlot M n i) (1 : ℕ)) + (Finsupp.single (conSlot M n i) (1 : ℕ)))
      ({selSlot M n i, conSlot M n i} : Set (Fin (latentNumVars M n))) := by
  intro x hx
  have hsc : selSlot M n i ≠ conSlot M n i := by
    simp [selSlot, conSlot, slot, Fin.ext_iff]
  by_cases hxs : x = selSlot M n i
  · left; exact hxs
  · by_cases hxc : x = conSlot M n i
    · right; exact hxc
    · exfalso
      have : ((Finsupp.single (selSlot M n i) (1 : ℕ)) + (Finsupp.single (conSlot M n i) (1 : ℕ))) x = 0 := by
        simp [Finsupp.single_apply, hxs, hxc]
      exact (Finsupp.mem_support_iff.mp hx) this

/-- Pairwise disjointness of per-block sel/con variable sets. -/
theorem selConPair_disjoint_of_ne (M : DTM) (n : ℕ)
    {i j : Fin (latentBaseVars M n)} (hij : i ≠ j) :
    Disjoint ({selSlot M n i, conSlot M n i} : Set (Fin (latentNumVars M n)))
      ({selSlot M n j, conSlot M n j} : Set (Fin (latentNumVars M n))) := by
  rw [Set.disjoint_left]
  intro x hxI hxJ
  rcases hxI with rfl | rfl <;> rcases hxJ with h | h
  · exact hij (selSlot_injective M n h)
  · -- sel i = con j impossible (2 mod 4 = 3 mod 4)
    have : False := by
      simp [selSlot, conSlot, slot, Fin.ext_iff] at h
      omega
    exact this.elim
  · -- con i = sel j impossible
    have : False := by
      simp [selSlot, conSlot, slot, Fin.ext_iff] at h
      omega
    exact this.elim
  · -- con i = con j implies i=j
    have : i = j := by
      simpa [conSlot, slot, Fin.ext_iff] using h
    exact hij this

/-- Union of per-block sel/con variable pairs over a finite index set. -/
def selConPairUnion (M : DTM) (n : ℕ) (S : Finset (Fin (latentBaseVars M n))) :
    Set (Fin (latentNumVars M n)) :=
  {x | ∃ i ∈ S, x ∈ ({selSlot M n i, conSlot M n i} : Set (Fin (latentNumVars M n)))}

/-- Product over a finite set of sel/con gadgets uses only the corresponding
union of per-block sel/con variable pairs. -/
theorem usesOnly_selConProd_on_set (M : DTM) (n : ℕ)
    (S : Finset (Fin (latentBaseVars M n))) :
    CoeffDisjoint.usesOnly (∏ i ∈ S, selConGadget M n i) (selConPairUnion M n S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro m hm x hx
      have hmcoeff : MvPolynomial.coeff m (1 : MvPolynomial (Fin (latentNumVars M n)) ℚ) ≠ 0 := by
        exact MvPolynomial.mem_support_iff.mp (by simpa [Finset.prod_empty] using hm)
      have hm0 : m = 0 := by
        by_contra h
        have : MvPolynomial.coeff m (1 : MvPolynomial (Fin (latentNumVars M n)) ℚ) = 0 := by
          rw [MvPolynomial.coeff_one]
          split_ifs with hmz
          · exact (h hmz.symm).elim
          · rfl
        exact hmcoeff this
      exfalso
      simpa [hm0] using hx
  | @insert i S hi ih =>
      have hp : CoeffDisjoint.usesOnly (selConGadget M n i)
          ({selSlot M n i, conSlot M n i} : Set (Fin (latentNumVars M n))) :=
        selConGadget_usesOnly_selConPair M n i
      have hq : CoeffDisjoint.usesOnly (∏ j ∈ S, selConGadget M n j) (selConPairUnion M n S) := ih
      have hmul : CoeffDisjoint.usesOnly
          ((selConGadget M n i) * (∏ j ∈ S, selConGadget M n j))
          (({selSlot M n i, conSlot M n i} : Set (Fin (latentNumVars M n))) ∪ selConPairUnion M n S) :=
        CoeffDisjoint.usesOnly_mul hp hq
      simpa [Finset.prod_insert hi, selConPairUnion, hi, Set.union_assoc, Set.union_left_comm,
        Set.union_comm, Set.setOf_or] using hmul

/-- Sum of per-block witness monomials is supported in the corresponding union set. -/
theorem monomSupported_selConSum_on_set (M : DTM) (n : ℕ)
    (S : Finset (Fin (latentBaseVars M n))) :
    CoeffDisjoint.monomSupportedIn
      (∑ i ∈ S,
        ((Finsupp.single (selSlot M n i) (1 : ℕ)) + (Finsupp.single (conSlot M n i) (1 : ℕ))))
      (selConPairUnion M n S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro x hx
      simpa using hx
  | @insert i S hi ih =>
      have hmI : CoeffDisjoint.monomSupportedIn
          ((Finsupp.single (selSlot M n i) (1 : ℕ)) + (Finsupp.single (conSlot M n i) (1 : ℕ)))
          ({selSlot M n i, conSlot M n i} : Set (Fin (latentNumVars M n))) :=
        mono_selConPair_supported M n i
      have hmS : CoeffDisjoint.monomSupportedIn
          (∑ j ∈ S,
            ((Finsupp.single (selSlot M n j) (1 : ℕ)) + (Finsupp.single (conSlot M n j) (1 : ℕ))))
          (selConPairUnion M n S) := ih
      have hsum : CoeffDisjoint.monomSupportedIn
          (((Finsupp.single (selSlot M n i) (1 : ℕ)) + (Finsupp.single (conSlot M n i) (1 : ℕ)))
            + (∑ j ∈ S,
                ((Finsupp.single (selSlot M n j) (1 : ℕ)) + (Finsupp.single (conSlot M n j) (1 : ℕ)))))
          (({selSlot M n i, conSlot M n i} : Set (Fin (latentNumVars M n))) ∪ selConPairUnion M n S) :=
        CoeffDisjoint.monomSupportedIn_add hmI hmS
      simpa [Finset.sum_insert hi, selConPairUnion, hi, Set.union_assoc, Set.union_left_comm,
        Set.union_comm, Set.setOf_or, add_assoc] using hsum

/-- Iterated disjoint-support coefficient factorization for sel/con gadgets. -/
theorem coeff_selConProd_sumMono_on_set (M : DTM) (n : ℕ)
    (S : Finset (Fin (latentBaseVars M n))) :
    MvPolynomial.coeff
      (∑ i ∈ S,
        ((Finsupp.single (selSlot M n i) (1 : ℕ)) + (Finsupp.single (conSlot M n i) (1 : ℕ))))
      (∏ i ∈ S, selConGadget M n i)
    = ((-1 : ℚ) ^ S.card) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp
  | @insert i S hi ih =>
      have hp : CoeffDisjoint.usesOnly (selConGadget M n i)
          ({selSlot M n i, conSlot M n i} : Set (Fin (latentNumVars M n))) :=
        selConGadget_usesOnly_selConPair M n i
      have hq : CoeffDisjoint.usesOnly (∏ j ∈ S, selConGadget M n j)
          (selConPairUnion M n S) :=
        usesOnly_selConProd_on_set M n S
      have hdisj : Disjoint
          ({selSlot M n i, conSlot M n i} : Set (Fin (latentNumVars M n)))
          (selConPairUnion M n S) := by
        rw [Set.disjoint_left]
        intro x hxI hxS
        rcases hxS with ⟨j, hjS, hxJ⟩
        have hij : i ≠ j := by
          intro h
          exact hi (h ▸ hjS)
        exact (Set.disjoint_left.mp (selConPair_disjoint_of_ne M n hij) hxI hxJ)
      have hmA : CoeffDisjoint.monomSupportedIn
          ((Finsupp.single (selSlot M n i) (1 : ℕ)) + (Finsupp.single (conSlot M n i) (1 : ℕ)))
          ({selSlot M n i, conSlot M n i} : Set (Fin (latentNumVars M n))) :=
        mono_selConPair_supported M n i
      have hmB : CoeffDisjoint.monomSupportedIn
          (∑ j ∈ S,
            ((Finsupp.single (selSlot M n j) (1 : ℕ)) + (Finsupp.single (conSlot M n j) (1 : ℕ))))
          (selConPairUnion M n S) :=
        monomSupported_selConSum_on_set M n S
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      rw [CoeffDisjoint.coeff_mul_disjoint hp hq hdisj hmA hmB]
      rw [coeff_selConGadget_target_mono, ih]
      simp [pow_succ, hi, mul_comm, mul_left_comm, mul_assoc]

/-- Full-product coefficient identity at the canonical witness monomial. -/
theorem coeff_allSelConMono_selConSheet_eq_pow_neg_one (M : DTM) (n : ℕ) :
    MvPolynomial.coeff (allSelConMono M n) (selConSheet M n)
      = ((-1 : ℚ) ^ (latentBaseVars M n)) := by
  simpa [allSelConMono, selConSheet] using
    (coeff_selConProd_sumMono_on_set M n (Finset.univ : Finset (Fin (latentBaseVars M n))))

/-- In particular, the canonical sel/con witness coefficient is nonzero. -/
theorem coeff_allSelConMono_selConSheet_ne_zero (M : DTM) (n : ℕ) :
    MvPolynomial.coeff (allSelConMono M n) (selConSheet M n) ≠ 0 := by
  rw [coeff_allSelConMono_selConSheet_eq_pow_neg_one]
  exact pow_ne_zero _ (by norm_num)

/-- A selector-slot variable never appears in a mach-copy gadget. -/
theorem selSlot_not_mem_vars_machCopyGadget (M : DTM) (n : ℕ)
    (i j : Fin (latentBaseVars M n)) :
    selSlot M n j ∉ (machCopyGadget M n i).vars := by
  intro hsel
  have hsub := (MvPolynomial.vars_sub_subset
    (p := (1 : MvPolynomial (Fin (latentNumVars M n)) ℚ))
    (q := (X (machSlot M n i) * X (copySlot M n i) :
      MvPolynomial (Fin (latentNumVars M n)) ℚ)))
  have hprod : selSlot M n j ∈
      (X (machSlot M n i) * X (copySlot M n i) :
        MvPolynomial (Fin (latentNumVars M n)) ℚ).vars := by
    have hunion : selSlot M n j ∈
        (1 : MvPolynomial (Fin (latentNumVars M n)) ℚ).vars ∪
        (X (machSlot M n i) * X (copySlot M n i) :
          MvPolynomial (Fin (latentNumVars M n)) ℚ).vars := by
      simpa [machCopyGadget, Xmach, Xcopy] using hsub hsel
    have hnotC : selSlot M n j ∉ (1 : MvPolynomial (Fin (latentNumVars M n)) ℚ).vars := by
      simpa using (MvPolynomial.not_mem_vars_C (1 : ℚ) (selSlot M n j))
    exact (Finset.mem_union.mp hunion).resolve_left hnotC
  have hmul := (MvPolynomial.vars_mul (X (machSlot M n i)) (X (copySlot M n i))) hprod
  have hcases : selSlot M n j = machSlot M n i ∨ selSlot M n j = copySlot M n i := by
    simpa [MvPolynomial.vars_X, Finset.mem_union, Finset.mem_singleton] using hmul
  cases hcases with
  | inl h =>
      have : False := by
        simp [selSlot, machSlot, slot, Fin.ext_iff] at h
        omega
      exact this.elim
  | inr h =>
      have : False := by
        simp [selSlot, copySlot, slot, Fin.ext_iff] at h
        omega
      exact this.elim

/-- A selector-slot variable never appears in a copy-consistency gadget. -/
theorem selSlot_not_mem_vars_copyConGadget (M : DTM) (n : ℕ)
    (i j : Fin (latentBaseVars M n)) :
    selSlot M n j ∉ (copyConGadget M n i).vars := by
  intro hsel
  have hsub := (MvPolynomial.vars_sub_subset
    (p := (1 : MvPolynomial (Fin (latentNumVars M n)) ℚ))
    (q := (X (copySlot M n i) * X (conSlot M n i) :
      MvPolynomial (Fin (latentNumVars M n)) ℚ)))
  have hprod : selSlot M n j ∈
      (X (copySlot M n i) * X (conSlot M n i) :
        MvPolynomial (Fin (latentNumVars M n)) ℚ).vars := by
    have hunion : selSlot M n j ∈
        (1 : MvPolynomial (Fin (latentNumVars M n)) ℚ).vars ∪
        (X (copySlot M n i) * X (conSlot M n i) :
          MvPolynomial (Fin (latentNumVars M n)) ℚ).vars := by
      simpa [copyConGadget, Xcopy, Xcon] using hsub hsel
    have hnotC : selSlot M n j ∉ (1 : MvPolynomial (Fin (latentNumVars M n)) ℚ).vars := by
      simpa using (MvPolynomial.not_mem_vars_C (1 : ℚ) (selSlot M n j))
    exact (Finset.mem_union.mp hunion).resolve_left hnotC
  have hmul := (MvPolynomial.vars_mul (X (copySlot M n i)) (X (conSlot M n i))) hprod
  have hcases : selSlot M n j = copySlot M n i ∨ selSlot M n j = conSlot M n i := by
    simpa [MvPolynomial.vars_X, Finset.mem_union, Finset.mem_singleton] using hmul
  cases hcases with
  | inl h =>
      have : False := by
        simp [selSlot, copySlot, slot, Fin.ext_iff] at h
        omega
      exact this.elim
  | inr h =>
      have : False := by
        simp [selSlot, conSlot, slot, Fin.ext_iff] at h
        omega
      exact this.elim

/-- If a monomial support contains a selector slot, its coefficient in
`machCopySheet` is zero. -/
theorem coeff_machCopySheet_eq_zero_of_selSlot_support (M : DTM) (n : ℕ)
    (d : (Fin (latentNumVars M n)) →₀ ℕ)
    (hsupp : ∃ j : Fin (latentBaseVars M n), selSlot M n j ∈ d.support) :
    MvPolynomial.coeff d (machCopySheet M n) = 0 := by
  by_contra hcoeff
  have hmem : d ∈ (machCopySheet M n).support := MvPolynomial.mem_support_iff.mpr hcoeff
  obtain ⟨j, hj⟩ := hsupp
  have hvar : selSlot M n j ∈ (machCopySheet M n).vars :=
    (MvPolynomial.mem_vars _).mpr ⟨d, hmem, hj⟩
  have hprodSub := MvPolynomial.vars_prod (s := (Finset.univ : Finset (Fin (latentBaseVars M n))))
    (f := fun i => machCopyGadget M n i)
  have hUnion : selSlot M n j ∈
      (Finset.univ : Finset (Fin (latentBaseVars M n))).biUnion
        (fun i => (machCopyGadget M n i).vars) := hprodSub hvar
  rcases Finset.mem_biUnion.mp hUnion with ⟨i, -, hi⟩
  exact (selSlot_not_mem_vars_machCopyGadget M n i j) hi

/-- If a monomial support contains a selector slot, its coefficient in
`copyConSheet` is zero. -/
theorem coeff_copyConSheet_eq_zero_of_selSlot_support (M : DTM) (n : ℕ)
    (d : (Fin (latentNumVars M n)) →₀ ℕ)
    (hsupp : ∃ j : Fin (latentBaseVars M n), selSlot M n j ∈ d.support) :
    MvPolynomial.coeff d (copyConSheet M n) = 0 := by
  by_contra hcoeff
  have hmem : d ∈ (copyConSheet M n).support := MvPolynomial.mem_support_iff.mpr hcoeff
  obtain ⟨j, hj⟩ := hsupp
  have hvar : selSlot M n j ∈ (copyConSheet M n).vars :=
    (MvPolynomial.mem_vars _).mpr ⟨d, hmem, hj⟩
  have hprodSub := MvPolynomial.vars_prod (s := (Finset.univ : Finset (Fin (latentBaseVars M n))))
    (f := fun i => copyConGadget M n i)
  have hUnion : selSlot M n j ∈
      (Finset.univ : Finset (Fin (latentBaseVars M n))).biUnion
        (fun i => (copyConGadget M n i).vars) := hprodSub hvar
  rcases Finset.mem_biUnion.mp hUnion with ⟨i, -, hi⟩
  exact (selSlot_not_mem_vars_copyConGadget M n i j) hi

/-- `allSelConMono` contains selector-slot support (for any chosen base index). -/
theorem allSelConMono_selSlot_mem_support (M : DTM) (n : ℕ)
    (j : Fin (latentBaseVars M n)) :
    selSlot M n j ∈ (allSelConMono M n).support := by
  classical
  have hne : (allSelConMono M n) (selSlot M n j) ≠ 0 := by
    intro hz
    have hsum0 : (∑ i : Fin (latentBaseVars M n),
        (((Finsupp.single (selSlot M n i) (1 : ℕ) + Finsupp.single (conSlot M n i) (1 : ℕ))
            : (Fin (latentNumVars M n)) →₀ ℕ)
          (selSlot M n j))) = 0 := by
      simpa [allSelConMono, Finsupp.sum_apply] using hz
    have htermj : ((((Finsupp.single (selSlot M n j) (1 : ℕ) + Finsupp.single (conSlot M n j) (1 : ℕ))
          : (Fin (latentNumVars M n)) →₀ ℕ)
        (selSlot M n j)) = 0) :=
      (Finset.sum_eq_zero_iff.mp hsum0) j (by simp)
    have : (1 : ℕ) = 0 := by
      simpa [Finsupp.single_apply, selSlot, conSlot, slot, Fin.ext_iff] using htermj
    exact Nat.one_ne_zero this
  exact Finsupp.mem_support_iff.mpr hne

/-- Concrete `hmach` for the canonical witness monomial. -/
theorem coeff_allSelConMono_machCopySheet_eq_zero (M : DTM) (n : ℕ)
    (j : Fin (latentBaseVars M n)) :
    MvPolynomial.coeff (allSelConMono M n) (machCopySheet M n) = 0 :=
  coeff_machCopySheet_eq_zero_of_selSlot_support M n (allSelConMono M n)
    ⟨j, allSelConMono_selSlot_mem_support M n j⟩

/-- Concrete `hcopy` for the canonical witness monomial. -/
theorem coeff_allSelConMono_copyConSheet_eq_zero (M : DTM) (n : ℕ)
    (j : Fin (latentBaseVars M n)) :
    MvPolynomial.coeff (allSelConMono M n) (copyConSheet M n) = 0 :=
  coeff_copyConSheet_eq_zero_of_selSlot_support M n (allSelConMono M n)
    ⟨j, allSelConMono_selSlot_mem_support M n j⟩

/-- Degree lower bound for the canonical witness monomial at contradiction scale. -/
theorem allSelConMono_degree_gt_four_of_hn804 (M : DTM) (n : ℕ)
    (hn804 : n ≥ 2 ^ 804) :
    4 < ∑ i ∈ (allSelConMono M n).support, (allSelConMono M n) i := by
  classical
  let d := allSelConMono M n
  have himg_subset :
      Finset.image (selSlot M n) (Finset.univ : Finset (Fin (latentBaseVars M n))) ⊆ d.support := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
    exact allSelConMono_selSlot_mem_support M n i
  have hcard_ge_base : latentBaseVars M n ≤ d.support.card := by
    have hle := Finset.card_le_card himg_subset
    have hcard_img :
        (Finset.image (selSlot M n) (Finset.univ : Finset (Fin (latentBaseVars M n)))).card
          = (Finset.univ : Finset (Fin (latentBaseVars M n))).card := by
      exact Finset.card_image_of_injective (Finset.univ : Finset (Fin (latentBaseVars M n)))
        (selSlot_injective M n)
    -- rewrite card of `Fin.univ`
    simpa [hcard_img] using hle
  have hsum_ge_card : d.support.card ≤ ∑ i ∈ d.support, d i := by
    calc
      d.support.card = ∑ i ∈ d.support, (1 : ℕ) := by simp
      _ ≤ ∑ i ∈ d.support, d i := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))
  have hsum_ge_n : n ≤ ∑ i ∈ d.support, d i := by
    exact le_trans (latentBaseVars_ge_n M n) (le_trans hcard_ge_base hsum_ge_card)
  have h4_lt_n : 4 < n := by
    have hpow : 4 < 2 ^ 804 := by native_decide
    exact lt_of_lt_of_le hpow hn804
  exact lt_of_lt_of_le h4_lt_n hsum_ge_n

/-- Fully automatic route-2 contradiction trigger against `hViolMatches` at the
canonical witness, using only the scale assumption `n ≥ 2^804`. -/
theorem no_hViolMatches_of_allSelCon_witness_auto
    (hLeVar : ∀ (M : DTM) (n : ℕ),
      numVars M n (Nat.log 2 n) ≤ latentNumVars M n)
    (M : DTM) (n : ℕ)
    (hn804 : n ≥ 2 ^ 804) :
    ¬ (MvPolynomial.rename
      (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
      (violationPolyOf ℚ M n) = latentCompiledPoly M n) := by
  have hdeg : 4 < ∑ i ∈ (allSelConMono M n).support, (allSelConMono M n) i :=
    allSelConMono_degree_gt_four_of_hn804 M n hn804
  have hsel : MvPolynomial.coeff (allSelConMono M n) (selConSheet M n) ≠ 0 :=
    coeff_allSelConMono_selConSheet_ne_zero M n
  have hbase_pos : 0 < latentBaseVars M n := by
    have hpow_pos : 0 < 2 ^ 804 := by norm_num
    have hn_pos : 0 < n := lt_of_lt_of_le hpow_pos hn804
    exact lt_of_lt_of_le hn_pos (latentBaseVars_ge_n M n)
  let j : Fin (latentBaseVars M n) := ⟨0, hbase_pos⟩
  have hmach : MvPolynomial.coeff (allSelConMono M n) (machCopySheet M n) = 0 :=
    coeff_allSelConMono_machCopySheet_eq_zero M n j
  have hcopy : MvPolynomial.coeff (allSelConMono M n) (copyConSheet M n) = 0 :=
    coeff_allSelConMono_copyConSheet_eq_zero M n j
  exact no_hViolMatches_of_allSelCon_witness hLeVar M n hdeg hsel hmach hcopy

/-- Refutation form of `hVerVanish` at one instance from a positive NP-side
multilinear rank lower bound for `tseitinPoly`. -/
theorem no_verifierTransport_vanish_of_mlLower
    (hLeVar : ∀ (M : DTM) (n : ℕ),
      numVars M n (Nat.log 2 n) ≤ latentNumVars M n)
    (hLeWitness : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      npNumVars n ≤ numVars M n (Nat.log 2 n))
    (M : DTM) (n : ℕ)
    (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804)
    (hNPml : mlBlockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
      (tseitinPoly ℚ n) ≥ n ^ (Nat.log 2 n / 4)) :
    MvPolynomial.rename
      (Function.comp (fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent
        (witnessInclusion M n (hLeWitness M n hn hn804)))
      (tseitinPoly ℚ n) ≠ 0 := by
  intro hvanish
  have ht0 : tseitinPoly ℚ n = 0 :=
    (verifierTransport_vanish_iff_tseitin_zero hLeVar hLeWitness M n hn hn804).mp hvanish
  have hr0 : mlBlockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
      (tseitinPoly ℚ n) = 0 := by
    simpa [ht0] using
      (mlBlockedSpdpRank_zero (F := ℚ) (B := tseitinPartition n)
        (κ := Nat.log 2 n) (ℓ := Nat.log 2 n))
  have hn_pos : 0 < n := by
    have h4 : (4 : ℕ) ≤ n := le_trans (by simp) hn
    exact lt_of_lt_of_le (by decide : 0 < 4) h4
  have hpow_pos : 0 < n ^ (Nat.log 2 n / 4) := Nat.pow_pos hn_pos
  have hle0 : n ^ (Nat.log 2 n / 4) ≤ 0 := by simpa [hr0] using hNPml
  exact (lt_irrefl _ (lt_of_lt_of_le hpow_pos hle0)).elim
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

/-- Concrete mapped-domination constructor from partition-compatibility.

This is the semantic form needed by coarsening: if equal compiled blocks stay
in equal latent blocks under `toLatent`, then the pullback latent partition is
coarser than the compiled partition, yielding the required rank inequality. -/
theorem bridgeRankDominationMapped_of_partitionCompatible (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (B : FullToLatentBridge M n)
    (hCompat : bridgePartitionCompatible M n B) :
    bridgeRankDominationMapped M n h_le B := by
  let Bc := compiledPartition M n
  let Bp := pullbackPartition (latentPartition M n) B.toLatent
  have hcoarsen : mlBlockedSpdpRank Bp (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
      ≤ mlBlockedSpdpRank Bc (Nat.log 2 n) (Nat.log 2 n)
          (fullCompiledPoly ℚ M n h_le) := by
    -- pullback latent partition is coarser than compiled under compatibility
    refine mlBlockedSpdpRank_coarsen ℚ Bc Bp (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le) ?_
    intro i j hij
    simpa [Bp] using hCompat i j hij
  have hrename := mlBlockedSpdpRank_rename_le B.toLatent B.inj
      (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
  unfold bridgeRankDominationMapped
  exact le_trans (by simpa [mapFullToLatentPoly, Bp] using hrename) hcoarsen

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

/-- Counterexample-schema negation for the explicit pointwise block-map claim.
If one index violates `compiled.assign = latent.assign ∘ toLatent`, then the
global pointwise condition cannot hold. -/
theorem not_globalAssignToLatent_of_counterexample
    (hLeVar : ∀ (M : DTM) (n : ℕ),
      numVars M n (Nat.log 2 n) ≤ latentNumVars M n)
    (M : DTM) (n : ℕ)
    (hcex : ∃ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i ≠
        (latentPartition M n).assign
          ((fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent i)) :
    ¬ (∀ i : Fin (numVars M n (Nat.log 2 n)),
      (compiledPartition M n).assign i =
        (latentPartition M n).assign
          ((fullToLatentBridgeOfLe M n (hLeVar M n)).toLatent i)) := by
  intro hAll
  rcases hcex with ⟨i, hi⟩
  exact hi (hAll i)

/-- Global packaged Step-(2) mapped-domination constructor from semantic
partition-compatibility (equal compiled blocks map to equal latent blocks). -/
theorem globalMapDom_of_globalPartitionCompatible
    (hLeVar : ∀ (M : DTM) (n : ℕ),
      numVars M n (Nat.log 2 n) ≤ latentNumVars M n)
    (hLeWitness : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hCompat : ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      bridgePartitionCompatible M n (fullToLatentBridgeOfLe M n (hLeVar M n))) :
    ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      bridgeRankDominationMapped M n (hLeWitness M n hn hn804)
        (fullToLatentBridgeOfLe M n (hLeVar M n)) := by
  intro M n hn hn804
  exact bridgeRankDominationMapped_of_partitionCompatible M n
    (hLeWitness M n hn hn804)
    (fullToLatentBridgeOfLe M n (hLeVar M n))
    (hCompat M n hn hn804)

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

/-- Named compiled-side profile-compression obligation list (skeleton) for
building the core32 full-rank theorem.

This structure is intentionally theorem-agnostic: populate fields with concrete
compiled/profile lemmas as they are proved, then discharge
`hPcore32_of_compiledProfileObligations` below. -/
structure CompiledProfileObligations (M : DTM) (n : ℕ) where
  profileCountBound : ∃ m, m ≥ 4 ∧ ∀ R, Nat.choose (R + m) m ≤ (R + 1) ^ m
  withinProfileDimBound : ∃ D, D ≥ 1 ∧ ∀ k d, d ≥ 1 →
      Nat.choose (k + d - 1) (d - 1) ≤ (k + 1) ^ (d - 1)
  assemblyBound : Prop

/-- Bridge theorem skeleton: reduce the monolithic core32 P-side theorem to a
named compiled-profile obligation bundle + one derivation theorem.

Use this to keep the remaining gap explicit and modular instead of a single
opaque `hPcore32` assumption. -/
theorem hPcore32_of_compiledProfileObligations
    (hObligations : ∀ (M : DTM) (n : ℕ), n ≥ 32 → CompiledProfileObligations M n)
    (hDerive : ∀ (M : DTM) (n : ℕ),
      n ≥ 32 →
      (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) →
      CompiledProfileObligations M n →
      mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n h_le) ≤ n ^ 160) :
    ∀ (M : DTM) (n : ℕ),
      n ≥ 32 →
      (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) →
      mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n h_le) ≤ n ^ 160 := by
  intro M n hn32 h_le
  exact hDerive M n hn32 h_le (hObligations M n hn32)

/-- Concrete instantiation helper: fill the first two compiled-profile
obligations from proved `ProfileCompression` lemmas, leaving only the
compiler-assembly obligation as an explicit input. -/
def compiledProfileObligations_of_profileCompression
    (hAssembly : ∀ (M : DTM) (n : ℕ), n ≥ 32 → Prop) :
    ∀ (M : DTM) (n : ℕ), n ≥ 32 → CompiledProfileObligations M n := by
  intro M n hn32
  refine {
    profileCountBound := ProfileCompression.profile_count_bound,
    withinProfileDimBound := ProfileCompression.within_profile_dim_bound,
    assemblyBound := hAssembly M n hn32
  }

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

/-- Named sub-implication scaffold for proving compiled-side `hDerive`.

This decomposes the derivation into three explicit implication stages:
1) profile-count contribution,
2) within-profile contribution,
3) final assembly to rank160.

Each field is a theorem target to be filled by concrete compiled/profile lemmas.
-/
structure CompiledDerivationScaffold (M : DTM) (n : ℕ) (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) where
  fromProfileCount :
    CompiledProfileObligations M n → Prop
  fromWithinProfile :
    CompiledProfileObligations M n → Prop
  finalAssembly :
    CompiledProfileObligations M n →
    mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le) ≤ n ^ 160

/-- Scaffold-to-derivation bridge: once the three compiled sub-implications are
proved (packaged as `CompiledDerivationScaffold`), `hDerive` follows directly. -/
theorem hDerive_of_compiledDerivationScaffold
    (M : DTM) (n : ℕ)
    (hn32 : n ≥ 32)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hOb : CompiledProfileObligations M n)
    (hScaf : CompiledDerivationScaffold M n h_le)
    (hStep1 : hScaf.fromProfileCount hOb)
    (hStep2 : hScaf.fromWithinProfile hOb) :
    mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le) ≤ n ^ 160 :=
  hScaf.finalAssembly hOb

/-- Canonical scaffold choice: use obligation fields directly as Step-1/Step-2
premises, and leave only the final assembly inequality as a parameter. -/
def compiledDerivationScaffold_default
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hFinal : CompiledProfileObligations M n →
      mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n h_le) ≤ n ^ 160) :
    CompiledDerivationScaffold M n h_le where
  fromProfileCount := fun _ =>
    ∃ m, m ≥ 4 ∧ ∀ R, Nat.choose (R + m) m ≤ (R + 1) ^ m
  fromWithinProfile := fun _ =>
    ∃ D, D ≥ 1 ∧ ∀ k d, d ≥ 1 → Nat.choose (k + d - 1) (d - 1) ≤ (k + 1) ^ (d - 1)
  finalAssembly := hFinal

/-- New target (Step-1): under the default scaffold, profile-count contribution
is discharged directly from the obligation bundle. -/
theorem compiled_step1_profileCount_default
    (M : DTM) (n : ℕ)
    (hn32 : n ≥ 32)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hOb : CompiledProfileObligations M n)
    (hFinal : CompiledProfileObligations M n →
      mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n h_le) ≤ n ^ 160) :
    (compiledDerivationScaffold_default M n h_le hFinal).fromProfileCount hOb :=
  hOb.profileCountBound

/-- New target (Step-2): under the default scaffold, within-profile contribution
is discharged directly from the obligation bundle. -/
theorem compiled_step2_withinProfile_default
    (M : DTM) (n : ℕ)
    (hn32 : n ≥ 32)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hOb : CompiledProfileObligations M n)
    (hFinal : CompiledProfileObligations M n →
      mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n h_le) ≤ n ^ 160) :
    (compiledDerivationScaffold_default M n h_le hFinal).fromWithinProfile hOb :=
  hOb.withinProfileDimBound

/-- Global packaged bridge: if you can provide the scaffold + step proofs at
each `(M,n,h_le)`, you obtain concrete `hPcore32`. -/
theorem hPcore32_of_compiledScaffold
    (hObligations : ∀ (M : DTM) (n : ℕ), n ≥ 32 → CompiledProfileObligations M n)
    (hScaf : ∀ (M : DTM) (n : ℕ)
      (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)),
      CompiledDerivationScaffold M n h_le)
    (hStep1 : ∀ (M : DTM) (n : ℕ)
      (hn32 : n ≥ 32)
      (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)),
      (hScaf M n h_le).fromProfileCount (hObligations M n hn32))
    (hStep2 : ∀ (M : DTM) (n : ℕ)
      (hn32 : n ≥ 32)
      (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)),
      (hScaf M n h_le).fromWithinProfile (hObligations M n hn32)) :
    ∀ (M : DTM) (n : ℕ),
      n ≥ 32 →
      (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) →
      mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n h_le) ≤ n ^ 160 := by
  intro M n hn32 h_le
  exact hDerive_of_compiledDerivationScaffold M n hn32 h_le
    (hObligations M n hn32)
    (hScaf M n h_le)
    (hStep1 M n hn32 h_le)
    (hStep2 M n hn32 h_le)

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
