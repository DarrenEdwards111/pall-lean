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

/-- Step-2 semantic constructor: build global bridge domination from the two
concrete sub-obligations highlighted in the proof plan:
(1) mapped domination, and (2) polynomial identification. -/
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
