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
