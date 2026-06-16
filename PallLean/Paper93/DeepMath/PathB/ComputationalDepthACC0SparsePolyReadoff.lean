import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CircuitSubstitution
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SparseCounting
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BeigelTaruiSparsity

/-!
# The read-off — a sparse low-degree polynomial gives a sub-`2ⁿ` cube count (wiring the counting socket)

The circuit-substitution assembly (`…ACC0CircuitSubstitution`) produces, for a constant-depth circuit, a low-degree
polynomial approximant.  This file wires that approximant to the existing counting machinery: a degree-`≤ D` polynomial
over the Boolean cube, written in its sparse `SYM∘AND` (monomial) form
\[ \mathrm{sparsePoly}\,\mathcal{S}\,c\,(x) \;=\; \sum_{S\in\mathcal{S}} c_S \cdot [\,\mathrm{monoAND}_S(x)\,], \]
has a **cube sum that is itself a sparse sum** — `∑ₓ sparsePoly = ∑_{S} c_S · 2^{n-|S|}` (`sparse_cube_sum`) — over at
most `(n+1)^D` features (`beigelTarui_monomial_count_le`).  So the acceptance count of the circuit (`∑ₓ` of its `{0,1}`
approximant), naively `2^n` work, is computed from quasipolynomially many feature weights — the Williams `ACC⁰`-`SAT`
speedup input.

## What is proved (clean axioms, no `sorry`)

* **`sparsePoly`** — the sparse `SYM∘AND` / monomial form of a low-degree polynomial.
* **`sparsePoly_cube_sum`** — `∑ₓ sparsePoly 𝒮 c x = ∑_{S∈𝒮} c S · 2^{n-|S|}` (the cube sum is a *sparse* sum, no
  enumeration of `2^n` inputs).
* **`sparse_features_le`** — `𝒮 ⊆ lowDegMonomials n D ⇒ 𝒮.card ≤ (n+1)^D` (quasipolynomially many features).
* **`sparse_readoff`** — the bridge: for a degree-`≤ D` sparse polynomial, the cube sum equals a sum of `≤ (n+1)^D`
  feature weights.  This is the sub-`2^n` counting input.

## The remaining socket

* **`sparse_readoff_to_NEXP_not_ACC0`** — *given* the sparse low-degree representation (the read-off of the substituted
  probabilistic polynomial — the one piece still requiring the `MvPolynomial` multilinearisation of
  `…ACC0CircuitSubstitution`'s approximant), the counting + Williams cash-out yields `¬ NEXPHasACC0Circuits`
  (re-exporting `…ACC0RankRouteFrontier`).

## Honest scope

The cube-sum identity and the quasipolynomial feature count are *proved* (reusing the counting kernel and the
Beigel–Tarui count).  The one remaining gap is the multilinearisation that turns the circuit-substitution approximant
(`…ACC0CircuitSubstitution.circuit_error_bound`) into this explicit sparse `monoAND` form; that is the named socket.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SparsePolyReadoff

open scoped Classical BigOperators
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0SparseCounting
open PallLean.Paper93.DeepMath.PathB.ACC0BeigelTaruiSparsity
open PallLean.Paper93.DeepMath.PathB.Layer3

variable {n : ℕ}

/-- The sparse `SYM∘AND` (monomial) form of a low-degree polynomial over the Boolean cube: a weighted sum of `AND`
features `monoAND_S` indexed by a sparse family `𝒮` of supports. -/
def sparsePoly {R : Type*} [CommRing R] (𝒮 : Finset (Finset (Fin n))) (c : Finset (Fin n) → R)
    (x : Fin n → Bool) : R :=
  ∑ S ∈ 𝒮, c S * (if monoAND S x = true then (1 : R) else 0)

/-- **The cube sum of a sparse polynomial is a sparse sum (proved): `∑ₓ sparsePoly = ∑_{S} c_S · 2^{n-|S|}`.**  No
enumeration of the `2^n` inputs — the sum collapses to one term per `AND` feature (the sparse cube-sum kernel). -/
theorem sparsePoly_cube_sum {R : Type*} [CommRing R] (𝒮 : Finset (Finset (Fin n)))
    (c : Finset (Fin n) → R) :
    (∑ x : Fin n → Bool, sparsePoly 𝒮 c x) = ∑ S ∈ 𝒮, c S * (2 : R) ^ (n - S.card) :=
  sparse_cube_sum 𝒮 c

/-- **The feature count is quasipolynomial (proved): `𝒮 ⊆ lowDegMonomials n D ⇒ 𝒮.card ≤ (n+1)^D`.** -/
theorem sparse_features_le (𝒮 : Finset (Finset (Fin n))) {D : ℕ}
    (h𝒮 : 𝒮 ⊆ lowDegMonomials n D) :
    𝒮.card ≤ (n + 1) ^ D :=
  le_trans (Finset.card_le_card h𝒮) (beigelTarui_monomial_count_le n D)

/-- **The read-off bridge (proved): a degree-`≤ D` sparse polynomial's cube sum is a sum of `≤ (n+1)^D` feature
weights.**  The acceptance count `∑ₓ sparsePoly`, naively `2^n` work, is computed from quasipolynomially many feature
weights `c_S · 2^{n-|S|}` — the sub-`2^n` `ACC⁰`-`SAT` counting input that Williams's argument consumes. -/
theorem sparse_readoff {R : Type*} [CommRing R] (𝒮 : Finset (Finset (Fin n)))
    (c : Finset (Fin n) → R) {D : ℕ} (h𝒮 : 𝒮 ⊆ lowDegMonomials n D) :
    (∑ x : Fin n → Bool, sparsePoly 𝒮 c x) = ∑ S ∈ 𝒮, c S * (2 : R) ^ (n - S.card)
      ∧ 𝒮.card ≤ (n + 1) ^ D :=
  ⟨sparsePoly_cube_sum 𝒮 c, sparse_features_le 𝒮 h𝒮⟩

/-- **The read-off cash-out (proved conditional).**  *Given* the sparse low-degree representation `readoff` (the
multilinearised read-off of the circuit-substitution approximant — the one remaining open piece) and the standard
Route-B inputs, the counting + Williams collapse yields `¬ NEXPHasACC0Circuits`. -/
theorem sparse_readoff_to_NEXP_not_ACC0
    (RSRep ACC0SatSpeedup NEXPHasACC0Circuits Collapse : Prop)
    (readoff : RSRep)
    (counting : RSRep → ACC0SatSpeedup)
    (williams : ACC0SatSpeedup → NEXPHasACC0Circuits → Collapse)
    (hierarchy : ¬ Collapse) :
    ¬ NEXPHasACC0Circuits :=
  ACC0RankRouteFrontier.composite_route_to_NEXP_not_ACC0
    RSRep ACC0SatSpeedup NEXPHasACC0Circuits Collapse readoff counting williams hierarchy

end PallLean.Paper93.DeepMath.PathB.ACC0SparsePolyReadoff

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SparsePolyReadoff.sparsePoly_cube_sum
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SparsePolyReadoff.sparse_features_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SparsePolyReadoff.sparse_readoff
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SparsePolyReadoff.sparse_readoff_to_NEXP_not_ACC0
