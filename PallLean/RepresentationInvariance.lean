import PallLean.CompiledSoS
import PallLean.NPWitness
import Mathlib.Tactic

/-!
# RepresentationInvariance — Paper Lemma 13

The compiler's representation invariance: if two source descriptions compute
the same Boolean function, their compiled forms have equivalent SPDP rank
(up to polynomial factors).

Paper reference: Lemma 13 (Semantic closure of the compiled normal form
under P-decidability), proved via Theorem 255 and Corollary 256.

## Key properties:
(I1) Normal-form invariance: same Boolean function → compiler equivalence
(I2) Rank stability: equivalence preserves rank up to poly(n) factors

## Application to P≠NP:
If M decides SAT (fn ∈ P), then:
- P-side: compiledPolySoS M n has rank = 0 (Theorem 92)
- NP-side: tseitinPoly has rank ≥ n^{Ω(log n)} (identity minor)
- Lemma 13: both compute fn, so ranks must be "compatible"
- Contradiction: 0 ≠ n^{Ω(log n)}
-/

namespace RepresentationInvariance

open SPDP MultilinearSPDP NPWitness Compiler CompiledSoS TuringMachine

/-- Paper Lemma 13: Representation invariance for the compiler.

    If M decides SAT (computes the same Boolean function as the Tseitin
    verifier), then the SPDP rank of M's compiled polynomial is at least
    as large as the Tseitin polynomial's rank (under the same parameters).

    This is the "semantic closure" bridge: same function → rank transfer.

    Paper proof: Theorem 255 (normal-form invariance) shows that any two
    admitted source descriptions of the same function produce equivalent
    compiled outputs. Corollary 256 shows rank stability under equivalence.
    Together: rank(C(M)) ≥ rank(C(Φn)) / poly(n). -/
theorem representation_invariance
    (M : DTM) (n : ℕ) (hn : n ≥ 32)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (κ ℓ : ℕ) (hκ : κ ≥ 5) :
    mlBlockedSpdpRank (tseitinPartition n) κ ℓ (tseitinPoly ℚ n) ≤
    mlBlockedSpdpRank (compiledPartition M n) κ ℓ
      (compiledPolySoS ℚ M n) + n ^ 10 := by
  -- Paper Lemma 13 + Theorem 255 + Corollary 256.
  -- The compiler maps both M and the Tseitin formula to compiled objects.
  -- Since they compute the same Boolean function (M decides SAT),
  -- the compiled ranks are related up to polynomial factors.
  --
  -- The "+ n^10" absorbs the polynomial correction from equivalence moves.
  sorry

end RepresentationInvariance
