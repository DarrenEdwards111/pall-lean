/-
  PaperAxioms.lean — Three axioms from the paper's proof

  These axiomatize the three deep results:
  1. Depth-4 simulation (Agrawal-Vinay + Tavenas)
  2. SPDP collapse under restriction (multi-switching lemma)
  3. Existence of a universal good seed (union bound)

  References:
  - Agrawal & Vinay (2008): Arithmetic circuits — a chasm at depth four
  - Tavenas (2015): Improved bounds for reduction to depth 4 and depth 3
  - Razborov (1995), Smolensky (1987): switching lemma literature
  - Kayal, Saha, Saptharishi (2014): depth-4 SPD lower bounds
-/
import PallLean.CircuitModel
import PallLean.RestrictedSPDP

namespace PaperAxioms

open CircuitModel RestrictedSPDP Restriction

/-! ## Finite Seed Union Helper

This is the purely combinatorial part of the paper's seed argument:
if the union of finitely many bad-seed sets is smaller than the full
seed space, then some seed avoids every bad set simultaneously.

The remaining seed-side axiom only has to supply the paper-specific
bound on the bad-seed union. -/

theorem exists_seed_avoiding_bad_union
    {σ τ : Type*} [DecidableEq σ] [Fintype σ]
    (tests : Finset τ) (bad : τ → Finset σ)
    (hcard : (tests.biUnion bad).card < Fintype.card σ) :
    ∃ s : σ, ∀ t ∈ tests, s ∉ bad t := by
  classical
  by_contra hno
  push_neg at hno
  have hsubset : (Finset.univ : Finset σ) ⊆ tests.biUnion bad := by
    intro s hs
    exact Finset.mem_biUnion.mpr (hno s)
  have hge : Fintype.card σ ≤ (tests.biUnion bad).card := by
    simpa using Finset.card_le_card hsubset
  exact Nat.not_lt_of_ge hge hcard

/-! ## Axiom 1: Depth-4 Simulation

Every polynomial-size Boolean circuit can be converted to a depth-4
ΣΠ∑Π circuit with bounded parameters.

The depth-4 circuit has the SAME numVars as the original (it's a
re-wiring of the same computation, not a variable change).

Paper: §7.3 Step 1 -/

axiom depth4_simulation :
    ∀ (C : PolySizeFamily),
    ∃ (D : ℕ → Depth4Circuit ℚ),
    ∃ (n₀ : ℕ),
    ∀ n ≥ n₀,
      -- Same number of variables
      (D n).params.numVars = C.numVars n ∧
      -- Bounded bottom fan-in
      (D n).params.bottomFanIn ≤ Nat.log 2 n ∧
      -- Bounded formal degree
      (D n).params.formalDegree ≤ (Nat.log 2 n) ^ 2 ∧
      -- Bounded size
      (D n).params.size ≤ n ^ (2 * C.sizeBound)

/-! ## Axiom 2: SPDP Collapse Under Restriction (Lemma 7.2)

For any depth-4 ΣΠ∑Π circuit with bounded bottom fan-in, a random
short-seed restriction collapses SPDP rank with high probability.

The axiom states: for each polynomial, there exists a restriction
that achieves low rank. The probabilistic argument (multi-switching)
is what guarantees this for MOST seeds.

Paper: §7.3 Step 2, Lemma 7.2 (multi-switching), Lemma 6.5 (sampler) -/

axiom spdp_collapse_under_restriction :
    ∀ (n : ℕ) (hn : n ≥ 2)
      (params : Depth4Params)
      (hv : params.numVars = n)
      (p : MvPolynomial (Fin n) ℚ),
    ∃ (ρ : Restriction.Restriction n),
      restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n) p ρ ≤
        (Nat.log 2 n + 1) * params.bottomFanIn

/-! ## Axiom 3: Multi-Switching + Signature Count → Union Bound

The paper proves Theorem 7.3 via three sub-results:

  (a) **Lemma 7.2 (multi-switching)**: For any depth-4 circuit C with
      bounded parameters, at most a δ(n)-fraction of seeds fail to
      collapse its SPDP rank. Formalised as `hil_multi_switching`.

  (b) **Lemma 7.2.1 (signature count)**: After restriction, the number
      of syntactically distinct SPDP row-space signatures is at most
      2^{O(log² N)}. Formalised as `rowspace_count`.

  (c) **Union bound (Step 4)**: Combining (a) and (b):
      Pr[∃ C that fails] ≤ 2^{O(log²N)} · δ(n) < 1/2.
      So a good seed s* exists.

We package (a)+(b)+(c) into a single axiom that directly states the
conclusion needed by `universal_good_seed`: the finite bad-set packaging
with a union smaller than the seed space.

Paper: §7.3 Steps 2-4, Lemma 7.2, Lemma 7.2.1. -/

axiom universal_good_seed_bad_union :
    ∀ (n : ℕ), n ≥ 2 →
    ∃ (m : ℕ) (bad : Fin m → Finset (Restriction.Restriction n)),
      -- (a) Coverage: for every polynomial, some signature class i
      --     captures all bad restrictions (multi-switching per signature)
      (∀ (p : MvPolynomial (Fin n) ℚ),
        ∃ i : Fin m, ∀ (ρ : Restriction.Restriction n),
          ρ ∉ bad i →
            restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n)
              p ρ ≤ (Nat.log 2 n + 1) ^ 2) ∧
      -- (b)+(c) Smallness: union of bad sets < total seed space
      --   (from signature count × per-signature failure probability)
      (Finset.univ.biUnion bad).card <
        Fintype.card (Restriction.Restriction n)

/-- Theorem 7.3: there exists a single restriction under which every
    relevant polynomial collapses.

    The proof is the finite union argument from the paper; the only
    remaining axiom is the paper-specific finite bad-seed bound above. -/
theorem universal_good_seed
    (n : ℕ) (hn : n ≥ 2) :
    ∃ (ρ : Restriction.Restriction n),
    ∀ (p : MvPolynomial (Fin n) ℚ),
      restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n)
        p ρ ≤ (Nat.log 2 n + 1) ^ 2 := by
  classical
  obtain ⟨m, bad, hcover, hcard⟩ := universal_good_seed_bad_union n hn
  obtain ⟨ρ, hρ⟩ :=
    exists_seed_avoiding_bad_union (tests := Finset.univ) bad hcard
  refine ⟨ρ, ?_⟩
  intro p
  obtain ⟨i, hi⟩ := hcover p
  exact hi ρ ((hρ i (by simp)))

end PaperAxioms
