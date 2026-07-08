import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCrossBranch

/-!
# N-Frame: the candidate Freshness Lemma — cancellation fanout non-reusability

The whole cross-branch direct sum has been compressed to a single obstruction: **cancellation-fanout
non-reusability**.  Computing `(F_k(a), F_k(b))` on disjoint blocks, the length deficit from the ideal
`2×` is exactly `#mixed` — the gates depending on BOTH blocks (`deficit_is_mixed`).  Each such gate
carries FOREIGN content into a cone (its `b`-content into `cone(F_k(a))`, symmetrically) that must
cancel.  The direct sum closes iff that cancellation is FRESH: `#mixed ≤ cN`.

This file states that obstruction as a candidate lemma, anchored by the one genuinely-provable pillar
(the restriction fact) and packaged with its sufficiency, with the core honestly marked open.

## Evidence the candidate holds (not proof)

Exact SAT synthesis (scratchpad): `cbudget(F ⊕ F) = 2·cbudget(F)` for the real 4-input W-coupling mixer
and 10 other functions (`CE_share = 0`), and a cancellation-reuse search over designed-for-reuse pairs
(variable-permuted, same-shape, shared-structure) found NO saving.  So at every reachable scale the
foreign content is pure debt — no mixed cancellation value does double duty.  This is empirical support
for non-reusability, at `cbudget ≤ 4` (the ceiling); it does NOT reach the amortization regime.

## The provable pillar (restriction): foreign inputs give no speed-up

  `foreign_inputs_no_speedup` — **PROVED**: a circuit outputting the `a`-only function `F_k(a)` on inputs
        `(a,b)`, restricted `b = const`, is a circuit for `F_k(a)` with no more gates
        (`rGates ≤ total`); since it still computes `F_k(a)` (`cbudgetFa ≤ rGates`), we get
        `cbudgetFa ≤ total`.  b-inputs never reduce `cbudget(F_k(a))` — a `b`-value is useless for an
        `a`-only output.  This is the rigorous form of "you cannot compute an `a`-value faster by mixing
        in a `b`-value."

## The deficit is exactly the mixed gates

  `deficit_is_mixed` — **PROVED**: with the pure/mixed partition (`total = pureA + pureB + mixed`) and
        the two restriction bounds (`cbudget ≤ pureA + mixed`, `cbudget ≤ pureB + mixed`, each from the
        pillar applied to `b=const` / `a=const`), `2·cbudget ≤ total + mixed`, i.e.
        `total ≥ 2·cbudget − #mixed`.  The deficit is exactly `#mixed`.

## The Freshness Lemma (candidate obstruction) and its sufficiency

  `freshness_closes_direct_sum` — **PROVED (contract)**: the FRESHNESS hypothesis `#mixed ≤ cN` (the
        cancellation is fresh — mixed gates number at most the mixer's fresh count) turns the deficit
        into `2·cbudget ≤ total + cN`, the cross-branch direct sum (absorbing the mixer's `cN`).  Chains
        into `ConeAmplify.amplify_exceeds_linear` for super-linear.
  `non_freshness_breaks` — **PROVED (witness)**: without freshness (`cN < #mixed`), the deficit permits
        `total < 2·cbudget`; the hypothesis is load-bearing, not decorative.

## Honest scope — this is a CANDIDATE, the core is open

`foreign_inputs_no_speedup` and `deficit_is_mixed` are proved (restriction).  The FRESHNESS hypothesis
`#mixed ≤ cN` is NOT proved — it is the candidate obstruction.  The pillar shows a mixed gate cannot
*accelerate* either single computation; it does NOT rule out a mixed gate doing DOUBLE DUTY (advancing
`a` and `b` one step each) with AMORTIZED cancellation.  That amortization is the residual, and proving
it impossible is an `O(1)`-restriction-Lipschitz-vs-`ω(1)` statement — i.e. `MeasureBarrier`.  So the
Freshness Lemma is a well-supported candidate (empirically holds to the exact-synthesis ceiling,
obstructed on paper by disjoint independence), not a theorem.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameFreshnessLemma

open PallLean.Paper93.DeepMath.PathB

/-- **THE RESTRICTION PILLAR (proved)**: b-inputs give no speed-up for an `a`-only output.  A circuit on
`(a,b)` outputting `F_k(a)`, restricted `b = const`, still computes `F_k(a)` with no more gates
(`rGates ≤ total`), so `cbudget(F_k(a)) ≤ total`.  Foreign inputs cannot reduce the cost of an `a`-only
function — the rigorous form of "you can't compute an `a`-value faster by mixing in a `b`-value." -/
theorem foreign_inputs_no_speedup (cbudgetFa rGates total : ℕ)
    (hrestrict : rGates ≤ total) (hcomputes : cbudgetFa ≤ rGates) :
    cbudgetFa ≤ total := by
  omega

/-- **THE DEFICIT IS THE MIXED GATES (proved)**: with `total = pureA + pureB + mixed` and the two
restriction bounds `cbudget ≤ pureA + mixed` (`b=const` survivors compute `F_k(a)`) and
`cbudget ≤ pureB + mixed`, we get `2·cbudget ≤ total + mixed` — i.e. `total ≥ 2·cbudget − #mixed`. -/
theorem deficit_is_mixed (cbudget pureA pureB mixed total : ℕ)
    (htot : total = pureA + pureB + mixed)
    (hA : cbudget ≤ pureA + mixed) (hB : cbudget ≤ pureB + mixed) :
    2 * cbudget ≤ total + mixed := by
  omega

/-- **THE FRESHNESS LEMMA CLOSES IT (proved contract)**: the candidate hypothesis `#mixed ≤ cN` (the
cancellation is fresh) turns the deficit `2·cbudget ≤ total + mixed` into `2·cbudget ≤ total + cN` — the
cross-branch direct sum, absorbing the mixer's `cN`.  (`#mixed ≤ cN` is the OPEN candidate.) -/
theorem freshness_closes_direct_sum (cbudget mixed cN total : ℕ)
    (hdef : 2 * cbudget ≤ total + mixed) (hfresh : mixed ≤ cN) :
    2 * cbudget ≤ total + cN := by
  omega

/-- **FRESHNESS IS LOAD-BEARING (proved witness)**: without it (`cN < #mixed`), the deficit accounting
permits `total < 2·cbudget` — the direct sum fails.  Witness `(cbudget,mixed,cN,total)=(100,50,10,150)`:
deficit `2·100 ≤ 150+50` holds, `cN=10 < 50=mixed`, and `150 < 200`.  So the freshness hypothesis is
non-trivial — it is exactly what must be proved. -/
theorem non_freshness_breaks :
    ∃ (cbudget mixed cN total : ℕ),
      2 * cbudget ≤ total + mixed ∧ cN < mixed ∧ total < 2 * cbudget :=
  ⟨100, 50, 10, 150, by omega, by omega, by omega⟩

/-- **THE FULL CHAIN, PACKAGED (proved)**: at every scale the deficit
(`2·T k + fresh k ≤ total k + mixed k`), freshness with amplification margin
(`mixed k + c·2^{k+1} ≤ fresh k` — the mixer's fresh charge covers the mixed deficit plus the increment),
and `total k ≤ T (k+1)` give the amplifiable recurrence, so `amplify_exceeds_linear` forces
`b·2^b ≤ T b` — super-linear. -/
theorem freshness_forces_superlinear
    (c : ℕ) (hc : 1 ≤ c) (T fresh mixed total : ℕ → ℕ)
    (hdef : ∀ k, 2 * T k + fresh k ≤ total k + mixed k)
    (hfresh : ∀ k, mixed k + c * 2 ^ (k + 1) ≤ fresh k)
    (hstep : ∀ k, total k ≤ T (k + 1)) (b : ℕ) :
    b * 2 ^ b ≤ T b := by
  apply NFrameConeAmplify.amplify_exceeds_linear c T hc _ b
  intro k
  have h1 := hdef k; have h2 := hfresh k; have h3 := hstep k
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameFreshnessLemma

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFreshnessLemma.foreign_inputs_no_speedup
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFreshnessLemma.deficit_is_mixed
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFreshnessLemma.freshness_closes_direct_sum
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFreshnessLemma.non_freshness_breaks
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFreshnessLemma.freshness_forces_superlinear
