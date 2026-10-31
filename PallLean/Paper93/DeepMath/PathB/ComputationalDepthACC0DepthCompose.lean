import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ResidueObserver

/-!
# Depth composition: a top over observed subcircuits is searchable (product boundary)

The exact symmetric gates (`…ACC0SymmetricExact`) compose across depth in the observer framework: a top gate over
`k` subcircuits, each observed by a small statistic, is observed by the **product** statistic (`observed_top_pi`), so
SAT-searchable once the product of the subcircuit boundaries is `< 2^n`.  This is the depth-composition law — it
iterates to any depth (each subcircuit may itself be such a composition).

```
top(sub₁,…,sub_k),  subᵢ observed by ≤ cᵢ cells   ⇒   top(...) observed by ≤ ∏ cᵢ cells.
```

## What is proved (clean axioms, no `sorry`)

* `depth_compose_searchable` — a top over `k` observed subcircuits with `∏ᵢ |Sᵢ| < 2^n` is SAT-searchable in `< 2^n`
  (joint statistic = the product of the subcircuit statistics).

## Honest scope — why this is composition but not the YBT size bound

The boundary here is the **product** `∏ᵢ cᵢ` of the layer boundaries — *exponential* in the number of subcircuits.
That is the naive composition: it composes correctly at any depth, but the product blows up.  The whole point of
Yao–Beigel–Tarui is replacing this multiplicative blow-up by the **additive** degree composition of the polynomial
method (degree adds across `∧`/`∨`, so a depth-`d` circuit has polylog degree and hence quasipolynomially many
monomial-`AND`s — `…ACC0ToAgreeDegree`).  That additive/quasipoly control is the open structural step, and it is
*approximate* (RS); the *exact* quasipoly depth-composition (true YBT) is the wall.  So this file gives the composition
law and the honest product boundary; the quasipoly refinement is what remains.  Still the cell/observer model; nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0DepthCompose

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver

variable {n : ℕ}

set_option maxHeartbeats 1000000

/-- **The depth-composition law (proved): a top over `k` observed subcircuits is SAT-searchable in `< 2^n` when the
product of their boundaries is `< 2^n`.**  The joint statistic is the product of the per-subcircuit statistics
(`observed_top_pi`); the boundary is `∏ᵢ |Sᵢ|` (the *product* — see the honest-scope note). -/
theorem depth_compose_searchable {k : ℕ} {S : Fin k → Type}
    [∀ i, Fintype (S i)]
    (sub : Fin k → (Fin n → Bool) → Bool) (stat : ∀ i, (Fin n → Bool) → S i)
    (hf : ∀ i, ObservedBy (sub i) (stat i)) (top : (Fin k → Bool) → Bool)
    (hreg : (∏ i, Fintype.card (S i)) < 2 ^ n) :
    ∃ g : (∀ i, S i) → Bool,
      (Satisfiable (fun x => top (fun i => sub i x)) ↔
          ∃ s ∈ Finset.univ.image (fun x => fun i => stat i x), g s = true)
        ∧ (Finset.univ.image (fun x => fun i => stat i x)).card < 2 ^ n := by
  obtain ⟨g, hg⟩ := observed_top_pi sub stat hf top
  exact ⟨g, observed_sat_iff g hg, lt_of_le_of_lt (observed_pi_cellCount_le stat) hreg⟩

end PallLean.Paper93.DeepMath.PathB.ACC0DepthCompose

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DepthCompose.depth_compose_searchable
