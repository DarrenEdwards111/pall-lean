import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModGateCrossLayer

/-!
# Any symmetric top over cross-layer SYM∘AND subcircuits is multi-count (PROVED)

The structural side of the RS approx→exact decode.  The Beigel–Tarui / Razborov–Smolensky exact
recovery decodes the target as a **symmetric top** (threshold / majority count) over `k` low-degree
approximants.  This brick proves that structure is always a `HasMultiSymRep`: **any** Boolean function
of the outputs of `k` `SYM∘AND` subcircuits (each on its own bottom layer) is a joint function of the
`k` layer counts.

  `topGate_crossLayer_hasMultiSymRep` — for any `top : (Fin k → Bool) → Bool` and any family of
  `HasSymAndRep` subcircuits `g`, the composite `x ↦ top (fun i => g i x)` is `HasMultiSymRep`.

This **subsumes** the cross-layer `MOD` case (`hasMultiSymRep_modGate_crossLayer`) and covers the RS
decode's `majority` / `threshold` top: the decode is structurally a `k`-count symmetric function, which
(via `miniBT_collapse_size`) collapses to a single-count `SYM∘AND` at the multiplicative tower size.

## What is proved (clean axioms, no `sorry`)

* `topGate_crossLayer_hasMultiSymRep` — any symmetric top over cross-layer `SYM∘AND` subcircuits is
  `HasMultiSymRep`.
* `majorityDecode_hasMultiSymRep` — the RS majority/threshold decode (`> half of the `g i` are `1``) is
  `HasMultiSymRep` (the structural half of approx→exact).

## Honest scope — the barrier is NOT here

This is the **structure** of the decode: it is multi-count symmetric, exactly as composition predicts.
It does **not** achieve the decode's *correctness*.  The genuine open content — turning `1−ε` RS
approximants into a *majority-correct-everywhere* family so the decode is **exact** — is the
amplification step, which works for prime modulus (`AC⁰[p]`) but **provably fails for composite
modulus** (`ACC⁰[m]`): that is the Razborov–Smolensky / `ApproxToExactCount` barrier, and it is **not**
discharged here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SymTopCrossLayer

open PallLean.Paper93.DeepMath.PathB.ACC0SymAndComposition
open PallLean.Paper93.DeepMath.PathB.ACC0Mod6SymAndDepth2 (satCount)
open PallLean.Paper93.DeepMath.PathB.ACC0ModGateCrossLayer (HasMultiSymRep)

variable {n : ℕ}

/-- **Any symmetric top over cross-layer `SYM∘AND` subcircuits is multi-count (proved).**  For any
`top : (Fin k → Bool) → Bool` and any family `g` of `HasSymAndRep` subcircuits (each on its own bottom
layer), `x ↦ top (fun i => g i x)` is a joint function of the `k` layer counts. -/
theorem topGate_crossLayer_hasMultiSymRep {k : ℕ} {g : Fin k → (Fin n → Bool) → Bool}
    (top : (Fin k → Bool) → Bool) (hg : ∀ i, HasSymAndRep (g i)) :
    HasMultiSymRep (fun x => top (fun i => g i x)) := by
  choose t supp sym hsym using hg
  exact ⟨k, t, supp, fun c => top (fun i => sym i (c i)), fun x => by simp only [hsym]⟩

/-- **The RS majority / threshold decode is multi-count (proved).**  The threshold-count decode
`x ↦ decide (k < 2 · #{i | g i x})` over a family of `HasSymAndRep` approximants is `HasMultiSymRep` —
the structural form of the Beigel–Tarui approx→exact symmetric decode. -/
theorem majorityDecode_hasMultiSymRep {k : ℕ} {g : Fin k → (Fin n → Bool) → Bool}
    (hg : ∀ i, HasSymAndRep (g i)) :
    HasMultiSymRep
      (fun x => decide (k < 2 * (Finset.univ.filter (fun i => g i x = true)).card)) :=
  topGate_crossLayer_hasMultiSymRep
    (fun b => decide (k < 2 * (Finset.univ.filter (fun i => b i = true)).card)) hg

/-!
**Decode structure proved.**  Any symmetric top (including majority / threshold) over cross-layer
`SYM∘AND` subcircuits is `HasMultiSymRep` — the decode is structurally multi-count symmetric (collapsing
to single-count `SYM∘AND` via `miniBT_collapse_size`, at the multiplicative tower size).  The barrier —
achieving a *majority-correct-everywhere* family so the decode is exact, which **fails for composite
modulus** (Razborov–Smolensky / `ApproxToExactCount`) — is **not** discharged here.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0SymTopCrossLayer

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymTopCrossLayer.topGate_crossLayer_hasMultiSymRep
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SymTopCrossLayer.majorityDecode_hasMultiSymRep
