import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTraceSchemaCapstone

/-!
# Narrowing the super-additive crux

`TraceSchemaCapstone` isolated the residual `P` vs `NP` crux as a `SuperAdditiveWitness`: a
generically-sound trace measure `μ` that is **not** `PolySizeDominated` yet hard on SAT.  This file
sharpens what such a `μ` must look like, by showing that the *capped* class — `PolySizeDominated`,
whose hardness always reduces to time — is a rich **algebra**:

* closed under addition, multiplication, constants, and pointwise domination
  (`polySizeDominated_add/mul/const/mono`);
* contains every measure bounded by a polynomial in the **number of trace rows**
  (`rowCount_poly_polySizeDominated`, since `rows ≤ traceSize`).

Consequently a super-additive witness escapes this entire algebra
(`witness_not_in_psd_algebra`): it is not any `+`/`×`/polynomial combination of size-dominated
measures, and — the sharp new constraint — **it cannot be bounded by any polynomial in the number
of configurations it inspects** (`witness_superpoly_in_rows`).  So the crux's cross-row
correlation must be genuinely *global* (super-polynomial in row count), not any bounded-locality
aggregate (pairwise, `k`-local, …), all of which are capped.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SuperAdditiveNarrow

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics (NPObs)
open PallLean.Paper93.DeepMath.PathB.ObserverInvariantBridge (InvHard)
open PallLean.Paper93.DeepMath.PathB.SeparationNoGo
open PallLean.Paper93.DeepMath.PathB.TraceMeasureSchema
open PallLean.Paper93.DeepMath.PathB.PolyCeiling
open PallLean.Paper93.DeepMath.PathB.TraceSchemaCapstone

/-! ## The capped class is an algebra -/

/-- Constants are capped. -/
theorem polySizeDominated_const (c : ℕ) : PolySizeDominated (fun _ => c) :=
  ⟨c, 0, fun tr => by simp⟩

/-- Pointwise domination preserves cappedness. -/
theorem polySizeDominated_mono (μ ν : List (List Bool) → ℕ) (hle : ∀ tr, μ tr ≤ ν tr)
    (hν : PolySizeDominated ν) : PolySizeDominated μ := by
  obtain ⟨c, k, h⟩ := hν
  exact ⟨c, k, fun tr => (hle tr).trans (h tr)⟩

/-- The capped class is closed under addition. -/
theorem polySizeDominated_add (μ ν : List (List Bool) → ℕ)
    (hμ : PolySizeDominated μ) (hν : PolySizeDominated ν) :
    PolySizeDominated (fun tr => μ tr + ν tr) := by
  obtain ⟨c₁, k₁, h₁⟩ := hμ
  obtain ⟨c₂, k₂, h₂⟩ := hν
  refine ⟨c₁ + c₂, max k₁ k₂, fun tr => ?_⟩
  have hb : (1 : ℕ) ≤ traceSize tr + 1 := Nat.le_add_left 1 _
  have e1 : (traceSize tr + 1) ^ k₁ ≤ (traceSize tr + 1) ^ max k₁ k₂ :=
    Nat.pow_le_pow_right hb (le_max_left k₁ k₂)
  have e2 : (traceSize tr + 1) ^ k₂ ≤ (traceSize tr + 1) ^ max k₁ k₂ :=
    Nat.pow_le_pow_right hb (le_max_right k₁ k₂)
  calc μ tr + ν tr
      ≤ c₁ * (traceSize tr + 1) ^ k₁ + c₂ * (traceSize tr + 1) ^ k₂ :=
        Nat.add_le_add (h₁ tr) (h₂ tr)
    _ ≤ c₁ * (traceSize tr + 1) ^ max k₁ k₂ + c₂ * (traceSize tr + 1) ^ max k₁ k₂ := by
        gcongr
    _ = (c₁ + c₂) * (traceSize tr + 1) ^ max k₁ k₂ := by ring

/-- The capped class is closed under multiplication. -/
theorem polySizeDominated_mul (μ ν : List (List Bool) → ℕ)
    (hμ : PolySizeDominated μ) (hν : PolySizeDominated ν) :
    PolySizeDominated (fun tr => μ tr * ν tr) := by
  obtain ⟨c₁, k₁, h₁⟩ := hμ
  obtain ⟨c₂, k₂, h₂⟩ := hν
  refine ⟨c₁ * c₂, k₁ + k₂, fun tr => ?_⟩
  calc μ tr * ν tr
      ≤ (c₁ * (traceSize tr + 1) ^ k₁) * (c₂ * (traceSize tr + 1) ^ k₂) :=
        Nat.mul_le_mul (h₁ tr) (h₂ tr)
    _ = c₁ * c₂ * (traceSize tr + 1) ^ (k₁ + k₂) := by rw [pow_add]; ring

/-! ## Row-count bounds are capped -/

/-- The number of trace rows is at most the trace size. -/
theorem rows_le_traceSize (tr : List (List Bool)) : tr.length ≤ traceSize tr := by
  rw [traceSize]; exact Nat.le_add_left _ _

/-- **Any measure bounded by a polynomial in the number of rows is capped.**  This subsumes every
bounded-locality aggregate: pairwise (`rows²`), `k`-local (`rows^k`), etc. -/
theorem rowCount_poly_polySizeDominated (μ : List (List Bool) → ℕ) (c k : ℕ)
    (h : ∀ tr, μ tr ≤ c * (tr.length + 1) ^ k) : PolySizeDominated μ := by
  refine ⟨c, k, fun tr => (h tr).trans ?_⟩
  have : (tr.length + 1) ^ k ≤ (traceSize tr + 1) ^ k :=
    Nat.pow_le_pow_left (Nat.add_le_add_right (rows_le_traceSize tr) 1) k
  exact Nat.mul_le_mul_left c this

/-! ## The witness escapes the algebra -/

/-- **Not capped ⟹ super-polynomial in the row count.**  A measure that is not `PolySizeDominated`
cannot be bounded by any polynomial in the number of configurations it inspects — otherwise
`rowCount_poly_polySizeDominated` would cap it.  So its super-polynomial value must come from
genuinely *global* cross-row correlation, not from any aggregate over a bounded number of rows. -/
theorem not_psd_imp_superpoly_rows (μ : List (List Bool) → ℕ) (hNP : ¬ PolySizeDominated μ) :
    ¬ ∃ c k : ℕ, ∀ tr, μ tr ≤ c * (tr.length + 1) ^ k := by
  rintro ⟨c, k, h⟩
  exact hNP (rowCount_poly_polySizeDominated μ c k h)

/-- **The narrowing, bundled.**  A super-additive witness `μ` (if one exists) is simultaneously:
generically sound, hard on SAT, not capped by any polynomial in the trace size, and — the new
constraint — not capped by any polynomial in the row count.  The residual `P` vs `NP` crux thus
requires cross-configuration correlation that is unbounded in locality. -/
theorem superAdditive_narrowing (SATV : NPObs) (h : SuperAdditiveWitness SATV) :
    ∃ μ, InvGenSound (traceInv μ) ∧ InvHard SATV (traceInv μ)
      ∧ ¬ PolySizeDominated μ
      ∧ ¬ ∃ c k : ℕ, ∀ tr, μ tr ≤ c * (tr.length + 1) ^ k := by
  obtain ⟨μ, hG, hNP, hH⟩ := h
  exact ⟨μ, hG, hH, hNP, not_psd_imp_superpoly_rows μ hNP⟩

end PallLean.Paper93.DeepMath.PathB.SuperAdditiveNarrow
