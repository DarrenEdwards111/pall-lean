import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3WeightGain
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PWeightExtends

/-!
# The restriction-measure interface — isolating independence into two named hypotheses

The first audit brick from `SCOPE_LAYER3_EXPANDER_RESTRICTIONS.md`: the Layer-2 switching/survivor
proof uses independence of the `p`-biased measure `pweight = ∏_v (…)` in **exactly two places** — the
per-label weight ratio (`pweight_le_ratio_pow`) and the conditional mass (`pweight_sum_extends`). This
file packages those two facts as the fields of an abstract `RestrictionMeasure`, with `pweight` as the
canonical instance, so the holographic count can later be re-proved over *any* measure satisfying the
interface (the decoder/injectivity is measure-free and needs no change).

* `RestrictionMeasure n p` — a weight `μ` with `nonneg`, **(M1)** the marginal ratio
  `μ σ ≤ (2p/(1-p))^s · μ τ` (freeing `s` coords), and **(M2)** the extension-box mass
  `∑_{extBox τ} μ = ((1-p)/2)^(n-stars τ)`.
* `pweightMeasure` — the `p`-biased product measure instantiates it.

**CORRECTION (supersedes the optimistic framing in `SCOPE_LAYER3_EXPANDER_RESTRICTIONS.md`):**
the switching *count* uses only `nonneg` + **(M1)** — but (M1) is applied at `s = pathLen`, the **full
descent-path length**, which the count itself bounds in `Icc s n` (so `s ≤ pathLen ≤ n`). It is **NOT**
a `≤ s`-support fact, so a small-`k` `k`-wise-independent measure does **not** satisfy it; the ratio
needs the product structure over the whole path (up to `n` coords). Separately, **(M2)** holding for
*all* `τ` pins every conditional mass by Möbius inversion and so **forces `μ = pweight`** — the exact
interface admits the product measure only. Genuine derandomisation would need to re-handle the rare
long-path contribution (each `r^{pathLen}`-suppressed) by a `k`-wise moment/tail bound, not a drop-in
instance — that is open. What *does* hold: the decoder/injectivity is measure-free.

This is a faithful Layer-2 refactoring (the abstract count genuinely generalises and recovers the
original); no lower bound, no capstone, no new assumption — `pweight` satisfies every field.  The
`s`-wise substitution it was meant to enable does **not** go through as first hoped.  Not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **A restriction-measure interface.**  Bundles the *only two* places the Layer-2 switching count
uses independence of the underlying measure: the marginal **ratio** (M1) and the extension-box **mass**
(M2).  Any `μ` satisfying these drives the holographic count, whose decoder is measure-free.  `pweight`
is the canonical product instance.  (See the header CORRECTION: the exact interface in fact forces
`μ = pweight`, and (M1) is used over full descent paths, not `≤ s`-support — so this does not yield a
genuine `k`-wise instance.) -/
structure RestrictionMeasure (n : ℕ) (p : ℚ) where
  /-- The underlying weight. -/
  toFun : (Fin n → Option Bool) → ℚ
  /-- The weight is nonnegative. -/
  nonneg : ∀ ρ, 0 ≤ toFun ρ
  /-- **(M1) marginal ratio:** if `σ` frees at least `s` coordinates beyond `τ`, its weight is at most
  `(2p/(1-p))^s` times `τ`'s.  (In the count this is applied at `s = pathLen`, the *full* descent-path
  length `∈ [s, n]` — NOT a `≤ s`-support fact, so a small-`k` `k`-wise measure does not satisfy it.) -/
  ratio : ∀ {σ τ : Fin n → Option Bool}, stars τ ≤ stars σ → ∀ {s : ℕ}, s ≤ stars σ - stars τ →
    toFun σ ≤ (2 * p / (1 - p)) ^ s * toFun τ
  /-- **(M2) extension-box mass:** the total weight of all restrictions extending `τ`.  The only
  *global* product fact; a `k`-wise/expander measure would supply a concentration substitute here. -/
  sumExtends : ∀ τ : Fin n → Option Bool,
    ∑ σ ∈ extBox τ, toFun σ = ((1 - p) / 2) ^ (n - stars τ)

namespace RestrictionMeasure

instance {p : ℚ} : CoeFun (RestrictionMeasure n p) (fun _ => (Fin n → Option Bool) → ℚ) :=
  ⟨toFun⟩

end RestrictionMeasure

/-- **The `p`-biased product measure instantiates the interface.**  Its three fields are exactly the
existing `pweight` lemmas: `pweight_nonneg`, `pweight_le_ratio_pow` (M1), `pweight_sum_extends` (M2).
This certifies the interface is faithful — nothing in the count needs `pweight` beyond these. -/
def pweightMeasure {p : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp3 : 3 * p ≤ 1) :
    RestrictionMeasure n p where
  toFun := pweight p
  nonneg := pweight_nonneg hp0 hp1
  ratio := by intro σ τ hst s hs; exact pweight_le_ratio_pow hp0 hp3 hst hs
  sumExtends := pweight_sum_extends p

@[simp] theorem pweightMeasure_apply {p : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp3 : 3 * p ≤ 1)
    (ρ : Fin n → Option Bool) : (pweightMeasure hp0 hp1 hp3).toFun ρ = pweight p ρ := rfl

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.pweightMeasure
