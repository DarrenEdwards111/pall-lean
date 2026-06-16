import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SymAndComposition

/-!
# Restricted mini-Beigel–Tarui: the two-count collapse holds *exactly* — the wall is size, not impossibility

In `…ACC0SymAndComposition` we isolated the composition wall: cross-layer `AND`/`OR` of two `SYM∘AND` functions lands
in a **joint two-count** representation, and the open question (`MiniBTCollapse`) was whether such a joint
representation collapses back to a single `SYM∘AND`.  We there guessed the exact collapse "too strong / false".

**That guess was wrong, and this file corrects it.**  The two-count collapse is *exactly* provable, by a **mixed-radix
encoding**: since the second count `c₂ = satCount s₂` is always `≤ t₂` (it counts a subset of `t₂` gates), choosing the
radix `D = t₂+1` lets a *single* count
\[ c^\star \;=\; D\cdot c_1 + c_2 \]
recover the pair via `c₁ = c^\star / D`, `c₂ = c^\star \% D`.  And `c^\star` is itself an achievable `AND`-count: the
achievable counts are closed under **addition** (append layers) and **integer scaling** (replicate each gate `D` times).
So the joint two-count observer collapses to a single-count `SYM∘AND` observer — exactly, no approximation.

**Why this does not solve `ACC⁰`.**  The collapse pays a **multiplicative** size blow-up: the new layer has
`t₁·(t₂+1) + t₂` gates (a *product* of the two sizes).  One composition step is fine, but iterating over circuit depth
`d` compounds the product into a **tower** — `≫` quasipolynomial.  *This* is the real Beigel–Tarui difficulty: not that
composition is impossible, but that the exact mixed-radix blow-up is super-multiplicative over depth, which is exactly
why the genuine theorem keeps size quasipolynomial via probabilistic polynomials instead of exact encoding.

## What is proved (clean axioms, no `sorry`)

* **`satCountF`** (sum form of the `AND`-count) with its algebra: **`satCountF_sumElim`** (additive under layer append),
  **`satCountF_replicate`** (`= k · count` under `k`-fold gate replication), **`satCountF_le_card`** (`≤` gate count).
* **`miniBT_two_count_collapse`** — every joint two-count representation collapses to a single `SYM∘AND` (the
  mixed-radix encoding); hence **`miniBTCollapse_holds : MiniBTCollapse n`** — the socket of `…ACC0SymAndComposition`
  is **discharged**, not assumed.
* **`hasSymAndRep_and`** / **`hasSymAndRep_or`** — therefore `SYM∘AND` (with *no* size bound) is **unconditionally**
  closed under `AND`/`OR` (and `NOT`, already proved).  The count dimension that cross-layer composition raised does
  collapse back.

## Honest scope

The collapse and the closures are *proved*, exactly.  What is **not** proved — and is the genuine open content — is
the collapse with a **quasipolynomial size bound surviving circuit depth**: the exact encoding here is multiplicative
and explodes over `ω(1)` depth, so the global quasipolynomial `SYM∘AND` representation of a whole `ACC⁰` circuit
(`composite_BT_degree`, socketed in `…ACC0CompositeBTTarget`) still requires the probabilistic-polynomial machinery.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0MiniBTTwoCount

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0Mod6SymAndDepth2
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0SymAndComposition

variable {n : ℕ}

/-! ## The sum form of the `AND`-count and its algebra -/

/-- **The `AND`-count over any finite gate-index type**, as a sum of `0/1` gate indicators. -/
def satCountF {ι : Type*} [Fintype ι] (supp : ι → Finset (Fin n)) (x : Fin n → Bool) : ℕ :=
  ∑ j, if monoAND (supp j) x = true then 1 else 0

/-- For a `Fin`-indexed layer, the sum form agrees with the `Finset.card` form `satCount`. -/
theorem satCount_eq_satCountF {t : ℕ} (supp : Fin t → Finset (Fin n)) (x : Fin n → Bool) :
    satCount supp x = satCountF supp x := by
  unfold satCount satCountF
  exact card_filter _ _

/-- **Append additivity (proved): the count over a concatenated layer is the sum of the counts.** -/
theorem satCountF_sumElim {ι κ : Type*} [Fintype ι] [Fintype κ]
    (s1 : ι → Finset (Fin n)) (s2 : κ → Finset (Fin n)) (x : Fin n → Bool) :
    satCountF (Sum.elim s1 s2) x = satCountF s1 x + satCountF s2 x := by
  unfold satCountF
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]

/-- **Replication scaling (proved): replicating each gate `k`-fold multiplies the count by `k`.** -/
theorem satCountF_replicate {ι : Type*} [Fintype ι] (s1 : ι → Finset (Fin n)) (k : ℕ)
    (x : Fin n → Bool) :
    satCountF (fun p : ι × Fin k => s1 p.1) x = k * satCountF s1 x := by
  unfold satCountF
  have key : ∀ i : ι, (∑ _c : Fin k, (if monoAND (s1 i) x = true then 1 else 0))
      = k * (if monoAND (s1 i) x = true then 1 else 0) := fun i => by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  calc (∑ p : ι × Fin k, if monoAND (s1 p.1) x = true then 1 else 0)
      = ∑ i : ι, ∑ _c : Fin k, (if monoAND (s1 i) x = true then 1 else 0) := by
        rw [Fintype.sum_prod_type]
    _ = ∑ i : ι, k * (if monoAND (s1 i) x = true then 1 else 0) :=
        Finset.sum_congr rfl (fun i _ => key i)
    _ = k * ∑ i : ι, (if monoAND (s1 i) x = true then 1 else 0) := by rw [Finset.mul_sum]

/-- **The count never exceeds the number of gates (proved).** -/
theorem satCountF_le_card {ι : Type*} [Fintype ι] (supp : ι → Finset (Fin n)) (x : Fin n → Bool) :
    satCountF supp x ≤ Fintype.card ι := by
  unfold satCountF
  calc ∑ j, (if monoAND (supp j) x = true then 1 else 0)
      ≤ ∑ _j : ι, 1 := Finset.sum_le_sum (fun j _ => by split <;> simp)
    _ = Fintype.card ι := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]

/-! ## The two-count collapse, exactly -/

/-- **Restricted mini-Beigel–Tarui (proved): the two-count joint observer collapses to a single `SYM∘AND`.**  By the
mixed-radix encoding `c⋆ = (t₂+1)·c₁ + c₂` over the layer `(s₁ replicated t₂+1 times) ++ s₂`: `c₂ ≤ t₂ < t₂+1` so
`c₁ = c⋆ / (t₂+1)` and `c₂ = c⋆ % (t₂+1)`, recovering the pair from the single count. -/
theorem miniBT_two_count_collapse {F : (Fin n → Bool) → Bool} (h : HasBinarySymRep F) :
    HasSymAndRep F := by
  obtain ⟨t1, t2, s1, s2, j, hF⟩ := h
  -- the encoded layer over `(Fin t1 × Fin (t2+1)) ⊕ Fin t2`
  let se : (Fin t1 × Fin (t2 + 1)) ⊕ Fin t2 → Finset (Fin n) :=
    Sum.elim (fun p => s1 p.1) s2
  -- the encoded count is the mixed-radix value `(t2+1)·c₁ + c₂`
  have hcount : ∀ x, satCountF se x = (t2 + 1) * satCountF s1 x + satCountF s2 x := by
    intro x
    show satCountF (Sum.elim (fun p : Fin t1 × Fin (t2 + 1) => s1 p.1) s2) x = _
    rw [satCountF_sumElim, satCountF_replicate]
  -- the low digit `c₂` is below the radix
  have hc2 : ∀ x, satCountF s2 x < t2 + 1 := by
    intro x
    have := satCountF_le_card s2 x
    rw [Fintype.card_fin] at this
    omega
  -- transport the encoded layer to a `Fin`-indexed family
  let e : Fin (Fintype.card ((Fin t1 × Fin (t2 + 1)) ⊕ Fin t2))
      ≃ ((Fin t1 × Fin (t2 + 1)) ⊕ Fin t2) := (Fintype.equivFin _).symm
  refine ⟨_, fun jx => se (e jx), fun s => j (s / (t2 + 1)) (s % (t2 + 1)), fun x => ?_⟩
  -- the `Fin`-layer count equals the encoded count
  have hsc : satCount (fun jx => se (e jx)) x = satCountF se x := by
    rw [satCount_eq_satCountF]
    exact Equiv.sum_comp e (fun i => if monoAND (se i) x = true then 1 else 0)
  rw [hF x, satCount_eq_satCountF s1 x, satCount_eq_satCountF s2 x, hsc, hcount x]
  dsimp only
  rw [Nat.mul_add_div (show 0 < t2 + 1 by omega), Nat.mul_add_mod_self_left,
    Nat.div_eq_of_lt (hc2 x), Nat.mod_eq_of_lt (hc2 x), add_zero]

/-- **The `…ACC0SymAndComposition` socket is discharged (proved): `MiniBTCollapse` holds.**  The exact two-count
collapse is a theorem, not a hypothesis — correcting the earlier guess that the exact form was too strong. -/
theorem miniBTCollapse_holds : MiniBTCollapse n :=
  fun _ h => miniBT_two_count_collapse h

/-! ## Unconditional closure of `SYM∘AND` under `AND` / `OR` -/

/-- **`SYM∘AND` is unconditionally closed under `AND` (proved).**  The count dimension that cross-layer composition
raised collapses back, with no size bound imposed. -/
theorem hasSymAndRep_and {F G : (Fin n → Bool) → Bool}
    (hF : HasSymAndRep F) (hG : HasSymAndRep G) :
    HasSymAndRep (fun x => F x && G x) :=
  symAndRep_closed_under_and_of_miniBT miniBTCollapse_holds hF hG

/-- **`SYM∘AND` is unconditionally closed under `OR` (proved).** -/
theorem hasSymAndRep_or {F G : (Fin n → Bool) → Bool}
    (hF : HasSymAndRep F) (hG : HasSymAndRep G) :
    HasSymAndRep (fun x => F x || G x) :=
  symAndRep_closed_under_or_of_miniBT miniBTCollapse_holds hF hG

/-! ## The size blow-up — where the real wall is -/

/-- **The collapse is multiplicative in size (proved): the encoded layer has `t₁·(t₂+1) + t₂` gates.**  A single
two-count collapse costs a *product* of the two layer sizes — fine once, but compounding this over circuit depth `d`
yields a tower, far above quasipolynomial.  This is the genuine Beigel–Tarui difficulty (kept quasipolynomial only via
probabilistic polynomials), not any impossibility of composition. -/
theorem miniBT_collapse_size (t1 t2 : ℕ) :
    Fintype.card ((Fin t1 × Fin (t2 + 1)) ⊕ Fin t2) = t1 * (t2 + 1) + t2 := by
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]

end PallLean.Paper93.DeepMath.PathB.ACC0MiniBTTwoCount

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MiniBTTwoCount.satCountF_sumElim
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MiniBTTwoCount.satCountF_replicate
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MiniBTTwoCount.miniBT_two_count_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MiniBTTwoCount.miniBTCollapse_holds
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MiniBTTwoCount.hasSymAndRep_and
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MiniBTTwoCount.miniBT_collapse_size
