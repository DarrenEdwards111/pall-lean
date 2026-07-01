import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSPDPDeterminantLike

/-!
# Toward a dynamic SPDP invariant: the genuine `+`-gate bound, and why "max-rank" cost fails

Two honest facts about a *dynamic* SPDP measure built from `SPDP.spdpRank`.

**The genuine additive gate bound** (the low-side per-transition lemma of a dynamic SPDP):

  `spdpRank_add_le` — `spdpRank κ ℓ (p + q) ≤ spdpRank κ ℓ p + spdpRank κ ℓ q`.

`spdpRank` is subadditive: an `+` gate at most adds the two operands' ranks (because `∂_S(p+q) = ∂_S p + ∂_S q`, so
the derivative span of `p+q` lies in the sum of the two spans).

**Why "max `spdpRank` across a construction trace" does NOT fix the `∏Xᵢ` weakness** (a proved no-go):

The natural idea — measure a trace `1 → X₀ → X₀X₁ → ⋯ → ∏Xᵢ` by the *maximum* `spdpRank` of its intermediate
states — cannot make `∏Xᵢ` cheap, because the **final state `∏Xᵢ` is itself in the trace** and already has
exponential rank (`spdpRank_fullProd_choose_ge`):

  `fullProd_dynamicTraceCost_ge` — any trace whose states include `∏Xᵢ` has `dynamicTraceCost ≥ C(n, κ)`.

So the max-across-states cost inherits the exponential *final* rank; it is `≥` the static rank, never below it.  A
dynamic SPDP that separates easy `∏Xᵢ` from hard targets must therefore measure something *non-accumulative* (per-step
transfer / trace length / a restricted rank), **not** the maximum accumulated derivative-span rank.  This is a
concrete correction to the naive "dynamic SPDP = max rank across states" proposal.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

open MvPolynomial SPDP Module

variable {n : ℕ} {F : Type*} [Field F]

/-- The SPDP subspace of a sum lies in the sum of the two SPDP subspaces (`∂_S(p+q) = ∂_S p + ∂_S q`). -/
theorem spdpSubspace_add_le (κ ℓ : ℕ) (p q : MvPolynomial (Fin n) F) :
    spdpSubspace κ ℓ (p + q) ≤ spdpSubspace κ ℓ p ⊔ spdpSubspace κ ℓ q := by
  rw [spdpSubspace, Submodule.span_le]
  rintro _ ⟨S, m, hSlen, hmdeg, rfl⟩
  rw [SetLike.mem_coe, iterDerivList_add, mul_add]
  refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · exact Submodule.subset_span ⟨S, m, hSlen, hmdeg, rfl⟩
  · exact Submodule.subset_span ⟨S, m, hSlen, hmdeg, rfl⟩

/-- **The `+`-gate bound (proved).**  `spdpRank` is subadditive: `spdpRank κ ℓ (p+q) ≤ spdpRank κ ℓ p + spdpRank κ ℓ q`.
The genuine low-side per-transition lemma of a dynamic SPDP invariant. -/
theorem spdpRank_add_le (κ ℓ : ℕ) (p q : MvPolynomial (Fin n) F) :
    spdpRank κ ℓ (p + q) ≤ spdpRank κ ℓ p + spdpRank κ ℓ q := by
  haveI : FiniteDimensional F (spdpSubspace κ ℓ p) :=
    Submodule.finiteDimensional_of_le (NFrameSPDPBridge.spdpSubspace_le_restrictTotalDegree κ ℓ p)
  haveI : FiniteDimensional F (spdpSubspace κ ℓ q) :=
    Submodule.finiteDimensional_of_le (NFrameSPDPBridge.spdpSubspace_le_restrictTotalDegree κ ℓ q)
  refine le_trans (Submodule.finrank_mono (spdpSubspace_add_le κ ℓ p q)) ?_
  exact Submodule.finrank_add_le_finrank_add_finrank _ _

/-! ### The no-go for the naive "max rank across states" dynamic cost -/

/-- Every element of a list is `≤` its `Nat.max`-fold. -/
theorem le_foldr_max (x : ℕ) (l : List ℕ) (h : x ∈ l) : x ≤ l.foldr Nat.max 0 := by
  induction l with
  | nil => simp at h
  | cons a l' ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with h1 | h2
    · exact h1 ▸ le_max_left _ _
    · exact le_trans (ih h2) (le_max_right _ _)

/-- The naive dynamic cost of a trace: the maximum order-`κ` SPDP rank across its states. -/
noncomputable def dynamicTraceCost (κ : ℕ) (states : List (MvPolynomial (Fin n) F)) : ℕ :=
  (states.map (fun p => spdpRank κ 0 p)).foldr Nat.max 0

/-- Any state's rank is at most the trace's max-rank cost. -/
theorem le_dynamicTraceCost {κ : ℕ} {states : List (MvPolynomial (Fin n) F)}
    {p : MvPolynomial (Fin n) F} (hp : p ∈ states) : spdpRank κ 0 p ≤ dynamicTraceCost κ states := by
  unfold dynamicTraceCost
  exact le_foldr_max _ _ (List.mem_map.mpr ⟨p, hp, rfl⟩)

/-- **The no-go (proved).**  Any construction trace whose states include `∏ᵢ Xᵢ` has max-rank cost `≥ C(n, κ)` —
exponential at `κ = n/2`.  So "max `spdpRank` across states" cannot make `∏ᵢ Xᵢ` cheap: it is bounded below by the
static final rank.  A useful dynamic SPDP must measure something non-accumulative. -/
theorem fullProd_dynamicTraceCost_ge (κ : ℕ) {states : List (MvPolynomial (Fin n) F)}
    (h : (fullProd : MvPolynomial (Fin n) F) ∈ states) :
    n.choose κ ≤ dynamicTraceCost κ states :=
  le_trans (spdpRank_fullProd_choose_ge κ) (le_dynamicTraceCost h)

end PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

#print axioms PallLean.Paper93.DeepMath.PathB.SPDPLowerBound.spdpRank_add_le
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPLowerBound.fullProd_dynamicTraceCost_ge
