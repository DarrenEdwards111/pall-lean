import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ResidueMachine

/-!
# A residue-observer algebra: composable abstraction for the residue speedup

The residue speedup so far was tied to `Depth2ModCircuit`.  This file abstracts it into a reusable, composable
**observer** theory: a Boolean function is *observed* by a statistic when it factors through it, and observers
compose (a top gate over observed subfunctions is observed by the product statistic) with a multiplicative
cell-count bound.  This makes depth iteration (the Beigel–Tarui socket) less ad hoc: an ACC layer over
residue-observed subcircuits is itself residue-observed.

## What is proved (clean axioms, no `sorry`)

* `ObservedBy` — `f` factors through `stat` (`∃ g, f = g ∘ stat`).
* `observed_sat_iff` — **SAT via the observer**: search `image(stat)`, not the cube.
* `observed_cellCount_le` — `|image(stat)| ≤ card(codomain)`.
* `ObservedBy.comp` — a function of an observed function is observed (same statistic).
* `observed_top_pi` — **the composition law**: any top function of a family of observed subfunctions is observed by
  the *product* statistic.
* `observed_pi_cellCount_le` — the product statistic has `≤ ∏_i card(S_i)` cells.
* `modGate_observedBy`, `depth2_observedBy` — a `MOD` gate is observed by its residue (`card q`); a depth-2 `MOD`
  circuit is observed by its residue vector (`card ∏ q_j`) — the residue speedup re-derived from the algebra.

## Honest scope

A clean reusable abstraction over the proved residue facts; `observed_top_pi` is the genuine composition primitive
for depth reduction.  It does **not** itself reduce `ACC⁰` depth (the `MOD`-of-`AND` direction needs the right
bottom-gate observers — the toy Beigel–Tarui step).  Still the cell-count model; nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ModResidueSpeedup

variable {n : ℕ}

/-- `f` is **observed by** `stat` if it factors through it: `f = g ∘ stat` for some `g`. -/
def ObservedBy {S : Type*} (f : (Fin n → Bool) → Bool) (stat : (Fin n → Bool) → S) : Prop :=
  ∃ g : S → Bool, ∀ x, f x = g (stat x)

/-- **SAT via the observer (proved): search the statistic's image, not the cube.** -/
theorem observed_sat_iff {S : Type*} [DecidableEq S] {f : (Fin n → Bool) → Bool}
    {stat : (Fin n → Bool) → S} (g : S → Bool) (hg : ∀ x, f x = g (stat x)) :
    Satisfiable f ↔ ∃ s ∈ Finset.univ.image stat, g s = true := by
  unfold Satisfiable
  simp_rw [hg]
  exact sat_iff_image g stat

/-- **The observer cell-count bound (proved): `|image(stat)| ≤ card(codomain)`.** -/
theorem observed_cellCount_le {S : Type*} [Fintype S] [DecidableEq S] (stat : (Fin n → Bool) → S) :
    (Finset.univ.image stat).card ≤ Fintype.card S :=
  le_trans (Finset.card_le_card (Finset.subset_univ _)) (le_of_eq Finset.card_univ)

/-- **Composition (proved): a function of an observed function is observed by the same statistic.** -/
theorem ObservedBy.comp {S : Type*} {f : (Fin n → Bool) → Bool} {stat : (Fin n → Bool) → S}
    (h : ObservedBy f stat) (φ : Bool → Bool) :
    ObservedBy (fun x => φ (f x)) stat := by
  obtain ⟨g, hg⟩ := h
  exact ⟨fun s => φ (g s), fun x => by show φ (f x) = φ (g (stat x)); rw [hg]⟩

/-- **Branch (proved): SAT decomposes over the `2^{#K}` assignments of a killed set `K`.**  The model-agnostic
branch-and-restrict decomposition, the observer-level branching primitive. -/
theorem observer_sat_branch (f : (Fin n → Bool) → Bool) (K : Finset (Fin n)) :
    Satisfiable f ↔ ∃ b : Fin n → Bool, ∃ x, (∀ i ∈ K, x i = b i) ∧ f x = true := by
  unfold Satisfiable
  constructor
  · rintro ⟨x, hx⟩; exact ⟨x, x, fun _ _ => rfl, hx⟩
  · rintro ⟨_, x, _, hx⟩; exact ⟨x, hx⟩

/-- **AND of two observed functions is observed by the product statistic (proved).** -/
theorem ObservedBy.and {S T : Type*} {f₁ f₂ : (Fin n → Bool) → Bool}
    {s₁ : (Fin n → Bool) → S} {s₂ : (Fin n → Bool) → T}
    (h₁ : ObservedBy f₁ s₁) (h₂ : ObservedBy f₂ s₂) :
    ObservedBy (fun x => f₁ x && f₂ x) (fun x => (s₁ x, s₂ x)) := by
  obtain ⟨g₁, hg₁⟩ := h₁
  obtain ⟨g₂, hg₂⟩ := h₂
  exact ⟨fun p => g₁ p.1 && g₂ p.2,
    fun x => by dsimp only; rw [hg₁ x, hg₂ x]⟩

/-- **OR of two observed functions is observed by the product statistic (proved).** -/
theorem ObservedBy.or {S T : Type*} {f₁ f₂ : (Fin n → Bool) → Bool}
    {s₁ : (Fin n → Bool) → S} {s₂ : (Fin n → Bool) → T}
    (h₁ : ObservedBy f₁ s₁) (h₂ : ObservedBy f₂ s₂) :
    ObservedBy (fun x => f₁ x || f₂ x) (fun x => (s₁ x, s₂ x)) := by
  obtain ⟨g₁, hg₁⟩ := h₁
  obtain ⟨g₂, hg₂⟩ := h₂
  exact ⟨fun p => g₁ p.1 || g₂ p.2,
    fun x => by dsimp only; rw [hg₁ x, hg₂ x]⟩

/-- **The composition law (proved): a top gate over observed subfunctions is observed by the product statistic.**
If each `f i` is observed by `stat i`, then *any* `top (f 1, …, f k)` is observed by the product statistic
`x ↦ (stat i x)_i`.  This is the residue-observer primitive for depth reduction: an ACC layer over residue-observed
subcircuits is residue-observed. -/
theorem observed_top_pi {ι : Type*} [Fintype ι] {S : ι → Type*}
    (f : ι → (Fin n → Bool) → Bool) (stat : ∀ i, (Fin n → Bool) → S i)
    (hf : ∀ i, ObservedBy (f i) (stat i)) (top : (ι → Bool) → Bool) :
    ObservedBy (fun x => top (fun i => f i x)) (fun x => fun i => stat i x) := by
  choose g hg using hf
  refine ⟨fun v => top (fun i => g i (v i)), fun x => ?_⟩
  show top (fun i => f i x) = top (fun i => g i (stat i x))
  exact congrArg top (funext fun i => hg i x)

/-- **The product cell-count bound (proved): `|image(product stat)| ≤ ∏_i card(S_i)`.** -/
theorem observed_pi_cellCount_le {ι : Type*} [Fintype ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] (stat : ∀ i, (Fin n → Bool) → S i) :
    (Finset.univ.image (fun x => fun i => stat i x)).card ≤ ∏ i, Fintype.card (S i) := by
  rw [← Fintype.card_pi]
  exact observed_cellCount_le _

/-! ## The `MOD` observers -/

/-- **A `MOD` gate is observed by its mod-statistic (proved), codomain `ZMod q` (`card q`).** -/
theorem modGate_observedBy (G : ModGate n) :
    ObservedBy (G.eval) (fun x => modQStatOn G.support G.modulus x) :=
  ⟨fun s => decide (s = G.target), fun _ => rfl⟩

/-- **A depth-2 `MOD` circuit is observed by its residue vector (proved).**  Via the composition law on the bottom
`MOD` observers — re-deriving the residue speedup (`card ∏ q_j`) from the observer algebra. -/
theorem depth2_observedBy {k : ℕ} (C : Depth2ModCircuit n k) :
    ObservedBy C.eval (modResVec C) :=
  observed_top_pi (fun j => (C.gates j).eval)
    (fun j x => modQStatOn (C.gates j).support (C.gates j).modulus x)
    (fun j => modGate_observedBy (C.gates j)) C.top

end PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver.observed_sat_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver.observed_top_pi
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver.observed_pi_cellCount_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver.depth2_observedBy
