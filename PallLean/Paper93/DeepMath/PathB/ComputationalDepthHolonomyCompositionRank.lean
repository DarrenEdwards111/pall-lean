import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHolonomyBoundedCycleRank

/-!
# Holonomy under composition — rank is subadditive, not super‑multiplicative

The feature‑counting budget blew up as `2^{(d+1)^k}` under composition of `k` gates — the *exponent* was
exponential in `k` (`…ACC0Composition`).  This file shows holonomy is qualitatively better: because it is
`F₂`‑linear in the charge, the holonomy class count is **submultiplicative** under composition, so the effective
**rank** (the exponent) grows only **additively** in the number of composed pieces.

The composition of two charge sources is their `F₂`‑sumset `A ⊞ B = {a + b : a ∈ A, b ∈ B}` (parallel constraints
superpose).  Linearity (`holSigZ_add`) gives `holSig(a+b) = holSig a + holSig b`, so a composed signature is
determined by the pair of component signatures.

## What is proved (clean axioms, no `sorry`)

* `holonomy_classes_submultiplicative` — `#classes(A ⊞ B) ≤ #classes(A) · #classes(B)`.  Composing two sources
  *multiplies* class counts (at most), i.e. **adds** their effective ranks.
* `holonomy_rank_subadditive` — the same in exponent form: if `#classes(A) ≤ 2^{rₐ}` and `#classes(B) ≤ 2^{r_b}`
  then `#classes(A ⊞ B) ≤ 2^{rₐ + r_b}`.  Effective holonomy rank is **subadditive** under composition.

## Why this matters — and the honest ceiling

This is the genuine structural advantage of holonomy over the additive‑statistic budget: composing `k` sources of
effective rank `≤ s` gives `≤ 2^{k·s}` classes — exponent **linear** in `k`, versus the feature budget's
`2^{(d+1)^k}` (exponent exponential in `k`).  Holonomy is therefore *far less vacuous* under composition: its
budget is `2^{poly}` with a *polynomial* exponent, where feature‑counting had a *super‑polynomial* exponent.

But it is still not A1: a polynomial **number of classes** needs effective rank `O(\log n)` (`2^{O(\log n)} = poly`),
and subadditivity only gives `k·s` — which is `O(\log n)` exactly when the composed circuit has `k·s = O(\log n)`
total effective cycle rank.  For an NP‑hard instance an ACC⁰ circuit can drive that rank to `Ω(n)` (expander
charges), so the open step is unchanged: **poly‑time ⇒ low total effective cycle rank on hard instances** =
`ACC0LowRealizedGodelSPDP`, still under the PRF‑free naturalness ceiling.  What is new: composition provably
contributes rank *additively*, so holonomy degrades gracefully where feature‑counting collapsed — the strongest
quantitative behaviour in the arc, with the gap named, not bridged.
-/

namespace PallLean.Paper93.DeepMath.PathB.HolonomyCompositionRank

open PallLean.Paper93.DeepMath.PathB.HolonomyPSideControl
open Classical

variable {V : Type*}

/-- **Holonomy classes are submultiplicative under composition (proved).**  The `F₂`‑sumset `A ⊞ B` of two charge
sources realizes at most `#classes(A) · #classes(B)` holonomy signatures: a composed signature `holSig(a+b)` is
`holSig a + holSig b`, determined by the component signatures. -/
theorem holonomy_classes_submultiplicative {m : ℕ} (cycle : Fin m → Finset V)
    (A B : Finset (V → ZMod 2)) :
    (((A ×ˢ B).image (fun p => p.1 + p.2)).image (holSigZ cycle)).card
      ≤ (A.image (holSigZ cycle)).card * (B.image (holSigZ cycle)).card := by
  have hsub : ((A ×ˢ B).image (fun p => p.1 + p.2)).image (holSigZ cycle)
      ⊆ ((A.image (holSigZ cycle)) ×ˢ (B.image (holSigZ cycle))).image (fun q => q.1 + q.2) := by
    intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨x, hx, rfl⟩ := hs
    rw [Finset.mem_image] at hx
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := hx
    rw [Finset.mem_product] at hab
    rw [Finset.mem_image]
    refine ⟨(holSigZ cycle a, holSigZ cycle b), ?_, ?_⟩
    · rw [Finset.mem_product]
      exact ⟨Finset.mem_image.mpr ⟨a, hab.1, rfl⟩, Finset.mem_image.mpr ⟨b, hab.2, rfl⟩⟩
    · exact (holSigZ_add cycle a b).symm
  calc (((A ×ˢ B).image (fun p => p.1 + p.2)).image (holSigZ cycle)).card
      ≤ (((A.image (holSigZ cycle)) ×ˢ (B.image (holSigZ cycle))).image (fun q => q.1 + q.2)).card :=
        Finset.card_le_card hsub
    _ ≤ ((A.image (holSigZ cycle)) ×ˢ (B.image (holSigZ cycle))).card := Finset.card_image_le
    _ = (A.image (holSigZ cycle)).card * (B.image (holSigZ cycle)).card := Finset.card_product _ _

/-- **Effective holonomy rank is subadditive under composition (proved).**  If `A` and `B` realize `≤ 2^{rₐ}` and
`≤ 2^{r_b}` holonomy classes, their composition realizes `≤ 2^{rₐ + r_b}` — the rank exponent **adds**, in
contrast to the feature budget's exponential `2^{(d+1)^k}` growth. -/
theorem holonomy_rank_subadditive {m rA rB : ℕ} (cycle : Fin m → Finset V)
    (A B : Finset (V → ZMod 2))
    (hA : (A.image (holSigZ cycle)).card ≤ 2 ^ rA) (hB : (B.image (holSigZ cycle)).card ≤ 2 ^ rB) :
    (((A ×ˢ B).image (fun p => p.1 + p.2)).image (holSigZ cycle)).card ≤ 2 ^ (rA + rB) := by
  calc (((A ×ˢ B).image (fun p => p.1 + p.2)).image (holSigZ cycle)).card
      ≤ (A.image (holSigZ cycle)).card * (B.image (holSigZ cycle)).card :=
        holonomy_classes_submultiplicative cycle A B
    _ ≤ 2 ^ rA * 2 ^ rB := Nat.mul_le_mul hA hB
    _ = 2 ^ (rA + rB) := by rw [pow_add]

end PallLean.Paper93.DeepMath.PathB.HolonomyCompositionRank

#print axioms PallLean.Paper93.DeepMath.PathB.HolonomyCompositionRank.holonomy_classes_submultiplicative
#print axioms PallLean.Paper93.DeepMath.PathB.HolonomyCompositionRank.holonomy_rank_subadditive
