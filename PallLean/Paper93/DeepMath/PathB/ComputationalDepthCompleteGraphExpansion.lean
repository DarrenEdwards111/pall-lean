import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinWidthKernel

/-!
# Asymptotic expander family: the complete graph `Kₙ` has expansion, for all `n`

This lifts rung 1 of the proof-complexity ladder from one concrete graph (`K4`)
to an **infinite family**: the complete graph `Kₙ` (edges = the 2-element vertex
subsets) satisfies `HasExpansion 1` for every `n`.  Combined with the width
kernel, this gives a width lower bound for the Tseitin combinations on a genuine
family, not just a single instance.

The expansion is *proved*, not assumed: for any nonempty vertex set `S` of at
most half the vertices, the map `u ↦ {u, w₀}` (for a fixed `w₀ ∉ S`) injects `S`
into the edge boundary `∂S`, so `|∂S| ≥ |S|`.

Honest scope unchanged: this is still a *restricted* (width) lower bound; the
full width→size step (BSW) and the lift to general computation are not here, and
the bridge to general `P` is P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

open Finset

/-- The complete graph `Kₙ`: vertices `Fin n`, edges the 2-element subsets. -/
def completeGraph (n : ℕ) :
    TseitinGraph (Fin n) {s : Finset (Fin n) // s.card = 2} where
  endpoints e := e.1
  card_endpoints e := e.2

/-- **Asymptotic expansion (proved).**  `Kₙ` has vertex expansion `1` for every
`n`: every nonempty set of at most half the vertices has edge boundary at least
its own size. -/
theorem completeGraph_hasExpansion (n : ℕ) :
    (completeGraph n).HasExpansion 1 := by
  classical
  intro S h1 h2
  rw [Fintype.card_fin] at h2
  obtain ⟨u₁, hu₁⟩ := Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one h1)
  have hSc : Sᶜ.Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨w₀, hw₀'⟩ := hSc
  rw [Finset.mem_compl] at hw₀'
  have hu₁w : u₁ ≠ w₀ := fun h => hw₀' (h ▸ hu₁)
  let g : Fin n → {s : Finset (Fin n) // s.card = 2} := fun u =>
    if h : u ≠ w₀ then ⟨{u, w₀}, Finset.card_pair h⟩
    else ⟨{u₁, w₀}, Finset.card_pair hu₁w⟩
  have hmaps : ∀ u ∈ S, g u ∈ (completeGraph n).boundary S := by
    intro u hu
    have huw : u ≠ w₀ := fun h => hw₀' (h ▸ hu)
    have hinter : ({u, w₀} : Finset (Fin n)) ∩ S = {u} := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hx | hx, hxS⟩
        · exact hx
        · exact absurd (hx ▸ hxS) hw₀'
      · intro hx; subst hx; exact ⟨Or.inl rfl, hu⟩
    simp only [TseitinGraph.boundary, Finset.mem_filter, Finset.mem_univ, true_and,
      g, dif_pos huw, completeGraph]
    rw [hinter, Finset.card_singleton]
  have hinj : Set.InjOn g S := by
    intro a ha b hb hab
    have haw : a ≠ w₀ := fun h => hw₀' (h ▸ ha)
    have hbw : b ≠ w₀ := fun h => hw₀' (h ▸ hb)
    simp only [g, dif_pos haw, dif_pos hbw, Subtype.mk.injEq] at hab
    have hmem : a ∈ ({b, w₀} : Finset (Fin n)) := hab ▸ Finset.mem_insert_self a {w₀}
    rcases Finset.mem_insert.mp hmem with h | h
    · exact h
    · exact absurd (Finset.mem_singleton.mp h) haw
  have hsub : S.image g ⊆ (completeGraph n).boundary S := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨u, hu, rfl⟩ := he
    exact hmaps u hu
  calc 1 * S.card = S.card := one_mul _
    _ = (S.image g).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((completeGraph n).boundary S).card := Finset.card_le_card hsub

/-- **Asymptotic width lower bound.**  For every `n`, the F₂ combination of any
medium vertex set's Tseitin constraints on `Kₙ` has width `≥ |S|` — a width lower
bound on a genuine infinite family, obtained from the kernel + the proved
expansion. -/
theorem completeGraph_combination_width (n : ℕ) (S : Finset (Fin n))
    (h1 : 1 ≤ S.card) (h2 : 2 * S.card ≤ Fintype.card (Fin n)) :
    S.card ≤ (edgeSupport ((completeGraph n).combination S)).card := by
  have := (completeGraph n).combination_support_card_ge_of_expansion
    (completeGraph_hasExpansion n) S h1 h2
  simpa using this

/-! ## Kernel-only axiom trace -/

#print axioms completeGraph
#print axioms completeGraph_hasExpansion
#print axioms completeGraph_combination_width

end PallLean.Paper93.DeepMath.PathB
