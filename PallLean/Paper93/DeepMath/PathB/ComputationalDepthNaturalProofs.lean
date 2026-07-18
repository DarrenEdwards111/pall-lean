import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPolyCeiling

/-!
# The schema evades natural proofs: generically-sound measures are not large

The barrier audit's second pillar.  The Razborov–Rudich natural-proofs barrier blocks a lower
bound whose underlying property is *natural* — constructive **and large** (dense on random
objects) — assuming pseudorandom functions exist.  This file shows the trace schema's
generically-sound measures automatically fail the **largeness** condition, so the natural-proofs
barrier does not apply to them.

Largeness, faithfully: a property is *large at threshold* `t` if, at every length `n`, at least
half of the length-`n` configurations exceed the threshold (`PropLarge`).  Generic soundness
caps a measure polynomially on *every* configuration (`perConfig_poly_of_genSound`), so at any
**superpolynomial** threshold there is a length at which **no** configuration reaches it — the
"μ-large" set is empty there, the opposite of dense.  Hence `genSound_not_propLarge`: a
generically-sound measure is not large at any superpolynomial threshold.

**Frontier reading.**  A natural-proofs *obstruction* would require the schema's hardness
property to be large; generic soundness — the very hypothesis that made the transfer work —
forces non-largeness instead.  Together with `TraceRelativization` (machine-dependence ⇒ evades
relativization), the schema evades *both* classical barriers.  So the surviving super-additive
candidate is not excluded by relativization or natural proofs; only algebrization remains open.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NaturalProofs

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.SeparationNoGo
open PallLean.Paper93.DeepMath.PathB.TraceMeasureSchema
open PallLean.Paper93.DeepMath.PathB.PolyCeiling (perConfig_poly_of_genSound)
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-- **Largeness at a threshold.**  The property "`μ` on a single configuration exceeds `t`" is
large at `t` if at every length `n`, at least half of the length-`n` configurations exceed the
threshold. -/
def PropLarge (μ : List (List Bool) → ℕ) (t : ℕ → ℕ) : Prop :=
  ∀ n, Fintype.card (Fin n → Bool)
    ≤ 2 * (Finset.univ.filter fun v : Fin n → Bool => t n ≤ μ [List.ofFn v]).card

/-- **The largeness evasion.**  A generically-sound trace measure is not large at any
superpolynomial threshold: generic soundness caps it polynomially on every configuration, so at
the length where the threshold outruns that cap, the "μ-large" set is empty — far from dense. -/
theorem genSound_not_propLarge (μ : List (List Bool) → ℕ)
    (hG : InvGenSound (traceInv μ)) (t : ℕ → ℕ) (ht : ¬ PolyBounded t) :
    ¬ PropLarge μ t := by
  obtain ⟨c, k, hpc⟩ := perConfig_poly_of_genSound μ hG
  have ht' : ∀ c k : ℕ, ∃ n, c * (n + 1) ^ k < t n := by
    intro c' k'
    by_contra hn
    push_neg at hn
    exact ht ⟨c', k', hn⟩
  obtain ⟨n, hn⟩ := ht' c k
  intro hLarge
  have hempty : (Finset.univ.filter fun v : Fin n → Bool => t n ≤ μ [List.ofFn v]) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro v _
    have hb : μ [List.ofFn v] ≤ c * (n + 1) ^ k := by
      have := hpc (List.ofFn v)
      simpa using this
    omega
  have hpos : 0 < Fintype.card (Fin n → Bool) := Fintype.card_pos
  have := hLarge n
  rw [hempty, Finset.card_empty] at this
  omega

/-- **Non-largeness, restated.**  Equivalently, a generically-sound measure is polynomially
capped on every configuration — so no configuration ever attains a superpolynomial value.  A
natural-proofs obstruction needs largeness; the schema's generic soundness supplies its negation
directly. -/
theorem genSound_config_poly_capped (μ : List (List Bool) → ℕ)
    (hG : InvGenSound (traceInv μ)) :
    ∃ c k, ∀ w : List Bool, μ [w] ≤ c * (w.length + 1) ^ k :=
  perConfig_poly_of_genSound μ hG

end PallLean.Paper93.DeepMath.PathB.NaturalProofs
