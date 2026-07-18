import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPolyCeiling

/-!
# A measure-level non-largeness fact: generically-sound measures are not large

**Scope, stated honestly up front.**  This file proves a *measure-level* fact — generically-sound
trace measures fail a faithfully-stated *largeness* condition — and connects it, informally, to the
Razborov–Rudich natural-proofs setting.  It is **not** a genuine natural-proofs barrier evasion.
The real natural-proofs barrier is a statement about a *property distinguishing a circuit class*
being simultaneously constructive and dense on random truth tables, conditional on pseudorandom
functions.  What is proved here is only the density (largeness) half, phrased for trace measures on
configurations, with no circuit class, no constructivity account, and no PRF hypothesis.  Read it
as "the schema's measures are not large in this configuration sense," not "the schema evades the
natural-proofs barrier."

The content: a property is *large at threshold* `t` if, at every length `n`, at least half of the
length-`n` configurations exceed the threshold (`PropLarge`).  Generic soundness caps a measure
polynomially on *every* configuration (`perConfig_poly_of_genSound`), so at any **superpolynomial**
threshold there is a length at which **no** configuration reaches it — the "μ-large" set is empty
there, the opposite of dense.  Hence `genSound_not_propLarge`: a generically-sound measure is not
large at any superpolynomial threshold.

**Frontier reading.**  This is one measure-level non-invariance fact among three
(machine-dependence in `TraceRelativization`, non-largeness here, non-language-invariance in
`TraceAlgebrization`).  Together they record that the schema's measures are not invariant in ways
the classical barriers exploit — a suggestive but weaker statement than genuine barrier evasion.

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

/-- **Measure-level non-largeness.**  A generically-sound trace measure is not large at any
superpolynomial threshold: generic soundness caps it polynomially on every configuration, so at
the length where the threshold outruns that cap, the "μ-large" set is empty — far from dense.
(This is the density half only, on configurations; it is not a natural-proofs barrier evasion.) -/
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
