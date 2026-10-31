import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingEnergy

/-!
# Testing quadratic energy against space-expansion simulation

The decisive test: can a semantics-preserving space-expansion simulation *flatten* `crossingEnergy`
(`= Σ (crossingCount b)²`) at polynomial overhead?  This file settles it for the natural class of
expansions and names exactly what a counterexample would require.

A space-expansion simulation lays the original computation out over a wider tape.  Every such
"stretch/pad" simulation — cell-spreading by a fixed factor, blank-insertion, coordinate
dilation — carries each original boundary `b` to a boundary `g b` of the simulator whose crossing
load is at least the original: `crossingCount M c b T ≤ crossingCount M' c' (g b) T'` (each original
crossing becomes a crossing of the embedded boundary).  We call this a **crossing-preserving
expansion**; `g` embeds `[0,S)` injectively into `[0,S')`.

## Result: survival

* `crossingEnergy_mono_of_embed` — energy is monotone under boundary embedding: if loads are
  preserved under an injective map, `Σ v² ≤ Σ w²`.  Extra boundaries only add non-negative energy.
* `crossingEnergy_survives_expansion` — **any crossing-preserving space expansion has
  `crossingEnergy M c S T ≤ crossingEnergy M' c' S' T'`**: it cannot lower the energy.  So cell-
  spreading and every stretch/pad simulation *fail to flatten* quadratic energy — the concentrated
  load stays concentrated at the embedded boundary, and adding space only adds boundaries.

## What a counterexample would need (honest boundary)

To *flatten* `crossingEnergy` a simulation must strictly **reduce** some crossing counts — i.e. avoid
re-crossings by storing/memoizing information rather than re-deriving it.  That is a genuine
time–space (storage) trade, and it falls *outside* the crossing-preserving class this theorem covers.
Whether such a polynomial-overhead simulation exists is the real open question; it is not settled
here.

Scope, stated plainly: `hpreserve` is taken as a hypothesis — it is the property every stretch-type
simulation supplies — rather than derived from a fully constructed simulating machine.  So this is a
survival theorem for the crossing-preserving **class**, with the counterexample precisely located
(a re-crossing-reducing simulation), not a full settlement.

Nothing here proves a separation or a superpolynomial bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

variable {M : Machine}

/-- **Energy is monotone under boundary embedding.**  If `[0,S)` embeds injectively into `[0,S')`
via `g` with loads preserved (`v b ≤ w (g b)`), then `Σ v² ≤ Σ w²`. -/
theorem crossingEnergy_mono_of_embed (v w : ℕ → ℕ) (S S' : ℕ) (g : ℕ → ℕ)
    (hginj : Set.InjOn g ↑(Finset.range S))
    (hgrange : ∀ b ∈ Finset.range S, g b ∈ Finset.range S')
    (hvw : ∀ b ∈ Finset.range S, v b ≤ w (g b)) :
    ∑ b ∈ Finset.range S, v b ^ 2 ≤ ∑ j ∈ Finset.range S', w j ^ 2 := by
  calc ∑ b ∈ Finset.range S, v b ^ 2
      ≤ ∑ b ∈ Finset.range S, w (g b) ^ 2 :=
        Finset.sum_le_sum (fun b hb => Nat.pow_le_pow_left (hvw b hb) 2)
    _ = ∑ j ∈ (Finset.range S).image g, w j ^ 2 :=
        (Finset.sum_image (f := fun j => w j ^ 2) hginj).symm
    _ ≤ ∑ j ∈ Finset.range S', w j ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.image_subset_iff.mpr hgrange) (fun i _ _ => Nat.zero_le _)

/-- **Quadratic energy survives crossing-preserving space expansion.**  If a simulation
`(M',c',S',T')` embeds the original boundaries injectively via `g` and preserves their crossing loads,
then it does not lower the energy.  Cell-spreading and every stretch/pad simulation are of this form,
so none of them flattens `crossingEnergy`. -/
theorem crossingEnergy_survives_expansion {M' : Machine}
    (c : Cfg M) (c' : Cfg M') (S S' T T' : ℕ) (g : ℕ → ℕ)
    (hginj : Set.InjOn g ↑(Finset.range S))
    (hgrange : ∀ b ∈ Finset.range S, g b ∈ Finset.range S')
    (hpreserve : ∀ b ∈ Finset.range S,
      crossingCount M c b T ≤ crossingCount M' c' (g b) T') :
    crossingEnergy M c S T ≤ crossingEnergy M' c' S' T' := by
  unfold crossingEnergy
  exact crossingEnergy_mono_of_embed
    (fun b => crossingCount M c b T) (fun j => crossingCount M' c' j T')
    S S' g hginj hgrange hpreserve

#print axioms crossingEnergy_mono_of_embed
#print axioms crossingEnergy_survives_expansion

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
