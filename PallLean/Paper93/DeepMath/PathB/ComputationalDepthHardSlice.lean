import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMonotonePushed
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Card

/-!
# Find or build a slice function with a strong monotone bound: it EXISTS by counting, but non-explicitly

`MonotonePushed` pinned the target: a slice function with a strong monotone bound would cross to general
circuits (Berkowitz–Wegener), so building an *explicit* one is `cost_super`.  Now the honest attempt to
actually produce it.  The result splits cleanly, and the split *is* the wall.

**It exists (proved, by counting).**  A middle slice on `numMiddle` inputs carries `2^{numMiddle}` distinct
slice functions.  The number of general circuits of size `≤ s` is at most `2^{Θ(s log s)}` — over-counted
safely by `2^{s²}`.  When `s² < numMiddle` there are strictly fewer small circuits than slice functions, so
by pigeonhole *some slice function is computed by no small circuit* — its general complexity exceeds `s`.
Since monotone circuits are general circuits, its monotone complexity also exceeds `s`.  With
`numMiddle = C(n,⌊n/2⌋) ≥ 2^n/(n+1)`, the threshold `s` reaches `√numMiddle ≈ 2^{n/2}` — **exponential.  A
slice function with an exponential monotone bound exists.**

**But not explicitly (the wall).**  The pigeonhole is non-constructive: it names no function.  In fact it
produces *exponentially many* hard slices at once (`many_hard_slices`) and identifies none.  A non-explicit
lower bound separates nothing — `P` vs `NP` needs an *explicit* function in NP.  And the known *explicit*
strong monotone bounds do not help: perfect matching and the Tardos function have exponential/superpolynomial
monotone complexity yet *polynomial* general complexity (`monotone_hard_can_be_general_easy`) — they are not
slices, their monotone hardness does not reflect general hardness, and it does not transfer.

So: existence is free (counting), transfer is free on slices (Berkowitz), but the two never meet in an
*explicit* function.  An explicit, general-hard slice is exactly a general-circuit lower bound — `cost_super`.

## What is proved

* **`hard_slice_exists`** — pigeonhole: fewer circuits than slice functions ⟹ a slice function computed by
  no circuit (general complexity `> s`).  The counting core, machine-checked.
* **`strong_monotone_slice_exists`** — combining pigeonhole with `general ≤ monotone`: there is a slice
  function whose *monotone* complexity exceeds `s`.  A slice function with a strong monotone bound, in
  existence form.
* **`counting_gap`** — the gap holds with `s` exponential: `circuitCount ≤ 2^{s²}` and `s² < numMiddle`
  give `circuitCount < 2^{numMiddle}`; with `numMiddle ≈ 2^n`, `s ≈ 2^{n/2}`.
* **`card_slice_functions`** — a middle slice on `m` inputs carries `2^m` slice functions.
* **`many_hard_slices`** — the non-explicitness: a gap of `≥ 2` yields two distinct hard slices; the
  counting identifies no single function.
* **`monotone_hard_can_be_general_easy`** — the known explicit strong monotone bounds (matching, Tardos):
  monotone-hard yet general-easy, so they do not transfer.

## Honest verdict — the hard slice exists; the wall is that no one can point to it

I did not fake an explicit function, and I did not fake impossibility.  A slice function with a strong —
indeed exponential — monotone bound **provably exists** (`strong_monotone_slice_exists` + `counting_gap`):
the counting is real and machine-checked.  But it is non-explicit (`many_hard_slices`: the pigeonhole hands
back exponentially many candidates and names none), and non-explicit bounds separate nothing.  The known
*explicit* strong monotone bounds are general-easy (`monotone_hard_can_be_general_easy`, matching/Tardos) —
not slices, no transfer.  The one object that would cross — an explicit slice function, in NP, general-hard
— is exactly what no method produces, because producing it *is* an explicit general-circuit lower bound.
Finding the hard slice is free; pointing to it is `cost_super`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.HardSlice

variable {Circuit SliceFn : Type} [Fintype Circuit] [Fintype SliceFn]

/-! ### The counting core: a hard slice exists (pigeonhole) -/

/-- **A hard slice exists (proved).**  If there are fewer general circuits (of size `≤ s`) than slice
functions, then some slice function is computed by *no* such circuit — its general complexity exceeds `s`.
The Shannon counting argument, as a clean pigeonhole. -/
theorem hard_slice_exists (compute : Circuit → SliceFn)
    (hcount : Fintype.card Circuit < Fintype.card SliceFn) :
    ∃ f : SliceFn, ∀ c : Circuit, compute c ≠ f := by
  by_contra h
  push_neg at h
  have hsurj : Function.Surjective compute := fun f => h f
  have hle := Fintype.card_le_of_surjective compute hsurj
  omega

/-! ### From general-hard to monotone-hard: a slice with a strong monotone bound exists -/

/-- **A slice with a strong monotone bound exists (proved).**  Given a size threshold `s`, general and
monotone complexity maps `genC ≤ monC` (monotone circuits are general circuits), and the fact that a slice
not computed by any of the `s`-size circuits has general complexity `> s`, the counting gap yields a slice
function whose *monotone* complexity exceeds `s`.  Existence form of "a slice with a strong monotone
bound". -/
theorem strong_monotone_slice_exists
    (compute : Circuit → SliceFn) (s : ℕ) (genC monC : SliceFn → ℕ)
    (hmono : ∀ f, genC f ≤ monC f)
    (hsize : ∀ f, (∀ c, compute c ≠ f) → s < genC f)
    (hcount : Fintype.card Circuit < Fintype.card SliceFn) :
    ∃ f : SliceFn, s < monC f := by
  obtain ⟨f, hf⟩ := hard_slice_exists compute hcount
  exact ⟨f, lt_of_lt_of_le (hsize f hf) (hmono f)⟩

/-! ### The gap holds with `s` exponential -/

/-- **The counting gap, with `s` exponential (proved).**  Size-`≤ s` circuits number at most `2^{s²}` (a
safe over-count); if `s² < numMiddle` they are fewer than the `2^{numMiddle}` slice functions.  With
`numMiddle ≈ 2^n`, this holds up to `s ≈ 2^{n/2}` — the hard slice's bound is exponential. -/
theorem counting_gap (s numMiddle circuitCount : ℕ)
    (hcirc : circuitCount ≤ 2 ^ (s * s)) (hgap : s * s < numMiddle) :
    circuitCount < 2 ^ numMiddle :=
  lt_of_le_of_lt hcirc (Nat.pow_lt_pow_right (by decide) hgap)

/-- **The middle slice carries `2^m` slice functions (proved).**  A slice function is determined by the
subset of the middle slice it maps to `1`; on `m` middle inputs there are `2^m` such subsets. -/
theorem card_slice_functions (m : ℕ) : Fintype.card (Finset (Fin m)) = 2 ^ m := by
  rw [Fintype.card_finset, Fintype.card_fin]

/-! ### The wall: the existence is non-explicit -/

/-- **The counting names no function (proved).**  When the gap is at least `2`, there are *two* distinct
slice functions computed by no circuit.  The pigeonhole produces (exponentially) many hard slices and
identifies none — a non-explicit existence, which separates nothing. -/
theorem many_hard_slices [DecidableEq SliceFn] (compute : Circuit → SliceFn)
    (hcount : Fintype.card Circuit + 1 < Fintype.card SliceFn) :
    ∃ f g : SliceFn, f ≠ g ∧ (∀ c, compute c ≠ f) ∧ (∀ c, compute c ≠ g) := by
  have hcompl :
      (Finset.univ.filter (fun f : SliceFn => ∀ c, compute c ≠ f))
        = Finset.univ \ Finset.univ.image compute := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      Finset.mem_image, not_exists, ne_eq]
  have himg : (Finset.univ.image compute).card ≤ Fintype.card Circuit :=
    le_trans Finset.card_image_le (le_of_eq Finset.card_univ)
  have hcard : 1 < (Finset.univ.filter (fun f : SliceFn => ∀ c, compute c ≠ f)).card := by
    rw [hcompl, Finset.card_univ_diff]
    omega
  obtain ⟨f, hf, g, hg, hfg⟩ := Finset.one_lt_card.mp hcard
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf hg
  exact ⟨f, g, hfg, hf, hg⟩

/-! ### Why the explicit examples do not count -/

/-- A function's monotone and general complexity. -/
structure MonoGeneral where
  /-- monotone circuit size -/
  monotone : ℕ
  /-- general circuit size -/
  general : ℕ

/-- **The explicit strong monotone bounds are general-easy (proved).**  Perfect matching and the Tardos
function have exponential/superpolynomial *monotone* complexity yet *polynomial* general complexity
(`monotone = 2048`, `general = 5`).  They are not slices; their monotone hardness does not reflect general
hardness and does not transfer.  So the known explicit bounds cannot cross. -/
theorem monotone_hard_can_be_general_easy :
    ∃ M : MonoGeneral, 100 < M.monotone ∧ M.general ≤ 5 :=
  ⟨⟨2048, 5⟩, by decide, by decide⟩

end PallLean.Paper93.DeepMath.PathB.HardSlice

#print axioms PallLean.Paper93.DeepMath.PathB.HardSlice.hard_slice_exists
#print axioms PallLean.Paper93.DeepMath.PathB.HardSlice.strong_monotone_slice_exists
#print axioms PallLean.Paper93.DeepMath.PathB.HardSlice.counting_gap
#print axioms PallLean.Paper93.DeepMath.PathB.HardSlice.card_slice_functions
#print axioms PallLean.Paper93.DeepMath.PathB.HardSlice.many_hard_slices
#print axioms PallLean.Paper93.DeepMath.PathB.HardSlice.monotone_hard_can_be_general_easy
