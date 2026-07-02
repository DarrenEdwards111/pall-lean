import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMagnitude

/-!
# N-Frame: scoping a refined invariant — a candidate test harness

Increment (d) proved the raw monoAND-degree invariant *inverts* on hardness (the trivial full-AND `∏ᵢ xᵢ` gets the maximal
value `n`).  A separation via N-Frame needs a **refined** invariant `Φ` that (i) does *not* invert — it must rate easy
functions low — while (ii) capturing a real class and (iii) gapping a target.  This file sets up the search:

1. **Generic framework.**  `Invariant`, and `invariant_beam` — the beam holds for *any* `ℕ`-valued measure, so a candidate
   only has to satisfy the capture/gap requirements.
2. **Screening test.**  `nframeComplexity_fullAnd_maximal` — **PROVED**: the raw invariant rates the easy full-AND
   *maximally*, so it fails the anti-inversion screen and is disqualified as-is.
3. **A concrete candidate.**  `bdry` — the edge-boundary / average-sensitivity measure (`∑` over cube edges that are
   bichromatic).  `bdry_const` (`= 0`) shows it is well-defined; `fullAnd_has_stable_edge` — **PROVED**: the full-AND has a
   direction where flipping does not change it (a *non*-boundary edge), so it is not maximally sensitive.  Parity has no
   such edge, so `bdry` separates them — passing the screen raw degree fails (which rates both at the maximum `n`).

## Honest scope — the candidate's ceiling, and what is still open

`bdry` (average sensitivity) genuinely corrects the inversion, and by classical results (Boppana / LMN — *not* formalized
here) `AC⁰` functions have low average sensitivity, so `bdry` *does* capture `AC⁰` and yields real (restricted)
separations.  But it does **not** reach `P vs NP`: `P` contains high-sensitivity functions (recursive majority, tribes),
so `bdry`-capture *fails* for `P` — the candidate's honest ceiling is `AC⁰`, not `P`.  A `P`-vs-`NP`-reaching invariant
needs a property `bdry` lacks: low value on *all* of `P` including its high-sensitivity members, which is a genuine
circuit lower bound and remains subject to the natural-proofs barrier (the raw/sensitivity measures are exactly the
"large, constructive" invariants the barrier constrains).  This file honestly sets up the harness and evaluates the first
two candidates; it does not produce a `P`-separating invariant.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameRefined

open PallLean.Paper93.DeepMath.PathB.NFrameACC0
  (NFrameComplexity mem_sqfSpan_n nframeComplexity_le_of_mem_span nframeComplexity_sqfEval_univ_eq)
open PallLean.Paper93.DeepMath.PathB.Layer4 (sqfEval boolToField)

variable {n : ℕ} {F : Type*} [Field F]

/-! ### 1. Generic candidate-invariant framework -/

/-- A candidate complexity invariant: any `ℕ`-valued measure on cube functions. -/
abbrev Invariant (F : Type*) [Field F] (n : ℕ) := ((Fin n → Bool) → F) → ℕ

/-- `Φ` **captures** a class at bound `B`. -/
def CapturesI (Φ : Invariant F n) (InClass : ((Fin n → Bool) → F) → Prop) (B : ℕ) : Prop :=
  ∀ f, InClass f → Φ f ≤ B

/-- `Φ` **gaps** the target above `B`. -/
def GapI (Φ : Invariant F n) (B : ℕ) (tgt : (Fin n → Bool) → F) : Prop := B < Φ tgt

/-- **The invariant-generic beam (proved).**  For *any* candidate invariant, capture + gap ⇒ separation.  So a candidate
only needs to satisfy the requirements; the separating machinery is invariant-agnostic. -/
theorem invariant_beam (Φ : Invariant F n) {InClass : ((Fin n → Bool) → F) → Prop} {B : ℕ}
    {tgt : (Fin n → Bool) → F} (cap : CapturesI Φ InClass B) (gap : GapI Φ B tgt) :
    ¬ InClass tgt :=
  fun h => absurd (cap tgt h) (not_le.mpr gap)

/-! ### 2. Screening: the raw invariant inverts (disqualified) -/

/-- Every function has raw N-Frame complexity `≤ n`. -/
theorem nframeComplexity_le_card [Fintype F] [DecidableEq F] (f : (Fin n → Bool) → F) :
    NFrameComplexity F f ≤ n :=
  nframeComplexity_le_of_mem_span (mem_sqfSpan_n f)

/-- **Raw N-Frame inverts on hardness (proved).**  The trivial full-AND is rated *maximally* by the raw invariant — every
function has raw N-Frame `≤ NFrameComplexity (full-AND) = n`.  So raw degree fails the anti-inversion screen. -/
theorem nframeComplexity_fullAnd_maximal [Fintype F] [DecidableEq F] (hn : 0 < n)
    (f : (Fin n → Bool) → F) :
    NFrameComplexity F f ≤ NFrameComplexity F (sqfEval F (Finset.univ : Finset (Fin n))) := by
  rw [nframeComplexity_sqfEval_univ_eq hn]
  exact nframeComplexity_le_card f

/-! ### 3. A concrete refined candidate: edge-boundary / average sensitivity -/

/-- Flip the `i`-th input coordinate. -/
def flipCoord (i : Fin n) (x : Fin n → Bool) : Fin n → Bool := Function.update x i (!x i)

/-- **Edge-boundary (average-sensitivity) invariant.**  The number of `(input, direction)` pairs across which `f` changes
value — a cube-native robustness measure. -/
def bdry [DecidableEq F] (f : (Fin n → Bool) → F) : ℕ :=
  ∑ p : (Fin n → Bool) × Fin n, if f p.1 = f (flipCoord p.2 p.1) then 0 else 1

/-- **`bdry` of a constant is `0` (proved).**  It is a genuine robustness measure — constants have no boundary. -/
theorem bdry_const [DecidableEq F] (c : F) : bdry (fun _ : Fin n → Bool => c) = 0 := by
  unfold bdry
  apply Finset.sum_eq_zero
  intro p _
  rw [if_pos rfl]

/-- Full-AND vanishes wherever some coordinate is `false`. -/
theorem sqfEval_univ_eq_zero_of_false {x : Fin n → Bool} (i : Fin n) (hi : x i = false) :
    sqfEval F (Finset.univ : Finset (Fin n)) x = 0 := by
  show (∏ j : Fin n, boolToField F (x j)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [boolToField, hi])

/-- **The full-AND has a stable edge (proved).**  There is an `(input, direction)` where flipping does not change the
full-AND — so it is *not* maximally sensitive.  Parity has no stable edge (every edge flips it); raw degree, which rates
full-AND and parity identically at the maximum `n`, cannot see this distinction, whereas `bdry` (which counts exactly the
*non*-stable edges) does.  This is the anti-inversion signal that disqualifies raw degree but not `bdry`. -/
theorem fullAnd_has_stable_edge (hn : 2 ≤ n) :
    ∃ (x : Fin n → Bool) (i : Fin n),
      sqfEval F (Finset.univ : Finset (Fin n)) x
        = sqfEval F (Finset.univ : Finset (Fin n)) (flipCoord i x) := by
  refine ⟨(fun _ => false), ⟨0, by omega⟩, ?_⟩
  have h0 : sqfEval F (Finset.univ : Finset (Fin n)) (fun _ => false) = 0 :=
    sqfEval_univ_eq_zero_of_false ⟨0, by omega⟩ rfl
  have h1 : sqfEval F (Finset.univ : Finset (Fin n))
      (flipCoord ⟨0, by omega⟩ (fun _ => false)) = 0 := by
    refine sqfEval_univ_eq_zero_of_false ⟨1, by omega⟩ ?_
    simp [flipCoord, Fin.ext_iff]
  rw [h0, h1]

end PallLean.Paper93.DeepMath.PathB.NFrameRefined

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRefined.invariant_beam
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRefined.nframeComplexity_fullAnd_maximal
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRefined.fullAnd_has_stable_edge
