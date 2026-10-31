import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityEval

/-!
# N-Frame: the multi-witness tensor family — Route F structural core

Route F (multi-witness) design rung.  The E5′ round showed the single-witness parity family
is capped at witness dimension `v = Θ(√N)` — forced because an affine literal over `F₂^v`
costs `Θ(v)` presence-bits to describe and `⊕#SAT`-hardness needs `Ω(v)` clauses, so
`N = m·L ≥ v²`.  Route F splits the `m` blocks into `g` independent GROUPS, each a
single-witness parity over its own `F₂^{v'}`, and combines by XOR:

    tensorParity BB := ⊕_γ parityFamily (BB γ)   (= Σ_γ Z_γ mod 2 in `ZMod 2`).

The structural payoff proved here — **detection localizes to a group**: a change confined to
group `γ*` flips the tensor value iff it flips group `γ*`'s own parity.  Disjoint witness
spaces ⇒ no cross-group over-determination; the total detectable rank is `Σ_γ v' = Θ(N)`,
which BEATS the crude `√N` witness cap.

  `groupCount` / `tensorParity` — the tensor family value in `ZMod 2`.
  `tensorParity_single_diff` — **PROVED**: a change off `γ*` leaves the tensor value shifted
        by exactly group `γ*`'s count change (Finset-sum cancellation).
  `tensor_detect_localizes` — **PROVED, THE LOCALIZATION**: the tensor flips iff group `γ*`
        flips — detection reduces to one group's `F₂^{v'}` machinery, unconstrained by the
        others.
  `groupCount_eq_parityFamily` — **PROVED**: the per-group count parity is exactly the
        existing `parityFamily`.

## Honest scope — what Route F does and does NOT do (assessed on paper, §F)

Localization is real and fixes the CRUDE witness-rank cap (tensor detectable rank `= Θ(N)`,
not `√N`).  But it does NOT convert to `(2+c)N`: (i) the annulus/concentration channel stays
ledger-dead (the `+1`-per-scale charge cancels the `O(1)`-per-scale witness-capped detection,
tensor or not); (ii) the single-cut spread channel already gave `Θ(N)` for ANY family and
tensoring adds no single-cut capacity (each priced position localizes to ONE group — no
cross-group amplification at one cut); (iii) if the per-group families are near-baseline-easy
the XOR family inherits a `2N + o(N)` circuit (decomposability).  So `(2+c)N` for the tensor
family reduces to the SAME spread-forcing statement as for the single family.  The genuine
escape is CHEAP-LITERAL (index) encoding to raise `v` past `√N`, which breaks the presence-bit
detection method — a new construction, not this one.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameTensorFamily

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval

variable {v m' g : ℕ}

/-- The satisfying-witness count of one group, in `ZMod 2`. -/
def groupCount (Bk : Fin m' → Finset (Lit v)) : ZMod 2 :=
  ((Finset.univ.filter (fun a => instSat a Bk)).card : ZMod 2)

/-- **THE TENSOR FAMILY VALUE**: the XOR of the per-group count parities. -/
def tensorParity (BB : Fin g → Fin m' → Finset (Lit v)) : ZMod 2 :=
  ∑ γ : Fin g, groupCount (BB γ)

/-- **The per-group identification (proved)**: the group count parity is `1` exactly when the
existing `parityFamily` fires. -/
theorem groupCount_eq_parityFamily (Bk : Fin m' → Finset (Lit v)) :
    (groupCount Bk = 1) ↔ (parityFamily Bk = true) := by
  unfold groupCount parityFamily
  rw [decide_eq_true_eq]
  set c := (Finset.univ.filter (fun a => instSat a Bk)).card with hc
  have hdvd : ((c : ℕ) : ZMod 2) = 0 ↔ 2 ∣ c := CharP.cast_eq_zero_iff (ZMod 2) 2 c
  have hz : ∀ z : ZMod 2, (z = 1) ↔ (z ≠ 0) := by decide
  rw [hz, ne_eq, hdvd]
  omega

/-- **THE SINGLE-DIFFERENCE SHIFT (proved)**: a change confined to group `γ*` shifts the
tensor value by exactly that group's count change. -/
theorem tensorParity_single_diff (BB BB' : Fin g → Fin m' → Finset (Lit v))
    (γstar : Fin g) (hoff : ∀ γ, γ ≠ γstar → BB' γ = BB γ) :
    tensorParity BB' - tensorParity BB = groupCount (BB' γstar) - groupCount (BB γstar) := by
  unfold tensorParity
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single γstar]
  · intro γ _ hγ
    rw [hoff γ hγ, sub_self]
  · intro h
    exact absurd (Finset.mem_univ γstar) h

/-- **THE LOCALIZATION (proved)**: the tensor family flips iff the changed group flips —
detection reduces to one group's own `F₂^{v'}` parity, unconstrained by the other groups. -/
theorem tensor_detect_localizes (BB BB' : Fin g → Fin m' → Finset (Lit v))
    (γstar : Fin g) (hoff : ∀ γ, γ ≠ γstar → BB' γ = BB γ) :
    tensorParity BB' ≠ tensorParity BB
      ↔ groupCount (BB' γstar) ≠ groupCount (BB γstar) := by
  have hshift := tensorParity_single_diff BB BB' γstar hoff
  constructor
  · intro h hc
    apply h
    have : tensorParity BB' - tensorParity BB = 0 := by rw [hshift, hc, sub_self]
    have h2 : tensorParity BB' = tensorParity BB := by
      have := sub_eq_zero.mp this
      exact this
    exact h2
  · intro h hc
    apply h
    rw [hc, sub_self] at hshift
    exact sub_eq_zero.mp hshift.symm

end PallLean.Paper93.DeepMath.PathB.NFrameTensorFamily

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTensorFamily.groupCount_eq_parityFamily
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTensorFamily.tensorParity_single_diff
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTensorFamily.tensor_detect_localizes
