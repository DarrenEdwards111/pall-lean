import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityTwoPoint
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityProbe

/-!
# N-Frame: the parity drag — the capacity feed

Rung 28b of the arc (… → two-point comparison → **parity drag**).  The tuple family over the
priced positions, fed to the engine's `cut_row_capacity` (f-generic — no re-proof): a row
family indexed by the subsets of `V`, pairwise distinguished by probes, prices `|V| ≤ j`.

  `parity_tuple_drag` — **PROVED, THE DRAG**: for any cut factorization of
        `parityFamilyBits` and any priced position set `V` with a tuple-faithful row family
        (`hrow_read`) and per-pair probe distinctness (`hdist`), the cut width bounds the
        priced mass: `V.card ≤ j`.

## Honest scope

`hdist` is the interface rung 28c discharges: for each pair of tuples, a probe built by
`probeOn` whose decoded mixes satisfy the `parity_two_point` package (pins + shared scaffold
cutting the witness space to a pair, kill-cost liveness supplying the pins, transversal
independence supplying `w` and `a₀`).  The counting that makes `|V| = Θ(T)` at a moderate
band — Markov block selection, the expander-affine codebook, the kill-cost arithmetic — is
rung 28c/29 territory.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameParityDrag

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval
open PallLean.Paper93.DeepMath.PathB.NFrameParityLayout
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {v m L N : ℕ}

set_option maxHeartbeats 1600000 in
/-- **THE PARITY DRAG (proved)**: a tuple-faithful, pairwise-distinguished row family over
the priced positions forces `V.card ≤ j` against any cut factorization of the parity
family. -/
theorem parity_tuple_drag (code : Fin L → Lit v) (hfit : m * L ≤ N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (parityFamilyBits code hfit) S j)
    (V : Finset (Fin m × Fin L))
    (rowOf : Finset (Fin m × Fin L) → (Fin N → Bool))
    (hrow_read : ∀ E ∈ V.powerset, ∀ q ∈ V,
      rowOf E (xbit hfit q.1 q.2) = decide (q ∈ E))
    (hdist : ∀ E ∈ V.powerset, ∀ E' ∈ V.powerset, E ≠ E' →
      ∃ x, parityFamilyBits code hfit (mixOn Sᶜ x (rowOf E))
        ≠ parityFamilyBits code hfit (mixOn Sᶜ x (rowOf E'))) :
    V.card ≤ j := by
  classical
  set Y : Finset (Fin N → Bool) := V.powerset.image rowOf with hY
  have hYcard : Y.card = 2 ^ V.card := by
    rw [hY, Finset.card_image_of_injOn, Finset.card_powerset]
    intro E hE E' hE' heq
    have hEp : E ∈ V.powerset := Finset.mem_coe.mp hE
    have hE'p : E' ∈ V.powerset := Finset.mem_coe.mp hE'
    have hEsub := Finset.mem_powerset.mp hEp
    have hE'sub := Finset.mem_powerset.mp hE'p
    ext q
    by_cases hq : q ∈ V
    · have h := congrFun heq (xbit hfit q.1 q.2)
      rw [hrow_read E hEp q hq, hrow_read E' hE'p q hq] at h
      constructor
      · intro hmem
        exact of_decide_eq_true (by rw [← h]; exact decide_eq_true hmem)
      · intro hmem
        exact of_decide_eq_true (by rw [h]; exact decide_eq_true hmem)
    · constructor
      · intro hmem
        exact absurd (hEsub hmem) hq
      · intro hmem
        exact absurd (hE'sub hmem) hq
  have hYdist : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' →
      ∃ x, parityFamilyBits code hfit (mixOn Sᶜ x y)
        ≠ parityFamilyBits code hfit (mixOn Sᶜ x y') := by
    intro y hy y' hy' hne
    rw [hY] at hy hy'
    obtain ⟨E, hEmem, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨E', hE'mem, rfl⟩ := Finset.mem_image.mp hy'
    have hEne : E ≠ E' := fun hcon => hne (by rw [hcon])
    exact hdist E hEmem E' hE'mem hEne
  have hcap := cut_row_capacity (parityFamilyBits code hfit) S j hcut Y hYdist
  rw [hYcard] at hcap
  by_contra hcon
  push_neg at hcon
  have hlt : (2 : ℕ) ^ j < 2 ^ V.card :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameParityDrag

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityDrag.parity_tuple_drag
