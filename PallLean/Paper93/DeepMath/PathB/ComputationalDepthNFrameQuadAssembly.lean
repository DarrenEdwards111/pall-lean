import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameQuadLayout

/-!
# N-Frame: the quadratic product assembly — multi-difference detection (28d–28g analogs)

Route H drag rung (… → quadratic layout/capacity → **product assembly**).  The tuple family
prices MANY quadratic targets at one balanced cut; a pair of tuples differs at MANY positions,
so the single-insert transfer (`gParity_detect_layout`) does not apply.  The multi-difference
engine, mirroring rung 28a's `parity_two_point` at the layout level: with the KIT BLANKET
(non-target data blocks carry the tautology `aff 0 0`, so they are satisfied regardless of the
tuple differences) and the RESERVE probe-fixed (pin blocks decode identically in both rows),
the non-target predicate agrees between the two rows — so the two-point comparison sees only
the target block's quadratic literal, however many positions differ.

  `gBlockSat_of_taut` — **PROVED**: a block containing the tautology `GLit.aff 0 0` is
        satisfied at every witness (the kit-absorption atom).
  `gParity_pair_dist_multi` — **PROVED, THE MULTI-DIFFERENCE ENGINE**: two rows whose target
        block decodes to `Tsh ∪ Tt` / `Tsh ∪ Tt'` (`Tt'` carrying the quadratic target,
        `Tt` origin-false and origin-`w`-invisible), whose reserve blocks decode identically,
        and whose other data blocks are kit, get DIFFERENT family parities — the layout-level
        per-pair `hdist` for the quadratic tuple drag, multi-difference native.

## Honest scope — what this closes (Route H)

`gParity_pair_dist_multi` discharges `gParity_tuple_drag`'s per-pair `hdist` for arbitrary
tuple differences: together they are the multi-difference quadratic drag.  What remains for a
concrete `Θ(N)` bound: the explicit row-family/codebook construction (a `gRowOf` with the kit
blanket, the reserve homogeneous pins, and the per-target scaffold, discharging the `hBk`/
`hres`/`hkit`/`hpair` package per pair — mechanical over a fixed codebook and reserve
transversal), and the concentration analysis at the raised local rank.  The engine here is
the 28a/28e content; the construction is the 28g bookkeeping.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameQuadAssembly

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval
open PallLean.Paper93.DeepMath.PathB.NFrameParityLayout
open PallLean.Paper93.DeepMath.PathB.NFrameQuadTwoPoint
open PallLean.Paper93.DeepMath.PathB.NFrameQuadLayout
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {v m L N : ℕ}

/-- **The kit-absorption atom (proved)**: a block carrying the tautology `aff 0 0` is
satisfied at every witness. -/
theorem gBlockSat_of_taut (a : Fin v → ZMod 2) (T : Finset (GLit v))
    (h : GLit.aff 0 0 ∈ T) : gBlockSat a T := by
  refine ⟨GLit.aff 0 0, h, ?_⟩
  change dotp (0 : Fin v → ZMod 2) a = 0
  unfold dotp
  simp

set_option maxHeartbeats 1600000 in
/-- **THE MULTI-DIFFERENCE ENGINE (proved)**: with the kit blanket (non-target data blocks
carry the tautology) and the reserve probe-fixed, the non-target predicate agrees between the
two rows; the two-point comparison then flips on the target block's quadratic literal alone —
however many positions differ. -/
theorem gParity_pair_dist_multi (code : Fin L → GLit v) (hfit : m * L ≤ N)
    (S : Finset (Fin N)) (x y y' : Fin N → Bool)
    (cstar : Fin m) (i j : Fin v) (w : Fin v → ZMod 2)
    (Tsh Tt Tt' : Finset (GLit v)) (RS : Finset (Fin m))
    (hqw : w i * w j = 1)
    (hBk : gDecodeBlock code hfit (mixOn Sᶜ x y) cstar = Tsh ∪ Tt)
    (hBk' : gDecodeBlock code hfit (mixOn Sᶜ x y') cstar = Tsh ∪ Tt')
    (htar' : GLit.quad i j 1 ∈ Tt')
    (h0t : ∀ ℓ ∈ Tt, ¬ gLitHolds 0 ℓ)
    (h0t' : ∀ ℓ ∈ Tt', ¬ gLitHolds 0 ℓ)
    (hkert : ∀ ℓ ∈ Tt, gLitHolds 0 ℓ ↔ gLitHolds w ℓ)
    (hres : ∀ c ∈ RS,
      gDecodeBlock code hfit (mixOn Sᶜ x y') c = gDecodeBlock code hfit (mixOn Sᶜ x y) c)
    (hkitY : ∀ c, c ≠ cstar → c ∉ RS →
      GLit.aff 0 0 ∈ gDecodeBlock code hfit (mixOn Sᶜ x y) c)
    (hkitY' : ∀ c, c ≠ cstar → c ∉ RS →
      GLit.aff 0 0 ∈ gDecodeBlock code hfit (mixOn Sᶜ x y') c)
    (hpair : ∀ a : Fin v → ZMod 2,
      ((∀ c, c ≠ cstar → gBlockSat a (gDecodeBlock code hfit (mixOn Sᶜ x y) c))
        ∧ ∀ ℓ ∈ Tsh, ¬ gLitHolds a ℓ)
        ↔ (a = 0 ∨ a = w)) :
    gParityFamilyBits code hfit (mixOn Sᶜ x y)
      ≠ gParityFamilyBits code hfit (mixOn Sᶜ x y') := by
  classical
  -- the non-target predicate agrees: reserve blocks identical, data blocks kit
  have hnt : ∀ a : Fin v → ZMod 2,
      (∀ c, c ≠ cstar → gBlockSat a (gDecodeBlock code hfit (mixOn Sᶜ x y) c))
        ↔ (∀ c, c ≠ cstar → gBlockSat a (gDecodeBlock code hfit (mixOn Sᶜ x y') c)) := by
    intro a
    constructor
    · intro h c hc
      by_cases hcRS : c ∈ RS
      · rw [hres c hcRS]
        exact h c hc
      · exact gBlockSat_of_taut a _ (hkitY' c hc hcRS)
    · intro h c hc
      by_cases hcRS : c ∈ RS
      · rw [← hres c hcRS]
        exact h c hc
      · exact gBlockSat_of_taut a _ (hkitY c hc hcRS)
  unfold gParityFamilyBits
  exact quad_two_point
    (fun c => gDecodeBlock code hfit (mixOn Sᶜ x y) c)
    (fun c => gDecodeBlock code hfit (mixOn Sᶜ x y') c)
    cstar Tsh Tt Tt' w i j hqw hBk hBk' htar' h0t h0t' hkert hnt hpair

set_option maxHeartbeats 1600000 in
/-- **THE MULTI-DIFFERENCE DRAG (proved)**: the product tuple family, each pair distinguished
by the multi-difference engine, prices `V.card ≤ j`.  The per-pair package (target block,
coordinates, witness, and the decode facts) is supplied by `hpkg`; the concrete row-family
construction that realizes it over a fixed codebook is the remaining bookkeeping. -/
theorem gParity_multi_drag (code : Fin L → GLit v) (hfit : m * L ≤ N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (gParityFamilyBits code hfit) S j)
    (V : Finset (Fin m × Fin L))
    (rowOf : Finset (Fin m × Fin L) → (Fin N → Bool))
    (hrow_read : ∀ E ∈ V.powerset, ∀ q ∈ V,
      rowOf E (xbit hfit q.1 q.2) = decide (q ∈ E))
    (hpkg : ∀ E ∈ V.powerset, ∀ E' ∈ V.powerset, E ≠ E' →
      ∃ (x : Fin N → Bool) (cstar : Fin m) (i j : Fin v) (w : Fin v → ZMod 2)
        (Tsh Tt Tt' : Finset (GLit v)) (RS : Finset (Fin m)),
        w i * w j = 1
        ∧ gDecodeBlock code hfit (mixOn Sᶜ x (rowOf E)) cstar = Tsh ∪ Tt
        ∧ gDecodeBlock code hfit (mixOn Sᶜ x (rowOf E')) cstar = Tsh ∪ Tt'
        ∧ GLit.quad i j 1 ∈ Tt'
        ∧ (∀ ℓ ∈ Tt, ¬ gLitHolds 0 ℓ)
        ∧ (∀ ℓ ∈ Tt', ¬ gLitHolds 0 ℓ)
        ∧ (∀ ℓ ∈ Tt, gLitHolds 0 ℓ ↔ gLitHolds w ℓ)
        ∧ (∀ c ∈ RS, gDecodeBlock code hfit (mixOn Sᶜ x (rowOf E')) c
            = gDecodeBlock code hfit (mixOn Sᶜ x (rowOf E)) c)
        ∧ (∀ c, c ≠ cstar → c ∉ RS →
            GLit.aff 0 0 ∈ gDecodeBlock code hfit (mixOn Sᶜ x (rowOf E)) c)
        ∧ (∀ c, c ≠ cstar → c ∉ RS →
            GLit.aff 0 0 ∈ gDecodeBlock code hfit (mixOn Sᶜ x (rowOf E')) c)
        ∧ (∀ a : Fin v → ZMod 2,
            ((∀ c, c ≠ cstar → gBlockSat a (gDecodeBlock code hfit (mixOn Sᶜ x (rowOf E)) c))
              ∧ ∀ ℓ ∈ Tsh, ¬ gLitHolds a ℓ)
              ↔ (a = 0 ∨ a = w))) :
    V.card ≤ j := by
  apply gParity_tuple_drag code hfit hcut V rowOf hrow_read
  intro E hE E' hE' hne
  obtain ⟨x, cstar, i, j', w, Tsh, Tt, Tt', RS, hqw, hBk, hBk', htar', h0t, h0t',
    hkert, hres, hkitY, hkitY', hpair⟩ := hpkg E hE E' hE' hne
  exact ⟨x, gParity_pair_dist_multi code hfit S x (rowOf E) (rowOf E') cstar i j' w
    Tsh Tt Tt' RS hqw hBk hBk' htar' h0t h0t' hkert hres hkitY hkitY' hpair⟩

end PallLean.Paper93.DeepMath.PathB.NFrameQuadAssembly

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadAssembly.gBlockSat_of_taut
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadAssembly.gParity_pair_dist_multi
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadAssembly.gParity_multi_drag
