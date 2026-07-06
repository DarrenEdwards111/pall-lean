import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameQuadSupply
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityLayout

/-!
# N-Frame: the quadratic layout & capacity transfer — GLit analogs of rungs 28b/28c

Route H drag rung (… → origin-pinning supply → **quadratic layout/capacity**).  The bit-level
realization of the generalized (`GLit`) family and the capacity feed: the drag now runs on
actual circuit inputs `Fin N → Bool`, reading bits into `GLit` blocks, and the cut width
bounds the priced mass.  The capacity engine `cut_row_capacity` is `f`-generic, so it applies
to the `GLit` family with no re-proof — the transfer is verbatim.

  `gDecodeBlock` / `gParityFamilyBits` — the bit realization: a block reads its `L` selector
        bits, the codebook maps ON bits to `GLit`s, `gParityFamily` scores the grid.
  `gDecodeBlock_congr` / `gParityFamilyBits_congr` — **PROVED**: the family depends on the
        input only through the block grid.
  `gParity_tuple_drag` — **PROVED, THE CAPACITY (28b analog)**: any tuple-faithful,
        pairwise-distinguished row family over the priced positions forces `V.card ≤ j`
        against a cut factorization of `gParityFamilyBits`.
  `gParity_detect_layout` — **PROVED, THE DETECTION TRANSFER (28c core)**: two bit-rows
        differing at ONE target index position give mixes whose decodes differ by inserting
        exactly the target `GLit`; with the quadratic origin package (`hqw`, `hpair`) on the
        decoded mix, the concrete family flips — the layout-level per-pair `hdist` for the
        quadratic target.

## Honest scope — what this closes (Route H)

The origin-pinned quadratic drag now runs on real inputs: `gParity_tuple_drag` is the
capacity feed, `gParity_detect_layout` transfers `quad_two_point` to the bit level.  What
remains for a `Θ(N)` quadratic bound: the PRODUCT (multi-difference) tuple assembly — placing
many origin-pinned quadratic targets at one balanced cut with per-pair packages from a
transversal — and the concentration analysis at the raised local rank.  The single-position
transfer here is the atom; the product assembly (28d–28g analogs) is the counting rung.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameQuadLayout

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval
open PallLean.Paper93.DeepMath.PathB.NFrameParityLayout
open PallLean.Paper93.DeepMath.PathB.NFrameQuadTwoPoint
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {v m L N : ℕ}

/-! ### The bit realization -/

/-- The decoded `GLit` content of block `c`: the codebook image of its ON selector bits. -/
noncomputable def gDecodeBlock (code : Fin L → GLit v) (hfit : m * L ≤ N)
    (x : Fin N → Bool) (c : Fin m) : Finset (GLit v) :=
  (Finset.univ.filter (fun i : Fin L => x (xbit hfit c i) = true)).image code

/-- **THE CONCRETE GENERALIZED FAMILY**: the parity of the decoded `GLit` block family. -/
noncomputable def gParityFamilyBits (code : Fin L → GLit v) (hfit : m * L ≤ N)
    (x : Fin N → Bool) : Bool :=
  gParityFamily (fun c => gDecodeBlock code hfit x c)

theorem gDecodeBlock_congr (code : Fin L → GLit v) (hfit : m * L ≤ N)
    {x y : Fin N → Bool} (c : Fin m)
    (h : ∀ i : Fin L, x (xbit hfit c i) = y (xbit hfit c i)) :
    gDecodeBlock code hfit x c = gDecodeBlock code hfit y c := by
  unfold gDecodeBlock
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [h i]

theorem gParityFamilyBits_congr (code : Fin L → GLit v) (hfit : m * L ≤ N)
    {x y : Fin N → Bool}
    (h : ∀ (c : Fin m) (i : Fin L), x (xbit hfit c i) = y (xbit hfit c i)) :
    gParityFamilyBits code hfit x = gParityFamilyBits code hfit y := by
  unfold gParityFamilyBits
  congr 1
  funext c
  exact gDecodeBlock_congr code hfit c (h c)

/-! ### The capacity transfer (28b) -/

set_option maxHeartbeats 1600000 in
/-- **THE CAPACITY (proved, 28b analog)**: a tuple-faithful, pairwise-distinguished row family
over the priced positions forces `V.card ≤ j` against any cut factorization of the
generalized family. -/
theorem gParity_tuple_drag (code : Fin L → GLit v) (hfit : m * L ≤ N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (gParityFamilyBits code hfit) S j)
    (V : Finset (Fin m × Fin L))
    (rowOf : Finset (Fin m × Fin L) → (Fin N → Bool))
    (hrow_read : ∀ E ∈ V.powerset, ∀ q ∈ V,
      rowOf E (xbit hfit q.1 q.2) = decide (q ∈ E))
    (hdist : ∀ E ∈ V.powerset, ∀ E' ∈ V.powerset, E ≠ E' →
      ∃ x, gParityFamilyBits code hfit (mixOn Sᶜ x (rowOf E))
        ≠ gParityFamilyBits code hfit (mixOn Sᶜ x (rowOf E'))) :
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
      ∃ x, gParityFamilyBits code hfit (mixOn Sᶜ x y)
        ≠ gParityFamilyBits code hfit (mixOn Sᶜ x y') := by
    intro y hy y' hy' hne
    rw [hY] at hy hy'
    obtain ⟨E, hEmem, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨E', hE'mem, rfl⟩ := Finset.mem_image.mp hy'
    have hEne : E ≠ E' := fun hcon => hne (by rw [hcon])
    exact hdist E hEmem E' hE'mem hEne
  have hcap := cut_row_capacity (gParityFamilyBits code hfit) S j hcut Y hYdist
  rw [hYcard] at hcap
  by_contra hcon
  push_neg at hcon
  have hlt : (2 : ℕ) ^ j < 2 ^ V.card :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  omega

/-! ### The detection transfer (28c core) -/

set_option maxHeartbeats 1600000 in
/-- **THE DETECTION TRANSFER (proved, 28c core)**: two bit-rows differing at one target index
position give mixes whose decodes differ by inserting exactly the target `GLit`; with the
quadratic origin package (`hqw`, `hpair`) on the decoded mix, the concrete family flips. -/
theorem gParity_detect_layout (code : Fin L → GLit v) (hfit : m * L ≤ N)
    (S : Finset (Fin N)) (x y y' : Fin N → Bool)
    (cstar : Fin m) (istar : Fin L) (i j : Fin v)
    (w : Fin v → ZMod 2)
    (hcode : code istar = GLit.quad i j 1)
    (hqw : w i * w j = 1)
    (hpos : xbit hfit cstar istar ∉ Sᶜ)
    (hy : y (xbit hfit cstar istar) = false)
    (hy' : y' (xbit hfit cstar istar) = true)
    (hagree : ∀ p : Fin N, p ≠ xbit hfit cstar istar → y p = y' p)
    (hpair : ∀ a : Fin v → ZMod 2,
      ((∀ c, c ≠ cstar → gBlockSat a (gDecodeBlock code hfit (mixOn Sᶜ x y) c))
        ∧ ∀ ℓ ∈ gDecodeBlock code hfit (mixOn Sᶜ x y) cstar, ¬ gLitHolds a ℓ)
        ↔ (a = 0 ∨ a = w)) :
    gParityFamilyBits code hfit (mixOn Sᶜ x y)
      ≠ gParityFamilyBits code hfit (mixOn Sᶜ x y') := by
  classical
  -- geometry: the primed decode inserts exactly the target literal at cstar
  have hBt : gDecodeBlock code hfit (mixOn Sᶜ x y') cstar
      = insert (GLit.quad i j 1) (gDecodeBlock code hfit (mixOn Sᶜ x y) cstar) := by
    rw [← hcode]
    unfold gDecodeBlock
    rw [← Finset.image_insert]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hkk : k = istar
    · subst hkk
      constructor
      · intro _
        exact Or.inl rfl
      · intro _
        rw [mix_read_row x y' hpos]
        exact hy'
    · have hpne : xbit hfit cstar k ≠ xbit hfit cstar istar := by
        intro hc
        exact hkk (xbit_inj hfit hc).2
      have hval : mixOn Sᶜ x y' (xbit hfit cstar k)
          = mixOn Sᶜ x y (xbit hfit cstar k) := by
        by_cases hmem : xbit hfit cstar k ∈ Sᶜ
        · rw [mix_read_probe x y' hmem, mix_read_probe x y hmem]
        · rw [mix_read_row x y' hmem, mix_read_row x y hmem]
          exact (hagree _ hpne).symm
      constructor
      · intro h
        refine Or.inr ?_
        rw [← hval]
        exact h
      · rintro (h | h)
        · exact absurd h hkk
        · rw [hval]
          exact h
  -- non-target blocks decode identically
  have hBr : ∀ c, c ≠ cstar →
      gDecodeBlock code hfit (mixOn Sᶜ x y') c = gDecodeBlock code hfit (mixOn Sᶜ x y) c := by
    intro c hc
    apply gDecodeBlock_congr
    intro k
    have hpne : xbit hfit c k ≠ xbit hfit cstar istar := by
      intro hcon
      exact hc (xbit_inj hfit hcon).1
    by_cases hmem : xbit hfit c k ∈ Sᶜ
    · rw [mix_read_probe x y' hmem, mix_read_probe x y hmem]
    · rw [mix_read_row x y' hmem, mix_read_row x y hmem]
      exact (hagree _ hpne).symm
  -- the non-target counts agree
  have hnt : ∀ a : Fin v → ZMod 2,
      (∀ c, c ≠ cstar → gBlockSat a (gDecodeBlock code hfit (mixOn Sᶜ x y) c))
        ↔ (∀ c, c ≠ cstar → gBlockSat a (gDecodeBlock code hfit (mixOn Sᶜ x y') c)) := by
    intro a
    constructor
    · intro h c hc
      rw [hBr c hc]
      exact h c hc
    · intro h c hc
      rw [← hBr c hc]
      exact h c hc
  have hT' : gDecodeBlock code hfit (mixOn Sᶜ x y') cstar
      = gDecodeBlock code hfit (mixOn Sᶜ x y) cstar ∪ {GLit.quad i j 1} := by
    rw [hBt, Finset.insert_eq, Finset.union_comm]
  have h0t' : ∀ ℓ ∈ ({GLit.quad i j 1} : Finset (GLit v)), ¬ gLitHolds 0 ℓ := by
    intro ℓ hℓ
    rw [Finset.mem_singleton] at hℓ
    subst hℓ
    change ¬ ((0 : Fin v → ZMod 2) i * (0 : Fin v → ZMod 2) j = 1)
    simp
  unfold gParityFamilyBits
  exact quad_two_point
    (fun c => gDecodeBlock code hfit (mixOn Sᶜ x y) c)
    (fun c => gDecodeBlock code hfit (mixOn Sᶜ x y') c)
    cstar (gDecodeBlock code hfit (mixOn Sᶜ x y) cstar) ∅ {GLit.quad i j 1}
    w i j hqw (Finset.union_empty _).symm hT' (Finset.mem_singleton_self _)
    (fun ℓ hℓ => absurd hℓ (Finset.notMem_empty ℓ)) h0t'
    (fun ℓ hℓ => absurd hℓ (Finset.notMem_empty ℓ)) hnt hpair

end PallLean.Paper93.DeepMath.PathB.NFrameQuadLayout

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadLayout.gParityFamilyBits_congr
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadLayout.gParity_tuple_drag
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadLayout.gParity_detect_layout
