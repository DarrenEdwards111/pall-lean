import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameGenericRootShape

/-!
# N-Frame: the standard drag — the codebook glue at real cuts

Work package 2, drag layer (… → generic root shape → **standard drag**).  The last
bookkeeping item: the priced set is parametrized by block–coordinate pairs `D` with a
valuation `val`, the per-target functions decode through `sIdx`, and the scaffold no-lose is
CONSTRUCTED — `stdSCR` is defined as exactly the row-side scaffold positions, so the
`hscaffold` partition is `filter P ∪ filter ¬P = all`, a theorem rather than a hypothesis.

  `pricedCoords` / `scafIdx` / `stdV` / `stdSCR` — the constructions.
  `sCoord` / `sVal` — the index decoders with their reads.
  `stdV_card` — `|stdV| = |D|` (the priced mass is the pair count).
  `parity_std_drag` — **PROVED, THE GLUED DRAG**: under a cut factorization of the
        standard-codebook parity family, `D.card ≤ j` — with exactly ONE
        expander-conditional hypothesis class left (`hlive`: the κ-assigned pin selector
        positions at the reserve are probe-side; `hTautProbe` and `hVS` are the
        side-placement bookkeeping of the counting round).

## Honest scope

The remaining distance to the unconditional `(2+c)N`: supplying `(D, val, κ)` with
`|D| = Θ(T)` and the side placements at real balanced cuts — the kill-accounting under the
certified-expander interface (canonical instantiation Ramanujan; any `c·d > 1` certificate
suffices).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameParityStdDrag

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval
open PallLean.Paper93.DeepMath.PathB.NFrameParityLayout
open PallLean.Paper93.DeepMath.PathB.NFrameParityCodebook
open PallLean.Paper93.DeepMath.PathB.NFrameParityStdCode
open PallLean.Paper93.DeepMath.PathB.NFrameParityAssembly
open PallLean.Paper93.DeepMath.PathB.NFrameParityDrag
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {v m N : ℕ}

/-! ### Decoders -/

/-- The coordinate decoder (total; junk-safe via `% v`). -/
def sCoord (hv : 0 < v) (i : Fin (stdL v)) : Fin v :=
  ⟨(i.val - 1) / 2 % v, Nat.mod_lt _ hv⟩

/-- The value decoder. -/
def sVal {v : ℕ} (i : Fin (stdL v)) : ZMod 2 := (((i.val - 1) % 2 : ℕ) : ZMod 2)

theorem sCoord_sIdx (hv : 0 < v) (j : Fin v) (b : ZMod 2) :
    sCoord hv (sIdx v j b) = j := by
  have hb : b.val < 2 := ZMod.val_lt b
  have hj := j.isLt
  apply Fin.ext
  show (1 + 2 * j.val + b.val - 1) / 2 % v = j.val
  have h1 : (1 + 2 * j.val + b.val - 1) / 2 = j.val := by omega
  rw [h1, Nat.mod_eq_of_lt hj]

theorem sVal_sIdx (v : ℕ) (j : Fin v) (b : ZMod 2) :
    sVal (sIdx v j b) = b := by
  have hb : b.val < 2 := ZMod.val_lt b
  show (((1 + 2 * j.val + b.val - 1) % 2 : ℕ) : ZMod 2) = b
  have h2 : (1 + 2 * j.val + b.val - 1) % 2 = b.val := by omega
  rw [h2]
  have hcast : ∀ x : ZMod 2, ((x.val : ℕ) : ZMod 2) = x := by decide
  exact hcast b

/-! ### The constructions -/

/-- The priced coordinates of a block. -/
def pricedCoords (D : Finset (Fin m × Fin v)) (c : Fin m) : Finset (Fin v) :=
  (D.filter (fun d => d.1 = c)).image Prod.snd

/-- The scaffold indices of a block: value-1 singletons on the unpriced coordinates. -/
def scafIdx (v : ℕ) (D : Finset (Fin m × Fin v)) (c : Fin m) : Finset (Fin (stdL v)) :=
  ((Finset.univ : Finset (Fin v)) \ pricedCoords D c).image (fun j' => sIdx v j' 1)

/-- The priced position set. -/
def stdV (v : ℕ) (D : Finset (Fin m × Fin v)) (val : Fin m → Fin v → ZMod 2) :
    Finset (Fin m × Fin (stdL v)) :=
  D.image (fun d => (d.1, sIdx v d.2 (val d.1 d.2)))

/-- The row-side scaffold positions: the no-lose, constructed. -/
def stdSCR (hfit : m * stdL v ≤ N) (S : Finset (Fin N))
    (D : Finset (Fin m × Fin v)) : Finset (Fin m × Fin (stdL v)) :=
  (D.image Prod.fst).biUnion (fun c =>
    ((scafIdx v D c).filter (fun i => xbit hfit c i ∉ Sᶜ)).image (fun i => (c, i)))

theorem stdV_mem (D : Finset (Fin m × Fin v)) (val : Fin m → Fin v → ZMod 2)
    {q : Fin m × Fin (stdL v)} :
    q ∈ stdV v D val ↔ ∃ d ∈ D, q = (d.1, sIdx v d.2 (val d.1 d.2)) := by
  unfold stdV
  rw [Finset.mem_image]
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d, hd, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d, hd, rfl⟩

/-- **The priced mass (proved)**: `|stdV| = |D|`. -/
theorem stdV_card (D : Finset (Fin m × Fin v)) (val : Fin m → Fin v → ZMod 2) :
    (stdV v D val).card = D.card := by
  unfold stdV
  apply Finset.card_image_of_injOn
  intro d _ d' _ h
  injection h with h1 h2
  exact Prod.ext h1 (sIdx_inj v h2).1

theorem stdSCR_slice (hfit : m * stdL v ≤ N) (S : Finset (Fin N))
    (D : Finset (Fin m × Fin v)) {c : Fin m} (hc : c ∈ D.image Prod.fst) :
    ((stdSCR hfit S D).filter (fun r => r.1 = c)).image Prod.snd
      = (scafIdx v D c).filter (fun i => xbit hfit c i ∉ Sᶜ) := by
  ext i
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨r, ⟨hrSCR, hrc⟩, rfl⟩
    unfold stdSCR at hrSCR
    obtain ⟨c', -, hr⟩ := Finset.mem_biUnion.mp hrSCR
    obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hr
    rw [Finset.mem_filter] at hi'
    have hcc : c' = c := hrc
    rw [← hcc]
    exact ⟨hi'.1, hi'.2⟩
  · rintro ⟨hscaf, hside⟩
    refine ⟨(c, i), ⟨?_, rfl⟩, rfl⟩
    unfold stdSCR
    apply Finset.mem_biUnion.mpr
    refine ⟨c, hc, ?_⟩
    apply Finset.mem_image_of_mem
    rw [Finset.mem_filter]
    exact ⟨hscaf, hside⟩

set_option maxHeartbeats 3200000 in
/-- **THE GLUED DRAG (proved)**: under a cut factorization of the standard-codebook parity
family, `D.card ≤ j` — with `hlive` the single expander-conditional class remaining. -/
theorem parity_std_drag (hv : 0 < v) (hfit : m * stdL v ≤ N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (parityFamilyBits (stdCode v hv) hfit) S j)
    (RS : Finset (Fin m))
    (D : Finset (Fin m × Fin v))
    (val : Fin m → Fin v → ZMod 2)
    (κ : Fin m × Fin (stdL v) → Fin m → Fin v)
    (hDRS : ∀ d ∈ D, d.1 ∉ RS)
    (hκmem : ∀ q ∈ stdV v D val, ∀ c ∈ RS,
      (q.1, κ q c) ∈ D ∧ κ q c ≠ sCoord hv q.2)
    (hκcov : ∀ q ∈ stdV v D val, ∀ j' : Fin v,
      (q.1, j') ∈ D → j' ≠ sCoord hv q.2 → ∃ c ∈ RS, κ q c = j')
    (hVS : ∀ d ∈ D, xbit hfit d.1 (sIdx v d.2 (val d.1 d.2)) ∉ Sᶜ)
    (hTautProbe : ∀ d ∈ D, xbit hfit d.1 (tautIdxStd v) ∈ Sᶜ)
    (hlive : ∀ q ∈ stdV v D val, ∀ c ∈ RS,
      xbit hfit c (sIdx v (κ q c) (val q.1 (κ q c) + 1)) ∈ Sᶜ) :
    D.card ≤ j := by
  classical
  rw [← stdV_card D val]
  apply parity_assembled_drag (stdCode v hv) hfit (tautIdxStd v) RS
    (stdSCR hfit S D) (stdV v D val) hcut
    (fun q c => sIdx v (κ q c) (val q.1 (κ q c) + 1))
    (fun q => scafIdx v D q.1)
    (fun q => sCoord hv q.2)
    (fun q => sVal q.2)
    (fun q => (pricedCoords D q.1).erase (sCoord hv q.2))
    (fun q => val q.1)
  -- hVt
  · intro q hq
    obtain ⟨d, hd, rfl⟩ := (stdV_mem D val).mp hq
    exact sIdx_ne_taut v d.2 (val d.1 d.2)
  -- hVSCR
  · intro q hq hqSCR
    obtain ⟨d, hd, rfl⟩ := (stdV_mem D val).mp hq
    unfold stdSCR at hqSCR
    obtain ⟨c', -, hr⟩ := Finset.mem_biUnion.mp hqSCR
    obtain ⟨i', hi', heq⟩ := Finset.mem_image.mp hr
    injection heq with hfst hsnd
    rw [Finset.mem_filter] at hi'
    unfold scafIdx at hi'
    obtain ⟨j', hj', hij⟩ := Finset.mem_image.mp hi'.1
    rw [Finset.mem_sdiff] at hj'
    apply hj'.2
    unfold pricedCoords
    have hjj : j' = d.2 := by
      have h0 : sIdx v j' 1 = sIdx v d.2 (val d.1 d.2) := hij.trans hsnd
      exact (sIdx_inj v h0).1
    rw [Finset.mem_image]
    refine ⟨d, ?_, hjj.symm⟩
    rw [Finset.mem_filter]
    exact ⟨hd, hfst.symm⟩
  -- hVRS
  · intro q hq
    obtain ⟨d, hd, rfl⟩ := (stdV_mem D val).mp hq
    exact hDRS d hd
  -- hSCRRS
  · intro r hr
    unfold stdSCR at hr
    obtain ⟨c', hc', hrm⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨i', -, rfl⟩ := Finset.mem_image.mp hrm
    obtain ⟨d, hd, hdc⟩ := Finset.mem_image.mp hc'
    show c' ∉ RS
    rw [← hdc]
    exact hDRS d hd
  -- hVS
  · intro q hq
    obtain ⟨d, hd, rfl⟩ := (stdV_mem D val).mp hq
    exact hVS d hd
  -- hSCRS
  · intro r hr
    unfold stdSCR at hr
    obtain ⟨c', -, hrm⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨i', hi', heq⟩ := Finset.mem_image.mp hrm
    rw [Finset.mem_filter] at hi'
    have hfst : r.1 = c' := congrArg Prod.fst heq.symm
    have hsnd : r.2 = i' := congrArg Prod.snd heq.symm
    rw [hfst, hsnd]
    exact hi'.2
  -- hTautProbe
  · intro q hq
    obtain ⟨d, hd, rfl⟩ := (stdV_mem D val).mp hq
    exact hTautProbe d hd
  -- hcodeTaut
  · exact stdCode_taut v hv
  -- hcodeStar
  · intro q hq
    obtain ⟨d, hd, rfl⟩ := (stdV_mem D val).mp hq
    show stdCode v hv (sIdx v d.2 (val d.1 d.2)) = _
    rw [stdCode_sIdx, sCoord_sIdx, sVal_sIdx]
  -- hKstar
  · intro q hq
    exact Finset.notMem_erase _ _
  -- hcodeV
  · intro q hq i hi hne
    obtain ⟨d, hd, rfl⟩ := (stdV_mem D val).mp hq
    have hiV : ((d.1, i) : Fin m × Fin (stdL v)) ∈ stdV v D val := hi
    obtain ⟨d', hd', heq⟩ := (stdV_mem D val).mp hiV
    injection heq with hfst hsnd
    refine ⟨d'.2, ?_, ?_⟩
    · rw [Finset.mem_erase]
      constructor
      · rw [sCoord_sIdx]
        intro hcon
        apply hne
        rw [hsnd, hcon, ← hfst]
      · unfold pricedCoords
        rw [Finset.mem_image]
        refine ⟨d', ?_, rfl⟩
        rw [Finset.mem_filter]
        exact ⟨hd', hfst.symm⟩
    · rw [hsnd, stdCode_sIdx, ← hfst]
  -- hpinCode
  · intro q hq c hc
    obtain ⟨hκD, hκne⟩ := hκmem q hq c hc
    refine ⟨κ q c, ?_, ?_⟩
    · rw [Finset.mem_erase]
      refine ⟨hκne, ?_⟩
      unfold pricedCoords
      rw [Finset.mem_image]
      refine ⟨(q.1, κ q c), ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨hκD, rfl⟩
    · rw [stdCode_sIdx]
  -- hpinCover
  · intro q hq j' hj'
    rw [Finset.mem_erase] at hj'
    obtain ⟨hne, hmem⟩ := hj'
    unfold pricedCoords at hmem
    obtain ⟨d', hd', hsnd⟩ := Finset.mem_image.mp hmem
    rw [Finset.mem_filter] at hd'
    have hD' : (q.1, j') ∈ D := by
      have : d' = (q.1, j') := Prod.ext hd'.2 hsnd
      rw [← this]
      exact hd'.1
    obtain ⟨c, hc, hκ⟩ := hκcov q hq j' hD' hne
    refine ⟨c, hc, ?_⟩
    rw [hκ, stdCode_sIdx]
  -- hscaffold
  · intro q hq
    obtain ⟨d, hd, rfl⟩ := (stdV_mem D val).mp hq
    have hcblocks : d.1 ∈ D.image Prod.fst := Finset.mem_image_of_mem _ hd
    rw [stdSCR_slice hfit S D hcblocks]
    have hpart : (scafIdx v D d.1).filter
        (fun i => xbit hfit d.1 i ∈ Sᶜ)
        ∪ (scafIdx v D d.1).filter (fun i => xbit hfit d.1 i ∉ Sᶜ)
        = scafIdx v D d.1 :=
      Finset.filter_union_filter_neg_eq _ _
    rw [hpart]
    -- the coordinate identity: insert (target coord) (erase ...) = pricedCoords
    have hins : insert (sCoord hv (sIdx v d.2 (val d.1 d.2)))
        ((pricedCoords D d.1).erase (sCoord hv (sIdx v d.2 (val d.1 d.2))))
        = pricedCoords D d.1 := by
      apply Finset.insert_erase
      rw [sCoord_sIdx]
      unfold pricedCoords
      rw [Finset.mem_image]
      refine ⟨d, ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨hd, rfl⟩
    rw [hins]
    unfold scafIdx
    rw [Finset.image_image]
    apply Finset.image_congr
    intro j' _
    exact stdCode_sIdx v hv j' 1
  -- hlive
  · intro q hq c hc
    exact hlive q hq c hc

end PallLean.Paper93.DeepMath.PathB.NFrameParityStdDrag

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityStdDrag.stdV_card
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityStdDrag.parity_std_drag
