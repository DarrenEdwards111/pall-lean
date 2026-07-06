import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityXCode

/-!
# N-Frame: the extended drag — `parity_route_drag` glued over the circulant codebook

Expander-discharge arc, rung E3b (… → extended codebook → **extended drag**).  The
route-drag re-glue at `xstdCode`: the priced set is again parametrized by block–coordinate
pairs `D` with a valuation `val`; the per-target functions decode through `sIdxX`; the
scaffold is CONSTRUCTED (`xstdSCR`) so the no-lose partition is a theorem; and the pins go
through the ROUTE TABLE `G` — per target and per priced coordinate, direct or circulant
edge, with the single route read `xstdCode_routeIdx` discharging both pin-layout slots.

  `sCoordX` / `sValX` — the singleton-range decoders with their reads.
  `pricedCoords` (reused) / `scafIdxX` / `xstdV` / `xstdSCR` — the constructions.
  `xstdV_card` — `|xstdV| = |D|`.
  `parity_xstd_drag` — **PROVED, THE EXTENDED GLUED DRAG**: under a cut factorization of
        the circulant-codebook parity family, `D.card ≤ j` — with the liveness class
        `hlive` now ROUTE-AWARE (the κ-assigned selector may be a direct singleton column
        or an edge column) and the companion-validity class `hcomp` (companions outside
        the priced set and the target coordinate — E4/E5's discharge target via the
        circulant independent-set choice).

## Honest scope

The remaining distance to the unconditional `(2+c)N`: supplying `(D, val, κ, G)` with
`|D| = Θ(T)` and the placements (`hVS`, `hTautProbe`, `hlive`, `hcomp`) at real balanced
cuts — the elementary kill-accounting over the circulant (E4–E5), no spectral input.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameParityXDrag

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval
open PallLean.Paper93.DeepMath.PathB.NFrameParityLayout
open PallLean.Paper93.DeepMath.PathB.NFrameParityCodebook
open PallLean.Paper93.DeepMath.PathB.NFrameParityStdDrag
open PallLean.Paper93.DeepMath.PathB.NFrameParityRouteSupply
open PallLean.Paper93.DeepMath.PathB.NFrameParityRouteAssembly
open PallLean.Paper93.DeepMath.PathB.NFrameParityXCode
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {v dd m N : ℕ}

/-! ### Decoders (singleton range) -/

/-- The coordinate decoder (total; junk-safe via `% v`). -/
def sCoordX (hv : 0 < v) (i : Fin (xstdL v dd)) : Fin v :=
  ⟨(i.val - 1) / 2 % v, Nat.mod_lt _ hv⟩

/-- The value decoder. -/
def sValX {v dd : ℕ} (i : Fin (xstdL v dd)) : ZMod 2 :=
  (((i.val - 1) % 2 : ℕ) : ZMod 2)

theorem sCoordX_sIdxX (hv : 0 < v) (j : Fin v) (b : ZMod 2) :
    sCoordX (dd := dd) hv (sIdxX v dd j b) = j := by
  have hb : b.val < 2 := ZMod.val_lt b
  have hj := j.isLt
  apply Fin.ext
  show (1 + 2 * j.val + b.val - 1) / 2 % v = j.val
  have h1 : (1 + 2 * j.val + b.val - 1) / 2 = j.val := by omega
  rw [h1, Nat.mod_eq_of_lt hj]

theorem sValX_sIdxX (v dd : ℕ) (j : Fin v) (b : ZMod 2) :
    sValX (sIdxX v dd j b) = b := by
  have hb : b.val < 2 := ZMod.val_lt b
  show (((1 + 2 * j.val + b.val - 1) % 2 : ℕ) : ZMod 2) = b
  have h2 : (1 + 2 * j.val + b.val - 1) % 2 = b.val := by omega
  rw [h2]
  have hcast : ∀ x : ZMod 2, ((x.val : ℕ) : ZMod 2) = x := by decide
  exact hcast b

/-! ### The constructions (`pricedCoords` reused from the standard drag) -/

/-- The scaffold indices of a block: value-1 singletons on the unpriced coordinates. -/
def scafIdxX (v dd : ℕ) (D : Finset (Fin m × Fin v)) (c : Fin m) :
    Finset (Fin (xstdL v dd)) :=
  ((Finset.univ : Finset (Fin v)) \ pricedCoords D c).image (fun j' => sIdxX v dd j' 1)

/-- The priced position set. -/
def xstdV (v dd : ℕ) (D : Finset (Fin m × Fin v)) (val : Fin m → Fin v → ZMod 2) :
    Finset (Fin m × Fin (xstdL v dd)) :=
  D.image (fun d => (d.1, sIdxX v dd d.2 (val d.1 d.2)))

/-- The row-side scaffold positions: the no-lose, constructed. -/
def xstdSCR (hfit : m * xstdL v dd ≤ N) (S : Finset (Fin N))
    (D : Finset (Fin m × Fin v)) : Finset (Fin m × Fin (xstdL v dd)) :=
  (D.image Prod.fst).biUnion (fun c =>
    ((scafIdxX v dd D c).filter (fun i => xbit hfit c i ∉ Sᶜ)).image (fun i => (c, i)))

theorem xstdV_mem (D : Finset (Fin m × Fin v)) (val : Fin m → Fin v → ZMod 2)
    {q : Fin m × Fin (xstdL v dd)} :
    q ∈ xstdV v dd D val ↔ ∃ d ∈ D, q = (d.1, sIdxX v dd d.2 (val d.1 d.2)) := by
  unfold xstdV
  rw [Finset.mem_image]
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d, hd, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d, hd, rfl⟩

/-- **The priced mass (proved)**: `|xstdV| = |D|`. -/
theorem xstdV_card (D : Finset (Fin m × Fin v)) (val : Fin m → Fin v → ZMod 2) :
    (xstdV v dd D val).card = D.card := by
  unfold xstdV
  apply Finset.card_image_of_injOn
  intro d _ d' _ h
  injection h with h1 h2
  exact Prod.ext h1 (sIdxX_inj v dd h2).1

theorem xstdSCR_slice (hfit : m * xstdL v dd ≤ N) (S : Finset (Fin N))
    (D : Finset (Fin m × Fin v)) {c : Fin m} (hc : c ∈ D.image Prod.fst) :
    ((xstdSCR hfit S D).filter (fun r => r.1 = c)).image Prod.snd
      = (scafIdxX v dd D c).filter (fun i => xbit hfit c i ∉ Sᶜ) := by
  ext i
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨r, ⟨hrSCR, hrc⟩, rfl⟩
    unfold xstdSCR at hrSCR
    obtain ⟨c', -, hr⟩ := Finset.mem_biUnion.mp hrSCR
    obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hr
    rw [Finset.mem_filter] at hi'
    have hcc : c' = c := hrc
    rw [← hcc]
    exact ⟨hi'.1, hi'.2⟩
  · rintro ⟨hscaf, hside⟩
    refine ⟨(c, i), ⟨?_, rfl⟩, rfl⟩
    unfold xstdSCR
    apply Finset.mem_biUnion.mpr
    refine ⟨c, hc, ?_⟩
    apply Finset.mem_image_of_mem
    rw [Finset.mem_filter]
    exact ⟨hscaf, hside⟩

set_option maxHeartbeats 3200000 in
/-- **THE EXTENDED GLUED DRAG (proved)**: under a cut factorization of the
circulant-codebook parity family, `D.card ≤ j` — pins through the route table `G`,
liveness route-aware, companions constrained by `hcomp`. -/
theorem parity_xstd_drag (hv : 0 < v) (hddv : dd ≤ v) (hfit : m * xstdL v dd ≤ N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (parityFamilyBits (xstdCode v dd hv) hfit) S j)
    (RS : Finset (Fin m))
    (D : Finset (Fin m × Fin v))
    (val : Fin m → Fin v → ZMod 2)
    (κ : Fin m × Fin (xstdL v dd) → Fin m → Fin v)
    (G : Fin m × Fin (xstdL v dd) → Fin v → PinRoute dd)
    (hDRS : ∀ d ∈ D, d.1 ∉ RS)
    (hκmem : ∀ q ∈ xstdV v dd D val, ∀ c ∈ RS,
      (q.1, κ q c) ∈ D ∧ κ q c ≠ sCoordX hv q.2)
    (hκcov : ∀ q ∈ xstdV v dd D val, ∀ j' : Fin v,
      (q.1, j') ∈ D → j' ≠ sCoordX hv q.2 → ∃ c ∈ RS, κ q c = j')
    (hcomp : ∀ q ∈ xstdV v dd D val,
      ∀ j' ∈ (pricedCoords D q.1).erase (sCoordX hv q.2), ∀ j'' : Fin v,
      routeCompanion v hv j' (G q j') = some j'' →
        j'' ∉ pricedCoords D q.1 ∧ j'' ≠ sCoordX hv q.2)
    (hVS : ∀ d ∈ D, xbit hfit d.1 (sIdxX v dd d.2 (val d.1 d.2)) ∉ Sᶜ)
    (hTautProbe : ∀ d ∈ D, xbit hfit d.1 (tautIdxX v dd) ∈ Sᶜ)
    (hlive : ∀ q ∈ xstdV v dd D val, ∀ c ∈ RS,
      xbit hfit c (routeIdx v dd hv (κ q c) (val q.1 (κ q c) + 1) (G q (κ q c)))
        ∈ Sᶜ) :
    D.card ≤ j := by
  classical
  rw [← xstdV_card (dd := dd) D val]
  apply parity_route_drag (xstdCode v dd hv) hfit (tautIdxX v dd) RS
    (xstdSCR hfit S D) (xstdV v dd D val) hcut
    (fun q c => routeIdx v dd hv (κ q c) (val q.1 (κ q c) + 1) (G q (κ q c)))
    (fun q => scafIdxX v dd D q.1)
    (fun q => sCoordX hv q.2)
    (fun q => sValX q.2)
    (fun q => (pricedCoords D q.1).erase (sCoordX hv q.2))
    (fun q => val q.1)
    (fun q => fun j' => routeLit v hv j' (val q.1 j' + 1) (G q j'))
  -- hrF: the route assignments
  · intro q hq j' hj'
    cases hG : G q j' with
    | direct =>
        left
        show routeLit v hv j' (val q.1 j' + 1) (G q j') = _
        rw [hG]
        rfl
    | edgeLo s =>
        right
        refine ⟨rot v hv j' (s.val + 1), ?_, ?_, ?_⟩
        · intro hmem
          exact (hcomp q hq j' hj' (rot v hv j' (s.val + 1))
            (by rw [hG]; rfl)).1 (Finset.mem_of_mem_erase hmem)
        · exact (hcomp q hq j' hj' (rot v hv j' (s.val + 1)) (by rw [hG]; rfl)).2
        · show routeLit v hv j' (val q.1 j' + 1) (G q j') = _
          rw [hG]
          rfl
    | edgeHi s =>
        right
        refine ⟨rot v hv j' (v - (s.val + 1)), ?_, ?_, ?_⟩
        · intro hmem
          exact (hcomp q hq j' hj' (rot v hv j' (v - (s.val + 1)))
            (by rw [hG]; rfl)).1 (Finset.mem_of_mem_erase hmem)
        · exact (hcomp q hq j' hj' (rot v hv j' (v - (s.val + 1)))
            (by rw [hG]; rfl)).2
        · show routeLit v hv j' (val q.1 j' + 1) (G q j') = _
          rw [hG]
          rfl
  -- hVt
  · intro q hq
    obtain ⟨d, hd, rfl⟩ := (xstdV_mem D val).mp hq
    exact sIdxX_ne_taut v dd d.2 (val d.1 d.2)
  -- hVSCR
  · intro q hq hqSCR
    obtain ⟨d, hd, rfl⟩ := (xstdV_mem D val).mp hq
    unfold xstdSCR at hqSCR
    obtain ⟨c', -, hr⟩ := Finset.mem_biUnion.mp hqSCR
    obtain ⟨i', hi', heq⟩ := Finset.mem_image.mp hr
    injection heq with hfst hsnd
    rw [Finset.mem_filter] at hi'
    unfold scafIdxX at hi'
    obtain ⟨j', hj', hij⟩ := Finset.mem_image.mp hi'.1
    rw [Finset.mem_sdiff] at hj'
    apply hj'.2
    unfold pricedCoords
    have hjj : j' = d.2 := by
      have h0 : sIdxX v dd j' 1 = sIdxX v dd d.2 (val d.1 d.2) := hij.trans hsnd
      exact (sIdxX_inj v dd h0).1
    rw [Finset.mem_image]
    refine ⟨d, ?_, hjj.symm⟩
    rw [Finset.mem_filter]
    exact ⟨hd, hfst.symm⟩
  -- hVRS
  · intro q hq
    obtain ⟨d, hd, rfl⟩ := (xstdV_mem D val).mp hq
    exact hDRS d hd
  -- hSCRRS
  · intro r hr
    unfold xstdSCR at hr
    obtain ⟨c', hc', hrm⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨i', -, rfl⟩ := Finset.mem_image.mp hrm
    obtain ⟨d, hd, hdc⟩ := Finset.mem_image.mp hc'
    show c' ∉ RS
    rw [← hdc]
    exact hDRS d hd
  -- hVS
  · intro q hq
    obtain ⟨d, hd, rfl⟩ := (xstdV_mem D val).mp hq
    exact hVS d hd
  -- hSCRS
  · intro r hr
    unfold xstdSCR at hr
    obtain ⟨c', -, hrm⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨i', hi', heq⟩ := Finset.mem_image.mp hrm
    rw [Finset.mem_filter] at hi'
    have hfst : r.1 = c' := congrArg Prod.fst heq.symm
    have hsnd : r.2 = i' := congrArg Prod.snd heq.symm
    rw [hfst, hsnd]
    exact hi'.2
  -- hTautProbe
  · intro q hq
    obtain ⟨d, hd, rfl⟩ := (xstdV_mem D val).mp hq
    exact hTautProbe d hd
  -- hcodeTaut
  · exact xstdCode_taut v dd hv
  -- hcodeStar
  · intro q hq
    obtain ⟨d, hd, rfl⟩ := (xstdV_mem D val).mp hq
    show xstdCode v dd hv (sIdxX v dd d.2 (val d.1 d.2)) = _
    rw [xstdCode_sIdxX, sCoordX_sIdxX, sValX_sIdxX]
  -- hKstar
  · intro q hq
    exact Finset.notMem_erase _ _
  -- hcodeV
  · intro q hq i hi hne
    obtain ⟨d, hd, rfl⟩ := (xstdV_mem D val).mp hq
    have hiV : ((d.1, i) : Fin m × Fin (xstdL v dd)) ∈ xstdV v dd D val := hi
    obtain ⟨d', hd', heq⟩ := (xstdV_mem D val).mp hiV
    injection heq with hfst hsnd
    refine ⟨d'.2, ?_, ?_⟩
    · rw [Finset.mem_erase]
      constructor
      · rw [sCoordX_sIdxX]
        intro hcon
        apply hne
        rw [hsnd, hcon, ← hfst]
      · unfold pricedCoords
        rw [Finset.mem_image]
        refine ⟨d', ?_, rfl⟩
        rw [Finset.mem_filter]
        exact ⟨hd', hfst.symm⟩
    · rw [hsnd, xstdCode_sIdxX, ← hfst]
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
    · exact xstdCode_routeIdx v dd hv hddv (κ q c) (val q.1 (κ q c) + 1)
        (G q (κ q c))
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
    rw [hκ]
    exact xstdCode_routeIdx v dd hv hddv j' (val q.1 j' + 1) (G q j')
  -- hscaffold
  · intro q hq
    obtain ⟨d, hd, rfl⟩ := (xstdV_mem D val).mp hq
    have hcblocks : d.1 ∈ D.image Prod.fst := Finset.mem_image_of_mem _ hd
    rw [xstdSCR_slice hfit S D hcblocks]
    have hpart : (scafIdxX v dd D d.1).filter
        (fun i => xbit hfit d.1 i ∈ Sᶜ)
        ∪ (scafIdxX v dd D d.1).filter (fun i => xbit hfit d.1 i ∉ Sᶜ)
        = scafIdxX v dd D d.1 :=
      Finset.filter_union_filter_neg_eq _ _
    rw [hpart]
    have hins : insert (sCoordX hv (sIdxX v dd d.2 (val d.1 d.2)))
        ((pricedCoords D d.1).erase (sCoordX hv (sIdxX v dd d.2 (val d.1 d.2))))
        = pricedCoords D d.1 := by
      apply Finset.insert_erase
      rw [sCoordX_sIdxX]
      unfold pricedCoords
      rw [Finset.mem_image]
      refine ⟨d, ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨hd, rfl⟩
    rw [hins]
    unfold scafIdxX
    rw [Finset.image_image]
    apply Finset.image_congr
    intro j' _
    exact xstdCode_sIdxX v dd hv j' 1
  -- hlive
  · intro q hq c hc
    exact hlive q hq c hc

end PallLean.Paper93.DeepMath.PathB.NFrameParityXDrag

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityXDrag.xstdV_card
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityXDrag.parity_xstd_drag
