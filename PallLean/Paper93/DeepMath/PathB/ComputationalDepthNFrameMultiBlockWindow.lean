import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMultiBlockDrag

/-!
# N-Frame: the rebuilt window — `m·j → j` in the balance census

Rung 5 of the multi-block arc (patch → context → eval → drag → **window**).  The single-block
census (`sat3_slot_dichotomy` / `sat3_empty_mass`) prices each block's inside-`S` selector mass
separately: every block ≤ `j`, so the nearly-empty mass bound carries an `m·j` term.  The
additive drag replaces the per-block budget with ONE shared budget: the total inside mass over a
whole set of data blocks is ≤ `j`.  This file rebuilds the window step in that form, with the
drag's pin/injection plumbing discharged from pure cardinality hypotheses:

  `sat3_multi_pin_sign_count` — the pin enumeration at full pool size is a bijection onto
        `univ \ C`, so pin-sign censuses equal block censuses.
  `sat3_multi_window` — **PROVED, the rebuilt window**: over any cut factorization, for data
        blocks `C` with patterns `V c` (slot-0 data in `S`, slot-1 kit positions off `S`), if the
        pin pool has room — `|⋃_c V c| + #{b ∉ C : slot-0 sign of b ∈ S} ≤ m − |C|` — and
        `m − |C| ≤ v`, then `Σ_{c ∈ C} |V c| ≤ j`.
  `sat3_multi_window_inside_mass` — **PROVED, the census form**: for slot-1-clean blocks the
        FULL slot-0 inside-columns sum to ≤ `j`:
        `Σ_{c ∈ C} #{w : slot-0 selector (c,w) ∈ S} ≤ j`.

Against `sat3_slot_dichotomy`'s nearly-empty branch (each block ≤ `j` inside, `Σ ≤ m·j`), the
window prices the whole set at ONE `j` — the `m·j → j` upgrade.  The adversary's remaining
moves are all priced in `S`-bits: poisoning a position costs a slot-1 bit inside `S` (shrinking
the clean set `C`), poisoning a pin costs a sign bit inside `S` (eating the room term) — the
balance census over those costs is the closing rung.

## Honest scope

The window prices data against an ABSTRACT cut factorization; composing with
`sat3_balanced_cut` (circuit ⇒ balanced cut at every band) and the poison census toward
`coneExcess = Ω(N)` / a `(2+c)·N` cbudget bound in the restricted wire model is the remaining
rung.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The pin census transfer -/

/-- **The pin census transfer (proved)**: at full pool size the pin enumeration is a bijection
onto `univ \ C`, so the count of pins whose slot-0 sign bit lies in `S` equals the count of
non-designated blocks whose sign bit lies in `S`. -/
theorem sat3_multi_pin_sign_count (N : ℕ) (C : Finset (Fin (sat3M N)))
    (S : Finset (Fin N)) :
    ((Finset.univ : Finset (Fin ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).card))).filter
      (fun p => sat3Bit N (sat3PinClauseM N C (le_refl _) p) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∈ S)).card
    = ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card := by
  classical
  apply Finset.card_bij (fun p _ => sat3PinClauseM N C (le_refl _) p)
  · intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      sat3PinClauseM_not_mem N C (le_refl _) p⟩, hp.2⟩
  · intro p1 hp1 p2 hp2 heq
    exact sat3PinClauseM_inj N C (le_refl _) heq
  · intro b hb
    rw [Finset.mem_filter] at hb
    have hpin : sat3PinClauseM N C (le_refl _)
        ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).equivFin ⟨b, hb.1⟩) = b := by
      show ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).equivFin.symm
        (Fin.castLE (le_refl _)
          ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).equivFin ⟨b, hb.1⟩))).val = b
      have hcast : Fin.castLE (le_refl _)
          ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).equivFin ⟨b, hb.1⟩)
          = (((Finset.univ : Finset (Fin (sat3M N))) \ C)).equivFin ⟨b, hb.1⟩ :=
        Fin.ext rfl
      rw [hcast, Equiv.symm_apply_apply]
    refine ⟨(((Finset.univ : Finset (Fin (sat3M N))) \ C)).equivFin ⟨b, hb.1⟩, ?_, hpin⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hpin]
    exact hb.2

/-! ### The rebuilt window -/

set_option maxHeartbeats 1600000 in
/-- **THE REBUILT WINDOW (proved)**: over any cut factorization, data blocks `C` with slot-0
patterns `V c` inside `S` and slot-1 kit positions off `S` have TOTAL inside mass at most `j` —
provided the pin pool has room: `|⋃_c V c| + #{b ∉ C : sign of b ∈ S} ≤ m − |C|` and
`m − |C| ≤ v`.  One shared budget `j` for the whole block set, not `j` per block. -/
theorem sat3_multi_window (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (C : Finset (Fin (sat3M N)))
    (V : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (hdata : ∀ c ∈ C, ∀ w ∈ V c,
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)
    (hkit1 : ∀ c ∈ C, ∀ c' ∈ C, ∀ w ∈ V c',
      sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)
    (hkv : sat3M N - C.card ≤ sat3V N)
    (hroom : (C.biUnion V).card
      + ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).filter (fun b =>
          sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
      ≤ sat3M N - C.card) :
    ∑ c ∈ C, (V c).card ≤ j := by
  classical
  have hpool : (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card = sat3M N - C.card :=
    sat3_pin_pool_card N C
  -- every pin index has its sign bit in `S` or out of `S`
  have hcover : (Finset.univ :
        Finset (Fin ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)))
      ⊆ ((Finset.univ :
          Finset (Fin ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).card))).filter
          (fun p => sat3Bit N (sat3PinClauseM N C (le_refl _) p) ⟨0, by omega⟩
            (sat3V N) (by omega) ∈ S))
        ∪ ((Finset.univ :
          Finset (Fin ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).card))).filter
          (fun p => sat3Bit N (sat3PinClauseM N C (le_refl _) p) ⟨0, by omega⟩
            (sat3V N) (by omega) ∉ S)) := by
    intro p _
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases hp : sat3Bit N (sat3PinClauseM N C (le_refl _) p) ⟨0, by omega⟩
        (sat3V N) (by omega) ∈ S
    · exact Or.inl ⟨Finset.mem_univ p, hp⟩
    · exact Or.inr ⟨Finset.mem_univ p, hp⟩
  have hcnt : (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card
      ≤ ((Finset.univ :
          Finset (Fin ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).card))).filter
          (fun p => sat3Bit N (sat3PinClauseM N C (le_refl _) p) ⟨0, by omega⟩
            (sat3V N) (by omega) ∈ S)).card
        + ((Finset.univ :
          Finset (Fin ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).card))).filter
          (fun p => sat3Bit N (sat3PinClauseM N C (le_refl _) p) ⟨0, by omega⟩
            (sat3V N) (by omega) ∉ S)).card := by
    calc (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card
        = (Finset.univ :
            Finset (Fin ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).card))).card := by
          rw [Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := Finset.card_le_card hcover
      _ ≤ _ := Finset.card_union_le _ _
  have hQ := sat3_multi_pin_sign_count N C S
  -- room: the off-sign pin pool covers the pattern union
  have hoff : (C.biUnion V).card
      ≤ ((Finset.univ :
          Finset (Fin ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).card))).filter
          (fun p => sat3Bit N (sat3PinClauseM N C (le_refl _) p) ⟨0, by omega⟩
            (sat3V N) (by omega) ∉ S)).card := by
    omega
  obtain ⟨P', hP'sub, hP'card⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ :
      Finset (Fin ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).card))).filter
      (fun p => sat3Bit N (sat3PinClauseM N C (le_refl _) p) ⟨0, by omega⟩
        (sat3V N) (by omega) ∉ S))
    (n := (C.biUnion V).card) hoff
  have hkv' : (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card ≤ sat3V N := by
    omega
  obtain ⟨α, hαinj, hαmap, hαstrict⟩ := exists_injection_mapping_strict hkv'
    P' (C.biUnion V) (by rw [hP'card])
  -- surjectivity of α from P' onto the pattern union
  have himg : P'.image α = C.biUnion V := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
      exact hαmap p hp
    · rw [Finset.card_image_of_injective _ hαinj, hP'card]
  exact sat3_multi_selector_data_drag N hv hcut C (le_refl _) α hαinj V hdata
    (fun c hc w hw => by
      have hwU : w ∈ C.biUnion V := Finset.mem_biUnion.mpr ⟨c, hc, hw⟩
      have hwim : w ∈ P'.image α := by
        rw [himg]
        exact hwU
      obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hwim
      exact ⟨p, hp⟩)
    (fun p hp => by
      obtain ⟨c, hc, hpc⟩ := hp
      have hpU : α p ∈ C.biUnion V := Finset.mem_biUnion.mpr ⟨c, hc, hpc⟩
      have hpP' : p ∈ P' := by
        by_contra hnp
        exact hαstrict p hnp hpU
      exact (Finset.mem_filter.mp (hP'sub hpP')).2)
    hkit1

/-! ### The census form -/

set_option maxHeartbeats 800000 in
/-- **THE INSIDE-MASS CENSUS (proved)**: for slot-1-clean data blocks with pin-pool room, the
FULL slot-0 inside-columns sum to at most `j` — the `m·j → j` upgrade over the per-block
dichotomy. -/
theorem sat3_multi_window_inside_mass (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (C : Finset (Fin (sat3M N)))
    (hclean1 : ∀ c ∈ C, ∀ w : Fin (sat3V N),
      sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)
    (hkv : sat3M N - C.card ≤ sat3V N)
    (hroom : (C.biUnion (fun c => (Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))).card
      + ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).filter (fun b =>
          sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
      ≤ sat3M N - C.card) :
    ∑ c ∈ C, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card ≤ j := by
  classical
  exact sat3_multi_window N hv hcut C
    (fun c => (Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))
    (fun c hc w hw => (Finset.mem_filter.mp hw).2)
    (fun c hc c' hc' w hw => hclean1 c hc w)
    hkv hroom

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_pin_sign_count
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_window
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_window_inside_mass
