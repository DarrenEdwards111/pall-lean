import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMultiBlockPrivateDrag

/-!
# N-Frame: the private window — cardinality-only pricing, no cleanliness

Rung 15 of the multi-block arc (… → private kit → private drag → **private window**).  The
rung-5 window discharged the drag's pin plumbing from cardinality room; its successors carried
the slot-1 cleanliness conditions that rung 12's stacked pairs attacked.  On the private drag
there is nothing left to attack: this file rebuilds the window chain with ROOM HYPOTHESES ONLY.

  `sat3_private_window` — **PROVED, the window**: for ANY data blocks `C` and patterns `V c`
        with slot-0 bits in `S`, `Σ_{c ∈ C} |V c| ≤ j` from three cardinality conditions:
        `m − |C| ≤ v` (pool injects), `|⋃V| + |C| ≤ v` (position space for the privates), and
        `|⋃V| + |C| + Q ≤ m − |C|` (pool room for pattern pins AND private pins).
        The privates are CONSTRUCTED here (a bijection from `C` onto fresh positions outside
        `⋃V`), and one strict injection routes off-sign pins onto patterns-plus-privates.
  `sat3_private_window_inside_mass` — the census form: the FULL slot-0 inside-columns of any
        block set sum to `≤ j` — no slot-1 condition.
  `sat3_private_clean_census` — **PROVED, the `m·j → j` core, room-only**: for ANY `C` with
        `j`-scale room (`j + 1 + |C| ≤ v` and `j + 1 + |C| + Q ≤ m − |C|`),
        `Σ_{c ∈ C} In₀(c) ≤ j`.  The rung-6 version demanded slot-1-clean blocks; the private
        version prices EVERY block set — the stacked-pair shelter is gone from the census.

## Honest scope

Room bills grew by the `|C|` private pins; everything else shrank.  The rebuilt budget
(two-cover without dirty terms), the band flight, and the arithmetic toward
`coneExcess = Ω(T)` / a `(2+c)·N` cbudget bound in the restricted wire model are the next
rung, not claims of this file.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The window -/

set_option maxHeartbeats 3200000 in
/-- **THE PRIVATE WINDOW (proved)**: `Σ_{c ∈ C} |V c| ≤ j` from cardinality room alone — no
slot-1 condition.  Privates and pins are constructed inside. -/
theorem sat3_private_window (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (C : Finset (Fin (sat3M N)))
    (V : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (hdata : ∀ c ∈ C, ∀ w ∈ V c,
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)
    (hkv : sat3M N - C.card ≤ sat3V N)
    (hspace : (C.biUnion V).card + C.card ≤ sat3V N)
    (hroom : (C.biUnion V).card + C.card
      + ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).filter (fun b =>
          sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
      ≤ sat3M N - C.card) :
    ∑ c ∈ C, (V c).card ≤ j := by
  classical
  have hpool : (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card = sat3M N - C.card :=
    sat3_pin_pool_card N C
  -- fresh positions for the privates
  have hcompl : (((Finset.univ : Finset (Fin (sat3V N))) \ C.biUnion V)).card
      = sat3V N - (C.biUnion V).card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  obtain ⟨U', hU'sub, hU'card⟩ := Finset.exists_subset_card_eq
    (s := ((Finset.univ : Finset (Fin (sat3V N))) \ C.biUnion V))
    (n := C.card) (by omega)
  set β : ↥C ≃ ↥U' :=
    C.equivFin.trans ((finCongr hU'card.symm).trans U'.equivFin.symm) with hβ
  set u : Fin (sat3M N) → Fin (sat3V N) :=
    fun c => if hc : c ∈ C then (β ⟨c, hc⟩).val else ⟨0, hv⟩ with hu
  have humem : ∀ c ∈ C, u c ∈ U' := by
    intro c hc
    show (if hc' : c ∈ C then (β ⟨c, hc'⟩).val else ⟨0, hv⟩) ∈ U'
    rw [dif_pos hc]
    exact (β ⟨c, hc⟩).2
  have huinj : ∀ c ∈ C, ∀ c' ∈ C, u c = u c' → c = c' := by
    intro c hc c' hc' h
    have h1 : u c = (β ⟨c, hc⟩).val := by
      show (if hc' : c ∈ C then (β ⟨c, hc'⟩).val else ⟨0, hv⟩) = (β ⟨c, hc⟩).val
      rw [dif_pos hc]
    have h2 : u c' = (β ⟨c', hc'⟩).val := by
      show (if hc'' : c' ∈ C then (β ⟨c', hc''⟩).val else ⟨0, hv⟩) = (β ⟨c', hc'⟩).val
      rw [dif_pos hc']
    rw [h1, h2] at h
    exact congrArg Subtype.val (β.injective (Subtype.ext h))
  have hupatV : ∀ c ∈ C, ∀ c' ∈ C, u c ∉ V c' := by
    intro c hc c' hc' hmem
    have h2 := hU'sub (humem c hc)
    exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_biUnion.mpr ⟨c', hc', hmem⟩)
  -- the pin target: patterns plus privates
  set W₀ : Finset (Fin (sat3V N)) := (C.biUnion V) ∪ U' with hW₀
  have hdisj : Disjoint (C.biUnion V) U' := by
    apply Finset.disjoint_left.mpr
    intro a ha ha'
    exact (Finset.mem_sdiff.mp (hU'sub ha')).2 ha
  have hW₀card : W₀.card = (C.biUnion V).card + C.card := by
    rw [hW₀, Finset.card_union_of_disjoint hdisj, hU'card]
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
  have hoff : W₀.card
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
    (n := W₀.card) hoff
  have hkv' : (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card ≤ sat3V N := by
    omega
  obtain ⟨α, hαinj, hαmap, hαstrict⟩ := exists_injection_mapping_strict hkv'
    P' W₀ (by rw [hP'card])
  have himg : P'.image α = W₀ := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
      exact hαmap p hp
    · rw [Finset.card_image_of_injective _ hαinj, hP'card]
  exact sat3_private_selector_drag N hv hcut C (le_refl _) α hαinj V u hdata
    (fun c hc w hw => by
      have hwW : w ∈ W₀ :=
        Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨c, hc, hw⟩)
      have hwim : w ∈ P'.image α := by
        rw [himg]
        exact hwW
      obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hwim
      exact ⟨p, hp⟩)
    (fun c hc => by
      have huW : u c ∈ W₀ := Finset.mem_union_right _ (humem c hc)
      have huim : u c ∈ P'.image α := by
        rw [himg]
        exact huW
      obtain ⟨p, -, hp⟩ := Finset.mem_image.mp huim
      exact ⟨p, hp⟩)
    huinj hupatV
    (fun p hp => by
      obtain ⟨c, hc, hpins⟩ := hp
      have hpW : α p ∈ W₀ := by
        rcases Finset.mem_insert.mp hpins with h | h
        · rw [h]
          exact Finset.mem_union_right _ (humem c hc)
        · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨c, hc, h⟩)
      have hpP' : p ∈ P' := by
        by_contra hnp
        exact hαstrict p hnp hpW
      exact (Finset.mem_filter.mp (hP'sub hpP')).2)

/-! ### The census forms -/

set_option maxHeartbeats 800000 in
/-- **The inside-mass form (proved)**: the FULL slot-0 inside-columns of ANY block set sum to
`≤ j` under cardinality room — no slot-1 condition. -/
theorem sat3_private_window_inside_mass (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (C : Finset (Fin (sat3M N)))
    (hkv : sat3M N - C.card ≤ sat3V N)
    (hspace : (C.biUnion (fun c => (Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))).card
      + C.card ≤ sat3V N)
    (hroom : (C.biUnion (fun c => (Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))).card
      + C.card
      + ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).filter (fun b =>
          sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
      ≤ sat3M N - C.card) :
    ∑ c ∈ C, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card ≤ j := by
  classical
  exact sat3_private_window N hv hcut C
    (fun c => (Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))
    (fun c hc w hw => (Finset.mem_filter.mp hw).2)
    hkv hspace hroom

set_option maxHeartbeats 1600000 in
/-- **THE PRIVATE CLEAN CENSUS (proved, room-only)**: for ANY block set `C` with `j`-scale room,
the total slot-0 inside mass is at most `j`.  The rung-6 version demanded slot-1-clean blocks;
here NO cleanliness is needed — the stacked-pair shelter is gone from the census. -/
theorem sat3_private_clean_census (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (C : Finset (Fin (sat3M N)))
    (hkv : sat3M N - C.card ≤ sat3V N)
    (hspace : j + 1 + C.card ≤ sat3V N)
    (hroom : j + 1 + C.card
      + ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).filter (fun b =>
          sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
      ≤ sat3M N - C.card) :
    ∑ c ∈ C, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card ≤ j := by
  classical
  by_contra hcon
  push_neg at hcon
  have hDcard : (C.sigma (fun c => (Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))).card
      = ∑ c ∈ C, ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card :=
    Finset.card_sigma _ _
  have hex : j + 1 ≤ (C.sigma (fun c =>
      (Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))).card := by
    omega
  obtain ⟨E, hEsub, hEcard⟩ := Finset.exists_subset_card_eq hex
  have hslice : C.sigma (fun c => sat3TupleOf N (fun c' =>
      (Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c' ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)) E c) = E := by
    ext ⟨c, w⟩
    rw [Finset.mem_sigma]
    constructor
    · rintro ⟨hc, hw⟩
      exact (sat3TupleOf_mem N _ E c w (sat3TupleOf_subset N _ E c hw)).mp hw
    · intro hqE
      have hqD := hEsub hqE
      rw [Finset.mem_sigma] at hqD
      exact ⟨hqD.1, (sat3TupleOf_mem N _ E c w hqD.2).mpr hqE⟩
  have hsum : ∑ c ∈ C, (sat3TupleOf N (fun c' =>
      (Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c' ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)) E c).card
      = j + 1 := by
    rw [← Finset.card_sigma, hslice, hEcard]
  have hbu := Finset.card_biUnion_le (s := C) (t := sat3TupleOf N (fun c' =>
    (Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c' ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)) E)
  rw [hsum] at hbu
  have hwin := sat3_private_window N hv hcut C
    (sat3TupleOf N (fun c' => (Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c' ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)) E)
    (fun c hc w hw => (Finset.mem_filter.mp (sat3TupleOf_subset N _ E c hw)).2)
    hkv (by omega) (by omega)
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_private_window
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_private_window_inside_mass
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_private_clean_census
