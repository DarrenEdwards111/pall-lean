import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDynamicPACGauge

/-!
# N-Frame: the interfaced two-mass kill — the aligned branch cannot leak selectors

The mixed sign↔selector family (V1 source) and the pinned-selector family (V0 source) lifted to
interfaced cuts through `crossing_triples_kill_interfaced`, then assembled into the aligned-branch
pressure theorem.  This is Track A's two-mass assembly (`sat3_mass_of_core`) at **any** interface.

  `sat3_s2sel_mem_union` — **PROVED**: every slot-2 selector bit is essential, hence read.
  `sat3_opposite_mass_kill_interfaced` — **PROVED, the kill**: for any block `cIdx` and pin `j₀`, a
        sign mass and a selector mass on opposite exclusive sides die: orientation A (sign `∉ B`,
        selector `∉ A`, pin-sign `∉ B`) via mixed odd + mixed V1-selDown + pinned V0-pinDown;
        orientation B (selector `∉ B`, sign `∉ A`, pin-sign `∉ A`) via pinned odd + mixed V1-signDown
        + pinned V0-selDown.  Any interface.
  `sat3_aligned_selector_capture_left/right` — **PROVED, the capture**: in the sign-aligned branch,
        every slot-2 selector whose block sign and pin sign are non-interned is captured on the
        **same** side as the signs.
  `sat3_united_mass_or_interface` — **PROVED, the assembly**: for any interfaced factorization of
        `sat3Family`: the sign layer AND the (sign-clean) slot-2 selector layer are one united mass
        in `A \ B`, or one united mass in `B \ A`, or `m ≤ |A ∩ B| + 4`.

**The aligned branch cannot leak selectors to the other side except through interned sign bits** —
every escaping selector `(cIdx, j₀)` costs an interned `signBit cIdx` or an interned pin sign.  The
united-mass structure of Track A's thinned residual now holds at any interface.

## Honest scope

Named, not claimed: (1) the quantitative selector-escape counting — each escape charges an interned
sign via the `(cIdx, j₀)` incidence structure, which should convert many escapes into another `Ω(m)`
interface bound; (2) slot-0/1 selectors and the remaining slot-probe families; (3) the assembly into
`GlobalPACInterfaceBound`; (4) the wire-frontier → coordinate-interface extraction.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **Every slot-2 selector bit is read (proved)**: the ZBase flip makes it essential. -/
theorem sat3_s2sel_mem_union (N : ℕ) (hv : 1 ≤ sat3V N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (c : Fin (sat3M N)) (jv : Fin (sat3V N)) :
    sat3S2Sel N c jv ∈ A ∪ B := by
  by_contra hout
  rw [Finset.mem_union] at hout
  push_neg at hout
  obtain ⟨hA, hB⟩ := hout
  have h1 : sat3Family N (sat3ZBase N c) = false := sat3ZBase_unsat N c
  have h2 : sat3Family N (Function.update (sat3ZBase N c) (sat3S2Sel N c jv) true)
      = true := sat3_zbase_flip_sat_t N hv c ⟨2, by omega⟩ jv
  rw [hf] at h1 h2
  have hgu : g (Function.update (sat3ZBase N c) (sat3S2Sel N c jv) true)
      = g (sat3ZBase N c) := by
    apply hg
    intro i hi
    exact Function.update_of_ne (fun hc => hA (by rw [← hc]; exact hi)) _ _
  have hhu : h (Function.update (sat3ZBase N c) (sat3S2Sel N c jv) true)
      = h (sat3ZBase N c) := by
    apply hh
    intro i hi
    exact Function.update_of_ne (fun hc => hB (by rw [← hc]; exact hi)) _ _
  rw [hgu, hhu, h1] at h2
  exact Bool.noConfusion h2

/-- **THE OPPOSITE-MASS KILL, ANY INTERFACE (proved)**: a sign mass and a selector mass on opposite
exclusive sides die — orientation A via mixed odd + mixed V1 + pinned V0-pinDown, orientation B via
pinned odd + mixed V1-signDown + pinned V0-selDown. -/
theorem sat3_opposite_mass_kill_interfaced (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2)) (hjv : j₀.val < sat3V N)
    (hsep :
      (sat3SignBit N cIdx ∉ B ∧ sat3S2Sel N cIdx ⟨j₀.val, hjv⟩ ∉ A
        ∧ sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
            (by omega) ∉ B)
      ∨ (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩ ∉ B ∧ sat3SignBit N cIdx ∉ A
        ∧ sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
            (by omega) ∉ A)) : False := by
  classical
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  have hστ : sat3SignBit N cIdx ≠ sat3S2Sel N cIdx ⟨j₀.val, hjv⟩ :=
    sat3_sign_ne_sel_bit N cIdx ⟨0, by omega⟩ ⟨2, by omega⟩ ⟨j₀.val, hjv⟩
  have hπτ : sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
      (by omega) ≠ sat3S2Sel N cIdx ⟨j₀.val, hjv⟩ := by
    show sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega)
      ≠ sat3Bit N cIdx ⟨2, by omega⟩ j₀.val (by omega)
    exact sat3Bit_ne_of_clause N _ _ _ _
      (fun h' => sat3PinClause_ne N cIdx hk j₀ h')
  rcases hsep with ⟨hσB, hτA, hπB⟩ | ⟨hτB, hσA, hπA⟩
  · -- signs left of the cut, selector right
    obtain ⟨w1a, w1b, w1c⟩ :=
      sat3_sign_selector_V1_selDown N hv hk hkv hm3 cIdx j₀ hjv
    obtain ⟨z0a, z0b, z0c⟩ :=
      sat3_selector_pinsign_V0_pinDown N hv hk hkv hm3 cIdx j₀ hjv
    exact crossing_triples_kill_interfaced (sat3Family N) A B op g h hg hh hf
      (sat3SignBit N cIdx) (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩)
      (sat3SignBit N cIdx) (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩)
      (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
      (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩)
      hσB hτA hστ hσB hτA hστ hπB hτA hπτ
      (mixedPt N cIdx hk j₀ hjv true false)
      (mixedPt N cIdx hk j₀ hjv true true)
      (pinnedPt N cIdx hk j₀ hjv (fun _ => true) false)
      (sat3_sign_selector_odd N hv hk hkv hm3 cIdx j₀ hjv)
      w1a w1b w1c z0a z0b z0c
  · -- selector left of the cut, signs right
    obtain ⟨w1a, w1b, w1c⟩ :=
      sat3_sign_selector_V1_signDown N hv hk hkv hm3 cIdx j₀ hjv
    obtain ⟨z0a, z0b, z0c⟩ :=
      sat3_selector_pinsign_V0_selDown N hv hk hkv hm3 cIdx j₀ hjv
    exact crossing_triples_kill_interfaced (sat3Family N) A B op g h hg hh hf
      (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩)
      (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
      (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩) (sat3SignBit N cIdx)
      (sat3S2Sel N cIdx ⟨j₀.val, hjv⟩)
      (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
      hτB hπA hπτ.symm hτB hσA hστ.symm hτB hπA hπτ.symm
      (pinnedPt N cIdx hk j₀ hjv (fun _ => false) true)
      (mixedPt N cIdx hk j₀ hjv false false)
      (pinnedPt N cIdx hk j₀ hjv (fun _ => false) true)
      (sat3_selector_pinsign_odd N hv hk hkv hm3 cIdx j₀ hjv)
      w1a w1b w1c z0a z0b z0c

/-- **THE CAPTURE, LEFT (proved)**: signs aligned in `A \ B` ⇒ every sign-clean slot-2 selector is
captured in `A \ B` too. -/
theorem sat3_aligned_selector_capture_left (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (haligned : ∀ c : Fin (sat3M N), sat3SignBit N c ∉ A ∩ B →
      sat3SignBit N c ∈ A \ B)
    (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2)) (hjv : j₀.val < sat3V N)
    (hσ : sat3SignBit N cIdx ∉ A ∩ B)
    (hπ : sat3SignBit N (sat3PinClause N cIdx hk j₀) ∉ A ∩ B)
    (hτ : sat3S2Sel N cIdx ⟨j₀.val, hjv⟩ ∉ A ∩ B) :
    sat3S2Sel N cIdx ⟨j₀.val, hjv⟩ ∈ A \ B := by
  have hτu := sat3_s2sel_mem_union N hv op g h A B hg hh hf cIdx ⟨j₀.val, hjv⟩
  have hσab := haligned cIdx hσ
  have hπab := haligned _ hπ
  rw [Finset.mem_union] at hτu
  rw [Finset.mem_inter] at hτ
  push_neg at hτ
  rw [Finset.mem_sdiff] at hσab hπab
  rw [Finset.mem_sdiff]
  by_cases hτA : sat3S2Sel N cIdx ⟨j₀.val, hjv⟩ ∈ A
  · exact ⟨hτA, hτ hτA⟩
  · exfalso
    have hπB : sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∉ B := hπab.2
    exact sat3_opposite_mass_kill_interfaced N hv hm3 hk op g h A B hg hh hf
      cIdx j₀ hjv (Or.inl ⟨hσab.2, hτA, hπB⟩)

/-- **THE CAPTURE, RIGHT (proved)**: signs aligned in `B \ A` ⇒ every sign-clean slot-2 selector is
captured in `B \ A` too. -/
theorem sat3_aligned_selector_capture_right (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (haligned : ∀ c : Fin (sat3M N), sat3SignBit N c ∉ A ∩ B →
      sat3SignBit N c ∈ B \ A)
    (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2)) (hjv : j₀.val < sat3V N)
    (hσ : sat3SignBit N cIdx ∉ A ∩ B)
    (hπ : sat3SignBit N (sat3PinClause N cIdx hk j₀) ∉ A ∩ B)
    (hτ : sat3S2Sel N cIdx ⟨j₀.val, hjv⟩ ∉ A ∩ B) :
    sat3S2Sel N cIdx ⟨j₀.val, hjv⟩ ∈ B \ A := by
  have hτu := sat3_s2sel_mem_union N hv op g h A B hg hh hf cIdx ⟨j₀.val, hjv⟩
  have hσab := haligned cIdx hσ
  have hπab := haligned _ hπ
  rw [Finset.mem_union] at hτu
  rw [Finset.mem_inter] at hτ
  push_neg at hτ
  rw [Finset.mem_sdiff] at hσab hπab
  rw [Finset.mem_sdiff]
  by_cases hτB : sat3S2Sel N cIdx ⟨j₀.val, hjv⟩ ∈ B
  · exact ⟨hτB, fun hA => hτ hA hτB⟩
  · exfalso
    have hπA : sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∉ A := hπab.2
    exact sat3_opposite_mass_kill_interfaced N hv hm3 hk op g h A B hg hh hf
      cIdx j₀ hjv (Or.inr ⟨hτB, hσab.2, hπA⟩)

/-- **THE UNITED-MASS ASSEMBLY (proved)**: for any interfaced factorization of `sat3Family`, the sign
layer and the sign-clean slot-2 selector layer form one united mass in `A \ B`, or one in `B \ A`, or
`m ≤ |A ∩ B| + 4`.  The aligned branch cannot leak selectors except through interned sign bits. -/
theorem sat3_united_mass_or_interface (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x)) :
    ((∀ c : Fin (sat3M N), sat3SignBit N c ∉ A ∩ B → sat3SignBit N c ∈ A \ B) ∧
      ∀ (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2)) (hjv : j₀.val < sat3V N),
        sat3SignBit N cIdx ∉ A ∩ B →
        sat3SignBit N (sat3PinClause N cIdx hk j₀) ∉ A ∩ B →
        sat3S2Sel N cIdx ⟨j₀.val, hjv⟩ ∉ A ∩ B →
        sat3S2Sel N cIdx ⟨j₀.val, hjv⟩ ∈ A \ B) ∨
    ((∀ c : Fin (sat3M N), sat3SignBit N c ∉ A ∩ B → sat3SignBit N c ∈ B \ A) ∧
      ∀ (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2)) (hjv : j₀.val < sat3V N),
        sat3SignBit N cIdx ∉ A ∩ B →
        sat3SignBit N (sat3PinClause N cIdx hk j₀) ∉ A ∩ B →
        sat3S2Sel N cIdx ⟨j₀.val, hjv⟩ ∉ A ∩ B →
        sat3S2Sel N cIdx ⟨j₀.val, hjv⟩ ∈ B \ A) ∨
    sat3M N ≤ (A ∩ B).card + 4 := by
  rcases sat3_sign_alignment_or_interface N hv hm3 hk op g h A B hg hh hf
    with hL | hR | hC
  · exact Or.inl ⟨hL, fun cIdx j₀ hjv hσ hπ hτ =>
      sat3_aligned_selector_capture_left N hv hm3 hk op g h A B hg hh hf
        hL cIdx j₀ hjv hσ hπ hτ⟩
  · exact Or.inr (Or.inl ⟨hR, fun cIdx j₀ hjv hσ hπ hτ =>
      sat3_aligned_selector_capture_right N hv hm3 hk op g h A B hg hh hf
        hR cIdx j₀ hjv hσ hπ hτ⟩)
  · exact Or.inr (Or.inr hC)

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_opposite_mass_kill_interfaced
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_united_mass_or_interface
