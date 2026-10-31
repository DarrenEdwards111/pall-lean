import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameGeneralSlotPatterns

/-!
# N-Frame: the selector sweep — every selector of every slot joins the mass

The general-slot patterns assembled.  A slot-`t` selector separated from the united mass supplies V1
through its same-block pair with a slot-2 selector (in the mass), V0 through a cross-block pair, and the
odd square from the same-block pair — `triples_kill_split_mixed` fires in both orientations.

  `sat3_core_of_all_selectors` — **PROVED, the reduction**: killing all-selectors-united cuts suffices
        for the core-mass residual.  Slot-2 separations contradict the standing alignment; slot-0/1
        separations die by the engine.
  `Sat3AllSelectorsMassNoSplit` — the **thinned residual** (NOT discharged): pins aligned and **every
        selector of every slot aligned with every sign** — the entire selector layer and the sign layer
        are one mass.
  `sat3_cbudget_2mD_of_all_selectors` — the conditional record through the full chain.

## Honest scope

The only coordinates a surviving cut may still move are the slot-1 and slot-2 **sign fields** — `2m` bits
out of `N`.  The last production rung is the slot-`t` probe family (a designated block whose satisfaction
routes through a slot-1/2 literal with its sign free), after which the final reduction discharges the
residual and `2·m·D ≤ cbudget (sat3Family N)` fires unconditionally.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- The **thinned residual** (NOT discharged): the whole selector layer is aligned with the sign layer. -/
def Sat3AllSelectorsMassNoSplit (N : ℕ) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) : Prop :=
  ∀ (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (S : Finset (Fin N)),
    (∀ x y : Fin N → Bool, (∀ i, i ∈ S → x i = y i) → g x = g y) →
    (∀ x y : Fin N → Bool, (∀ i, i ∉ S → x i = y i) → h x = h y) →
    (∀ x, sat3Family N x = op (g x) (h x)) →
    (∃ s₀ : Fin N, s₀ ∈ S) → (∃ t₀ : Fin N, t₀ ∉ S) →
    (∀ (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2)),
      (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∈ S ↔ sat3SignBit N cIdx ∈ S)) →
    (∀ (c : Fin (sat3M N)) (t : Fin 3) (j : Fin (sat3V N)),
      (sat3Bit N c t j.val (by have := j.isLt; omega) ∈ S
        ↔ sat3SignBit N c ∈ S)) → False

/-- **THE SELECTOR SWEEP (proved)**: killing all-selectors-united cuts suffices. -/
theorem sat3_core_of_all_selectors (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (hW : Sat3AllSelectorsMassNoSplit N hm3 hk) :
    Sat3CoreMassNoSplit N hm3 hk := by
  intro op g h S hg hh hf hs ht hal hmono hall2
  classical
  by_cases hallt : ∀ (c : Fin (sat3M N)) (t : Fin 3) (j : Fin (sat3V N)),
      (sat3Bit N c t j.val (by have := j.isLt; omega) ∈ S ↔ sat3SignBit N c ∈ S)
  · exact hW op g h S hg hh hf hs ht hal hallt
  · push_neg at hallt
    obtain ⟨c, t, j, hciff⟩ := hallt
    -- the sign walk (pins-alignment is connected)
    have hm0 : (0 : ℕ) < sat3M N := by omega
    have hstep : ∀ x : Fin (sat3M N),
        (sat3SignBit N x ∈ S ↔ sat3SignBit N ⟨0, hm0⟩ ∈ S) := by
      intro x
      by_cases hx0 : x.val = 0
      · rw [show x = ⟨0, hm0⟩ from Fin.ext hx0]
      · have hpc : sat3PinClause N x hk ⟨0, by omega⟩ = (⟨0, hm0⟩ : Fin (sat3M N)) := by
          apply Fin.ext
          rw [sat3PinClause_val]
          rw [if_pos (show ((⟨0, by omega⟩ : Fin (sat3M N - 2))).val < x.val from by
            show (0 : ℕ) < x.val
            omega)]
        have h1 := hal x ⟨0, by omega⟩
        rw [hpc] at h1
        exact (h1 : sat3SignBit N ⟨0, hm0⟩ ∈ S ↔ sat3SignBit N x ∈ S).symm
    have hwalk : ∀ x y : Fin (sat3M N),
        (sat3SignBit N x ∈ S ↔ sat3SignBit N y ∈ S) :=
      fun x y => (hstep x).trans (hstep y).symm
    -- slot-2 separations contradict the standing alignment
    by_cases ht2 : t.val = 2
    · have hteq : t = ⟨2, by omega⟩ := Fin.ext ht2
      rw [hteq] at hciff
      have hbridge : (sat3Bit N c ⟨2, by omega⟩ j.val (by have := j.isLt; omega) ∈ S)
          ↔ sat3SignBit N c ∈ S := hall2 c j
      rcases hciff with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2 (hbridge.mp h1)
      · exact h1 (hbridge.mpr h2)
    · -- the kill: same-block V1 + odd, cross-block V0
      have hneB : sat3Bit N c t j.val (by have := j.isLt; omega)
          ≠ sat3Bit N c ⟨2, by omega⟩ j.val (by have := j.isLt; omega) := by
        intro hcon
        have hval := congrArg Fin.val hcon
        rcases t with ⟨tv, htv⟩
        interval_cases tv
        · exact absurd (show c.val * sat3D N + 0 * (sat3V N + 1) + j.val
              = c.val * sat3D N + 2 * (sat3V N + 1) + j.val from hval) (by omega)
        · exact absurd (show c.val * sat3D N + 1 * (sat3V N + 1) + j.val
              = c.val * sat3D N + 2 * (sat3V N + 1) + j.val from hval) (by omega)
        · exact ht2 rfl
      have hc' : ∃ c' : Fin (sat3M N), c'.val ≠ c.val := by
        by_cases h0 : c.val = 0
        · exact ⟨⟨1, by omega⟩, by show (1 : ℕ) ≠ c.val; omega⟩
        · exact ⟨⟨0, by omega⟩, by show (0 : ℕ) ≠ c.val; omega⟩
      obtain ⟨c', hcc⟩ := hc'
      have hB2c : (sat3Bit N c ⟨2, by omega⟩ j.val (by have := j.isLt; omega) ∈ S)
          ↔ sat3SignBit N c ∈ S := hall2 c j
      have hB2c' : (sat3Bit N c' ⟨2, by omega⟩ (⟨0, hv⟩ : Fin (sat3V N)).val
          (by omega) ∈ S) ↔ sat3SignBit N c ∈ S :=
        (hall2 c' ⟨0, hv⟩).trans (hwalk c' c)
      have hne_cross : sat3Bit N c t j.val (by have := j.isLt; omega)
          ≠ sat3Bit N c' ⟨2, by omega⟩ (⟨0, hv⟩ : Fin (sat3V N)).val (by omega) :=
        sat3Bit_ne_of_clause N _ _ _ _ (fun h' => hcc h'.symm)
      have hne_cross' : sat3Bit N c' ⟨2, by omega⟩ (⟨0, hv⟩ : Fin (sat3V N)).val
          (by omega) ≠ sat3Bit N c t j.val (by have := j.isLt; omega) :=
        sat3Bit_ne_of_clause N _ _ _ _ hcc
      rcases hciff with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · -- case A: the selector is in S, the mass is out
        have hB2N : sat3Bit N c ⟨2, by omega⟩ j.val (by have := j.isLt; omega) ∉ S :=
          fun hm => h2 (hB2c.mp hm)
        have hCrN : sat3Bit N c' ⟨2, by omega⟩ (⟨0, hv⟩ : Fin (sat3V N)).val
            (by omega) ∉ S := fun hm => h2 (hB2c'.mp hm)
        obtain ⟨hV1a, hV1b, hV1c⟩ :=
          sat3_same_block_V1_t N hv c t ⟨2, by omega⟩ j j hneB
        obtain ⟨hV0a, hV0b, hV0c⟩ :=
          sat3_cross_block_V0_t N hv c c' (fun h' => hcc h'.symm) t ⟨2, by omega⟩ j ⟨0, hv⟩
        have hodd := sat3_same_block_odd_t N hv c t ⟨2, by omega⟩ j j
        exact triples_kill_split_mixed (sat3Family N) S op g h hg hh hf
          (sat3Bit N c t j.val (by have := j.isLt; omega))
          (sat3Bit N c ⟨2, by omega⟩ j.val (by have := j.isLt; omega))
          (sat3Bit N c t j.val (by have := j.isLt; omega))
          (sat3Bit N c ⟨2, by omega⟩ j.val (by have := j.isLt; omega))
          (sat3Bit N c t j.val (by have := j.isLt; omega))
          (sat3Bit N c' ⟨2, by omega⟩ (⟨0, hv⟩ : Fin (sat3V N)).val (by omega))
          h1 hB2N hneB h1 hB2N hneB h1 hCrN hne_cross
          (sat3ZBase N c)
          (Function.update (sat3ZBase N c)
            (sat3Bit N c ⟨2, by omega⟩ j.val (by have := j.isLt; omega)) true)
          (Function.update (sat3ZBase2 N c c')
            (sat3Bit N c t j.val (by have := j.isLt; omega)) true)
          hodd hV1a hV1b hV1c hV0a hV0b hV0c
      · -- case B: the mass is in S, the selector is out
        have hB2S : sat3Bit N c ⟨2, by omega⟩ j.val (by have := j.isLt; omega) ∈ S :=
          hB2c.mpr h2
        have hCrS : sat3Bit N c' ⟨2, by omega⟩ (⟨0, hv⟩ : Fin (sat3V N)).val
            (by omega) ∈ S := hB2c'.mpr h2
        obtain ⟨hV1a, hV1b, hV1c⟩ :=
          sat3_same_block_V1_t N hv c ⟨2, by omega⟩ t j j hneB.symm
        obtain ⟨hV0a, hV0b, hV0c⟩ :=
          sat3_cross_block_V0_t N hv c' c hcc
            ⟨2, by omega⟩ t ⟨0, hv⟩ j
        have hodd := sat3_same_block_odd_t N hv c ⟨2, by omega⟩ t j j
        exact triples_kill_split_mixed (sat3Family N) S op g h hg hh hf
          (sat3Bit N c ⟨2, by omega⟩ j.val (by have := j.isLt; omega))
          (sat3Bit N c t j.val (by have := j.isLt; omega))
          (sat3Bit N c ⟨2, by omega⟩ j.val (by have := j.isLt; omega))
          (sat3Bit N c t j.val (by have := j.isLt; omega))
          (sat3Bit N c' ⟨2, by omega⟩ (⟨0, hv⟩ : Fin (sat3V N)).val (by omega))
          (sat3Bit N c t j.val (by have := j.isLt; omega))
          hB2S h1 hneB.symm hB2S h1 hneB.symm hCrS h1 hne_cross'
          (sat3ZBase N c)
          (Function.update (sat3ZBase N c)
            (sat3Bit N c t j.val (by have := j.isLt; omega)) true)
          (Function.update (sat3ZBase2 N c' c)
            (sat3Bit N c' ⟨2, by omega⟩ (⟨0, hv⟩ : Fin (sat3V N)).val (by omega)) true)
          hodd hV1a hV1b hV1c hV0a hV0b hV0c

/-- **THE CONDITIONAL RECORD (hypothesis named, not claimed)**: all-selectors residual ⇒
`2·m·D ≤ cbudget`. -/
theorem sat3_cbudget_2mD_of_all_selectors (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (hW : Sat3AllSelectorsMassNoSplit N hm3 hk) :
    2 * (sat3M N * sat3D N) ≤ cbudget (sat3Family N) :=
  sat3_cbudget_2mD_of_core N hv hm3 hk (sat3_core_of_all_selectors N hv hm3 hk hW)

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_core_of_all_selectors
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cbudget_2mD_of_all_selectors
