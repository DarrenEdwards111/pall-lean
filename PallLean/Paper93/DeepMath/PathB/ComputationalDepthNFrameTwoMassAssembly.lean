import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFramePinnedSelectorPatterns

/-!
# N-Frame: the two-mass assembly — the selector and sign masses may no longer separate

The mixed engine fired on the two-mass cut.

  `sat3_mass_of_core` — **PROVED, the reduction**: the two-mass branch of `Sat3MonolithicMassNoSplit`
        discharges.  The pins-alignment graph is connected (every block's pin family reaches block `0`),
        so the slot-0 sign layer is one mass; if the slot-2 selector layer is globally monolithic and
        sits on the *opposite* side, the pair (designated sign, slot-2 selector) carries odd + V1 and the
        pair (slot-2 selector, pin-sign) carries V0 — all separated, `triples_kill_split_mixed` fires,
        both orientations handled with no massage (case A takes the AND-pair odd, case B the OR-pair
        odd).
  `Sat3CoreMassNoSplit` — the **thinned residual** (NOT discharged): pins aligned, blocks monolithic,
        and **every slot-2 selector aligned with every sign** — the two layers are one united mass.
  `sat3_cbudget_2mD_of_core` — the conditional record through the full chain.

## Honest scope

The surviving cuts now keep the entire slot-2 selector layer and the entire slot-0 sign layer on one
common side.  The only movable pieces left are slot-0/1 selectors and slot-1/2 sign fields — the last
two coordinate families without produced patterns (general-slot `ZBase` flips and slot-`t` probes, each
a mirror of an existing build).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- The **thinned residual** (NOT discharged): the slot-2 and sign layers are one united mass. -/
def Sat3CoreMassNoSplit (N : ℕ) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) : Prop :=
  ∀ (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (S : Finset (Fin N)),
    (∀ x y : Fin N → Bool, (∀ i, i ∈ S → x i = y i) → g x = g y) →
    (∀ x y : Fin N → Bool, (∀ i, i ∉ S → x i = y i) → h x = h y) →
    (∀ x, sat3Family N x = op (g x) (h x)) →
    (∃ s₀ : Fin N, s₀ ∈ S) → (∃ t₀ : Fin N, t₀ ∉ S) →
    (∀ (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2)),
      (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∈ S ↔ sat3SignBit N cIdx ∈ S)) →
    (∀ (c : Fin (sat3M N)) (j₁ j₂ : Fin (sat3V N)),
      (sat3S2Sel N c j₁ ∈ S ↔ sat3S2Sel N c j₂ ∈ S)) →
    (∀ (c : Fin (sat3M N)) (j : Fin (sat3V N)),
      (sat3S2Sel N c j ∈ S ↔ sat3SignBit N c ∈ S)) → False

/-- **THE REDUCTION (proved)**: killing united-mass cuts suffices — opposite masses die by the mixed
engine on the AND and OR pattern pairs. -/
theorem sat3_mass_of_core (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (hW : Sat3CoreMassNoSplit N hm3 hk) :
    Sat3MonolithicMassNoSplit N hm3 hk := by
  intro op g h S hg hh hf hs ht hal hmono hdisj
  classical
  have hm0 : (0 : ℕ) < sat3M N := by omega
  -- the pins-alignment graph is connected: every sign aligns with block 0's sign
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
  rcases hdisj with hss | hglob
  · -- sign↔selector aligned on pinned variables: the layers are already united
    apply hW op g h S hg hh hf hs ht hal hmono
    intro c j
    exact (hmono c j ⟨0, hv⟩).trans (hss c ⟨0, hv⟩ (by show (0 : ℕ) < sat3M N - 2; omega))
  · -- slot-2 globally monolithic
    by_cases hunited : (sat3S2Sel N ⟨0, hm0⟩ ⟨0, hv⟩ ∈ S
        ↔ sat3SignBit N ⟨0, hm0⟩ ∈ S)
    · -- united masses: feed the core
      apply hW op g h S hg hh hf hs ht hal hmono
      intro c j
      exact ((hglob c ⟨0, hm0⟩ j ⟨0, hv⟩).trans hunited).trans
        (hwalk ⟨0, hm0⟩ c)
    · -- opposite masses: the two-mass kill at block 0, pinned variable 0
      set c₀ : Fin (sat3M N) := ⟨0, hm0⟩ with hc₀
      set j₀ : Fin (sat3M N - 2) := ⟨0, by omega⟩ with hj₀
      have hjv : j₀.val < sat3V N := by
        show (0 : ℕ) < sat3V N
        omega
      have hkv : sat3M N - 2 ≤ sat3V N := by
        have := sat3M_pred_le_sat3V N
        omega
      have hne_ss : sat3S2Sel N c₀ ⟨j₀.val, hjv⟩ ≠ sat3SignBit N c₀ :=
        sat3S2Sel_ne_signBit N c₀ ⟨j₀.val, hjv⟩ c₀
      have hne_sp : sat3S2Sel N c₀ ⟨j₀.val, hjv⟩
          ≠ sat3Bit N (sat3PinClause N c₀ hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega) :=
        (sat3Bit_ne_s2sel_of_clause N (sat3PinClause N c₀ hk j₀) c₀
          (sat3PinClause_ne N c₀ hk j₀) _ _ _ ⟨j₀.val, hjv⟩).symm
      have hps : (sat3Bit N (sat3PinClause N c₀ hk j₀) ⟨0, by omega⟩ (sat3V N)
          (by omega) : Fin N) = sat3SignBit N (sat3PinClause N c₀ hk j₀) := rfl
      have hselmatch : sat3S2Sel N c₀ ⟨j₀.val, hjv⟩ ∈ S
          ↔ sat3S2Sel N c₀ ⟨0, hv⟩ ∈ S :=
        hglob c₀ c₀ ⟨j₀.val, hjv⟩ ⟨0, hv⟩
      have hpinwalk : (sat3Bit N (sat3PinClause N c₀ hk j₀) ⟨0, by omega⟩ (sat3V N)
          (by omega) ∈ S) ↔ sat3SignBit N c₀ ∈ S := by
        rw [hps]
        exact hwalk (sat3PinClause N c₀ hk j₀) c₀
      rcases Classical.em (sat3S2Sel N c₀ ⟨0, hv⟩ ∈ S) with h1 | h1
      · rcases Classical.em (sat3SignBit N c₀ ∈ S) with h2 | h2
        · exact hunited ⟨fun _ => h2, fun _ => h1⟩
        · -- case A: selector mass in S, sign mass out
          have hselS : sat3S2Sel N c₀ ⟨j₀.val, hjv⟩ ∈ S := hselmatch.mpr h1
          have hpinN : sat3Bit N (sat3PinClause N c₀ hk j₀) ⟨0, by omega⟩ (sat3V N)
              (by omega) ∉ S := fun hmem => h2 (hpinwalk.mp hmem)
          obtain ⟨hV1a, hV1b, hV1c⟩ :=
            sat3_sign_selector_V1_signDown N hv hk hkv hm3 c₀ j₀ hjv
          obtain ⟨hV0a, hV0b, hV0c⟩ :=
            sat3_selector_pinsign_V0_selDown N hv hk hkv hm3 c₀ j₀ hjv
          have hodd := sat3_selector_pinsign_odd N hv hk hkv hm3 c₀ j₀ hjv
          exact triples_kill_split_mixed (sat3Family N) S op g h hg hh hf
            (sat3S2Sel N c₀ ⟨j₀.val, hjv⟩)
            (sat3Bit N (sat3PinClause N c₀ hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
            (sat3S2Sel N c₀ ⟨j₀.val, hjv⟩) (sat3SignBit N c₀)
            (sat3S2Sel N c₀ ⟨j₀.val, hjv⟩)
            (sat3Bit N (sat3PinClause N c₀ hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
            hselS hpinN hne_sp hselS h2 hne_ss hselS hpinN hne_sp
            (pinnedPt N c₀ hk j₀ hjv (fun _ => false) true)
            (mixedPt N c₀ hk j₀ hjv false false)
            (pinnedPt N c₀ hk j₀ hjv (fun _ => false) true)
            hodd hV1a hV1b hV1c hV0a hV0b hV0c
      · rcases Classical.em (sat3SignBit N c₀ ∈ S) with h2 | h2
        · -- case B: sign mass in S, selector mass out
          have hselN : sat3S2Sel N c₀ ⟨j₀.val, hjv⟩ ∉ S :=
            fun hmem => h1 (hselmatch.mp hmem)
          have hpinS : sat3Bit N (sat3PinClause N c₀ hk j₀) ⟨0, by omega⟩ (sat3V N)
              (by omega) ∈ S := hpinwalk.mpr h2
          obtain ⟨hV1a, hV1b, hV1c⟩ :=
            sat3_sign_selector_V1_selDown N hv hk hkv hm3 c₀ j₀ hjv
          obtain ⟨hV0a, hV0b, hV0c⟩ :=
            sat3_selector_pinsign_V0_pinDown N hv hk hkv hm3 c₀ j₀ hjv
          have hodd := sat3_sign_selector_odd N hv hk hkv hm3 c₀ j₀ hjv
          exact triples_kill_split_mixed (sat3Family N) S op g h hg hh hf
            (sat3SignBit N c₀) (sat3S2Sel N c₀ ⟨j₀.val, hjv⟩)
            (sat3SignBit N c₀) (sat3S2Sel N c₀ ⟨j₀.val, hjv⟩)
            (sat3Bit N (sat3PinClause N c₀ hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
            (sat3S2Sel N c₀ ⟨j₀.val, hjv⟩)
            h2 hselN hne_ss.symm h2 hselN hne_ss.symm hpinS hselN hne_sp.symm
            (mixedPt N c₀ hk j₀ hjv true false)
            (mixedPt N c₀ hk j₀ hjv true true)
            (pinnedPt N c₀ hk j₀ hjv (fun _ => true) false)
            hodd hV1a hV1b hV1c hV0a hV0b hV0c
        · exact hunited ⟨fun hh => absurd hh h1, fun hh => absurd hh h2⟩

/-- **THE CONDITIONAL RECORD (hypothesis named, not claimed)**: united-mass residual ⇒
`2·m·D ≤ cbudget`. -/
theorem sat3_cbudget_2mD_of_core (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (hW : Sat3CoreMassNoSplit N hm3 hk) :
    2 * (sat3M N * sat3D N) ≤ cbudget (sat3Family N) :=
  sat3_cbudget_2mD_of_mass N hv hm3 hk (sat3_mass_of_core N hv hm3 hk hW)

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_mass_of_core
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cbudget_2mD_of_core
