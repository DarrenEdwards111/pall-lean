import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSlotSignProbes

/-!
# N-Frame: the final reduction — the split hypothesis discharges, the bound fires

The last residual, killed.  Under the exact-layout hypothesis `m·D = N` (every coordinate is a layout
bit — necessary: a padding bit is blind, and a padding-bit cut genuinely admits a split), every
coordinate of `Fin N` is a selector or a sign.  Selectors of all slots and the slot-0 signs are the
united mass; a surviving cut could only move a slot-1/2 sign — and the slot-sign probes kill exactly
that.  If nothing is separated from the mass, the cut is improper.

  `sat3_all_selectors_mass_no_split` — **PROVED, the discharge**: `Sat3AllSelectorsMassNoSplit` holds.
  `sat3_no_bipartite_split_proper` — **PROVED, the hypothesis becomes a theorem**: SAT admits no
        bipartite split over a proper cut.
  `sat3_coneExcess_pos` — **PROVED**: every minimal circuit for SAT has `coneExcess ≥ 1` — positive
        boundary curvature.
  `sat3_cbudget_ge_2N` — **PROVED, THE UNCONDITIONAL RECORD**: `2·N ≤ cbudget (sat3Family N)` — the
        first strict bound beyond the connectivity floor `2·N − 1`, with no hypothesis but the layout
        shape.

## Honest scope

This is a `+1` beyond connectivity — the read-once/excess-zero configuration is now impossible for SAT,
formally.  It is not `Ω(m)` excess, not superlinear, not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.  The next
mountains are unchanged: forced excess `Ω(m)`, curvature accumulation, observer-captures-P.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **THE DISCHARGE (proved)**: under exact layout, the all-selectors-mass residual holds outright. -/
theorem sat3_all_selectors_mass_no_split (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (hDN : sat3M N * sat3D N = N) :
    Sat3AllSelectorsMassNoSplit N hm3 hk := by
  intro op g h S hg hh hf hs ht hal hallt
  classical
  have hm0 : (0 : ℕ) < sat3M N := by omega
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  -- the sign walk
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
  -- coordinate classification under exact layout
  have hclass : ∀ i : Fin N, ∃ (c : Fin (sat3M N)) (tS : Fin 3) (fI : ℕ)
      (hfI : fI < sat3V N + 1), i = sat3Bit N c tS fI hfI := by
    intro i
    have hiN : i.val < N := i.isLt
    have hD : 0 < sat3D N := sat3D_pos N
    have hDval : sat3D N = 3 * (sat3V N + 1) := rfl
    have h1 := Nat.div_add_mod i.val (sat3D N)
    have h2 := Nat.div_add_mod (i.val % sat3D N) (sat3V N + 1)
    have hmodlt : i.val % sat3D N < sat3D N := Nat.mod_lt _ hD
    have hdivm : i.val / sat3D N < sat3M N := by
      rw [Nat.div_lt_iff_lt_mul hD]
      have hDN' : sat3M N * sat3D N = N := hDN
      omega
    have hslot : (i.val % sat3D N) / (sat3V N + 1) < 3 := by
      rw [Nat.div_lt_iff_lt_mul (by omega : 0 < sat3V N + 1)]
      omega
    have hfld : (i.val % sat3D N) % (sat3V N + 1) < sat3V N + 1 :=
      Nat.mod_lt _ (by omega)
    refine ⟨⟨i.val / sat3D N, hdivm⟩,
      ⟨(i.val % sat3D N) / (sat3V N + 1), hslot⟩,
      (i.val % sat3D N) % (sat3V N + 1), hfld, ?_⟩
    apply Fin.ext
    show i.val = (i.val / sat3D N) * sat3D N
      + ((i.val % sat3D N) / (sat3V N + 1)) * (sat3V N + 1)
      + (i.val % sat3D N) % (sat3V N + 1)
    rw [Nat.mul_comm (sat3D N) (i.val / sat3D N)] at h1
    rw [Nat.mul_comm (sat3V N + 1) ((i.val % sat3D N) / (sat3V N + 1))] at h2
    omega
  -- either every sign field is aligned — improper — or a slot-1/2 sign is separated: the kill
  by_cases hsig : ∀ (c : Fin (sat3M N)) (tS : Fin 3),
      (sat3Bit N c tS (sat3V N) (by omega) ∈ S ↔ sat3SignBit N ⟨0, hm0⟩ ∈ S)
  · -- everything aligned with the anchor: the cut is improper
    have halign : ∀ i : Fin N, (i ∈ S ↔ sat3SignBit N ⟨0, hm0⟩ ∈ S) := by
      intro i
      obtain ⟨c, tS, fI, hfI, rfl⟩ := hclass i
      by_cases hfv : fI = sat3V N
      · subst hfv
        exact hsig c tS
      · have hflt : fI < sat3V N := by omega
        exact (show (sat3Bit N c tS (⟨fI, hflt⟩ : Fin (sat3V N)).val
            (by omega) ∈ S ↔ sat3SignBit N c ∈ S) from
          hallt c tS ⟨fI, hflt⟩).trans (hwalk c ⟨0, hm0⟩)
    obtain ⟨s₀, hs₀⟩ := hs
    obtain ⟨t₀, ht₀⟩ := ht
    exact ht₀ ((halign t₀).mpr ((halign s₀).mp hs₀))
  · push_neg at hsig
    obtain ⟨c, tσ, hciff⟩ := hsig
    -- slot-0 sign fields are the walked mass: dispose
    by_cases ht0 : tσ.val = 0
    · exfalso
      have hbit : (sat3Bit N c tσ (sat3V N) (by omega) ∈ S
          ↔ sat3SignBit N ⟨0, hm0⟩ ∈ S) := by
        have hteq : tσ = ⟨0, by omega⟩ := Fin.ext ht0
        rw [hteq]
        exact (show (sat3SignBit N c ∈ S ↔ _) from hwalk c ⟨0, hm0⟩)
      rcases hciff with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2 (hbit.mp h1)
      · exact h1 (hbit.mpr h2)
    · -- the kill at the separated slot-1/2 sign σ
      set w₀ : Fin (sat3M N - 2) := ⟨0, by omega⟩ with hw₀
      have hwv : w₀.val < sat3V N := by
        show (0 : ℕ) < sat3V N
        omega
      have hselT : (sat3Bit N c tσ w₀.val (by omega) ∈ S
          ↔ sat3SignBit N ⟨0, hm0⟩ ∈ S) :=
        (show (sat3Bit N c tσ (⟨w₀.val, hwv⟩ : Fin (sat3V N)).val (by omega) ∈ S
            ↔ sat3SignBit N c ∈ S) from hallt c tσ ⟨w₀.val, hwv⟩).trans
          (hwalk c ⟨0, hm0⟩)
      have hpin : (sat3Bit N (sat3PinClause N c hk w₀) ⟨0, by omega⟩ (sat3V N)
          (by omega) ∈ S ↔ sat3SignBit N ⟨0, hm0⟩ ∈ S) :=
        (show (sat3SignBit N (sat3PinClause N c hk w₀) ∈ S ↔ _) from
          hwalk (sat3PinClause N c hk w₀) ⟨0, hm0⟩)
      have hne_sig_sel : sat3Bit N c tσ (sat3V N) (by omega)
          ≠ sat3Bit N c tσ w₀.val (by omega) :=
        sat3Bit_ne_same_block N c tσ tσ (sat3V N) w₀.val (by omega) (by omega)
          (by rintro ⟨-, h'⟩; omega)
      have hne_sig_pin : sat3Bit N c tσ (sat3V N) (by omega)
          ≠ sat3Bit N (sat3PinClause N c hk w₀) ⟨0, by omega⟩ (sat3V N) (by omega) :=
        sat3Bit_ne_of_clause N _ _ _ _
          (fun h' => sat3PinClause_ne N c hk w₀ h'.symm)
      -- corner values, all four contexts
      have heval := fun bvec b a =>
        slotSignPt_eval N hv hk hkv hm3 c tσ w₀ hwv bvec b a
      -- separate by orientation
      rcases Classical.em (sat3Bit N c tσ (sat3V N) (by omega) ∈ S) with hσ | hσ <;>
        rcases Classical.em (sat3SignBit N ⟨0, hm0⟩ ∈ S) with hM | hM
      · rcases hciff with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact h2 hM
        · exact h1 hσ
      · -- orientation A: σ ∈ S, the mass out
        have hselN : sat3Bit N c tσ w₀.val (by omega) ∉ S :=
          fun hm' => hM (hselT.mp hm')
        have hpinN : sat3Bit N (sat3PinClause N c hk w₀) ⟨0, by omega⟩ (sat3V N)
            (by omega) ∉ S := fun hm' => hM (hpin.mp hm')
        -- odd at (σ, selT), base (b,a) = (1,0), false context
        have hodd : xor (xor
            (sat3Family N (slotSignPt N c hk tσ w₀ hwv (fun _ => false) true false))
            (sat3Family N (Function.update
              (slotSignPt N c hk tσ w₀ hwv (fun _ => false) true false)
              (sat3Bit N c tσ (sat3V N) (by omega))
              (!(slotSignPt N c hk tσ w₀ hwv (fun _ => false) true false
                (sat3Bit N c tσ (sat3V N) (by omega)))))))
          (xor (sat3Family N (Function.update
              (slotSignPt N c hk tσ w₀ hwv (fun _ => false) true false)
              (sat3Bit N c tσ w₀.val (by omega))
              (!(slotSignPt N c hk tσ w₀ hwv (fun _ => false) true false
                (sat3Bit N c tσ w₀.val (by omega))))))
            (sat3Family N (Function.update (Function.update
              (slotSignPt N c hk tσ w₀ hwv (fun _ => false) true false)
              (sat3Bit N c tσ (sat3V N) (by omega))
              (!(slotSignPt N c hk tσ w₀ hwv (fun _ => false) true false
                (sat3Bit N c tσ (sat3V N) (by omega)))))
              (sat3Bit N c tσ w₀.val (by omega))
              (!(slotSignPt N c hk tσ w₀ hwv (fun _ => false) true false
                (sat3Bit N c tσ w₀.val (by omega))))))) = true := by
          rw [slotSignPt_val_sign N c hk tσ w₀ hwv, slotSignPt_val_sel N c hk tσ w₀ hwv]
          rw [slotSignPt_flip_sign N c hk tσ w₀ hwv, slotSignPt_flip_sel N c hk tσ w₀ hwv,
            slotSignPt_flip_sel N c hk tσ w₀ hwv]
          rw [heval, heval, heval, heval]
          rfl
        -- V1 at (σ, pinSign), base (1,1), false context
        have hV1a : sat3Family N (slotSignPt N c hk tσ w₀ hwv (fun _ => false) true true)
            = true := by
          rw [heval]
          rfl
        have hV1c : sat3Family N (Function.update
            (slotSignPt N c hk tσ w₀ hwv (fun _ => false) true true)
            (sat3Bit N (sat3PinClause N c hk w₀) ⟨0, by omega⟩ (sat3V N) (by omega))
            (!(slotSignPt N c hk tσ w₀ hwv (fun _ => false) true true
              (sat3Bit N (sat3PinClause N c hk w₀) ⟨0, by omega⟩ (sat3V N)
                (by omega))))) = false := by
          rw [slotSignPt_val_pin N c hk hkv tσ w₀ hwv,
            slotSignPt_flip_pin N c hk hkv tσ w₀ hwv, heval, Function.update_self]
          rfl
        have hV1b : sat3Family N (Function.update (Function.update
            (slotSignPt N c hk tσ w₀ hwv (fun _ => false) true true)
            (sat3Bit N c tσ (sat3V N) (by omega))
            (!(slotSignPt N c hk tσ w₀ hwv (fun _ => false) true true
              (sat3Bit N c tσ (sat3V N) (by omega)))))
            (sat3Bit N (sat3PinClause N c hk w₀) ⟨0, by omega⟩ (sat3V N) (by omega))
            (!(slotSignPt N c hk tσ w₀ hwv (fun _ => false) true true
              (sat3Bit N (sat3PinClause N c hk w₀) ⟨0, by omega⟩ (sat3V N)
                (by omega))))) = true := by
          rw [slotSignPt_val_sign N c hk tσ w₀ hwv,
            slotSignPt_val_pin N c hk hkv tσ w₀ hwv,
            slotSignPt_flip_sign N c hk tσ w₀ hwv,
            slotSignPt_flip_pin N c hk hkv tσ w₀ hwv, heval, Function.update_self]
          rfl
        -- V0 at (σ, pinSign), base (1,0), false context
        have hV0a : sat3Family N (slotSignPt N c hk tσ w₀ hwv (fun _ => false) true false)
            = false := by
          rw [heval]
          rfl
        have hV0c : sat3Family N (Function.update
            (slotSignPt N c hk tσ w₀ hwv (fun _ => false) true false)
            (sat3Bit N (sat3PinClause N c hk w₀) ⟨0, by omega⟩ (sat3V N) (by omega))
            (!(slotSignPt N c hk tσ w₀ hwv (fun _ => false) true false
              (sat3Bit N (sat3PinClause N c hk w₀) ⟨0, by omega⟩ (sat3V N)
                (by omega))))) = true := by
          rw [slotSignPt_val_pin N c hk hkv tσ w₀ hwv,
            slotSignPt_flip_pin N c hk hkv tσ w₀ hwv, heval, Function.update_self]
          rfl
        have hV0b : sat3Family N (Function.update (Function.update
            (slotSignPt N c hk tσ w₀ hwv (fun _ => false) true false)
            (sat3Bit N c tσ (sat3V N) (by omega))
            (!(slotSignPt N c hk tσ w₀ hwv (fun _ => false) true false
              (sat3Bit N c tσ (sat3V N) (by omega)))))
            (sat3Bit N (sat3PinClause N c hk w₀) ⟨0, by omega⟩ (sat3V N) (by omega))
            (!(slotSignPt N c hk tσ w₀ hwv (fun _ => false) true false
              (sat3Bit N (sat3PinClause N c hk w₀) ⟨0, by omega⟩ (sat3V N)
                (by omega))))) = false := by
          rw [slotSignPt_val_sign N c hk tσ w₀ hwv,
            slotSignPt_val_pin N c hk hkv tσ w₀ hwv,
            slotSignPt_flip_sign N c hk tσ w₀ hwv,
            slotSignPt_flip_pin N c hk hkv tσ w₀ hwv, heval, Function.update_self]
          rfl
        exact triples_kill_split_mixed (sat3Family N) S op g h hg hh hf
          (sat3Bit N c tσ (sat3V N) (by omega)) (sat3Bit N c tσ w₀.val (by omega))
          (sat3Bit N c tσ (sat3V N) (by omega))
          (sat3Bit N (sat3PinClause N c hk w₀) ⟨0, by omega⟩ (sat3V N) (by omega))
          (sat3Bit N c tσ (sat3V N) (by omega))
          (sat3Bit N (sat3PinClause N c hk w₀) ⟨0, by omega⟩ (sat3V N) (by omega))
          hσ hselN hne_sig_sel hσ hpinN hne_sig_pin hσ hpinN hne_sig_pin
          (slotSignPt N c hk tσ w₀ hwv (fun _ => false) true false)
          (slotSignPt N c hk tσ w₀ hwv (fun _ => false) true true)
          (slotSignPt N c hk tσ w₀ hwv (fun _ => false) true false)
          hodd hV1a hV1b hV1c hV0a hV0b hV0c
      · -- orientation B: the mass in S, σ out
        have hselS : sat3Bit N c tσ w₀.val (by omega) ∈ S := hselT.mpr hM
        have hpinS : sat3Bit N (sat3PinClause N c hk w₀) ⟨0, by omega⟩ (sat3V N)
            (by omega) ∈ S := hpin.mpr hM
        have hodd : xor (xor
            (sat3Family N (slotSignPt N c hk tσ w₀ hwv (fun _ => false) true false))
            (sat3Family N (Function.update
              (slotSignPt N c hk tσ w₀ hwv (fun _ => false) true false)
              (sat3Bit N c tσ w₀.val (by omega))
              (!(slotSignPt N c hk tσ w₀ hwv (fun _ => false) true false
                (sat3Bit N c tσ w₀.val (by omega)))))))
          (xor (sat3Family N (Function.update
              (slotSignPt N c hk tσ w₀ hwv (fun _ => false) true false)
              (sat3Bit N c tσ (sat3V N) (by omega))
              (!(slotSignPt N c hk tσ w₀ hwv (fun _ => false) true false
                (sat3Bit N c tσ (sat3V N) (by omega))))))
            (sat3Family N (Function.update (Function.update
              (slotSignPt N c hk tσ w₀ hwv (fun _ => false) true false)
              (sat3Bit N c tσ w₀.val (by omega))
              (!(slotSignPt N c hk tσ w₀ hwv (fun _ => false) true false
                (sat3Bit N c tσ w₀.val (by omega)))))
              (sat3Bit N c tσ (sat3V N) (by omega))
              (!(slotSignPt N c hk tσ w₀ hwv (fun _ => false) true false
                (sat3Bit N c tσ (sat3V N) (by omega))))))) = true := by
          rw [slotSignPt_val_sign N c hk tσ w₀ hwv, slotSignPt_val_sel N c hk tσ w₀ hwv]
          rw [slotSignPt_flip_sel N c hk tσ w₀ hwv, slotSignPt_flip_sign N c hk tσ w₀ hwv,
            slotSignPt_flip_sign N c hk tσ w₀ hwv]
          rw [heval, heval, heval, heval]
          rfl
        have hV1a : sat3Family N (slotSignPt N c hk tσ w₀ hwv (fun _ => false) true true)
            = true := by
          rw [heval]
          rfl
        have hV1c : sat3Family N (Function.update
            (slotSignPt N c hk tσ w₀ hwv (fun _ => false) true true)
            (sat3Bit N c tσ (sat3V N) (by omega))
            (!(slotSignPt N c hk tσ w₀ hwv (fun _ => false) true true
              (sat3Bit N c tσ (sat3V N) (by omega))))) = false := by
          rw [slotSignPt_val_sign N c hk tσ w₀ hwv,
            slotSignPt_flip_sign N c hk tσ w₀ hwv, heval]
          rfl
        have hV1b : sat3Family N (Function.update (Function.update
            (slotSignPt N c hk tσ w₀ hwv (fun _ => false) true true)
            (sat3Bit N (sat3PinClause N c hk w₀) ⟨0, by omega⟩ (sat3V N) (by omega))
            (!(slotSignPt N c hk tσ w₀ hwv (fun _ => false) true true
              (sat3Bit N (sat3PinClause N c hk w₀) ⟨0, by omega⟩ (sat3V N)
                (by omega)))))
            (sat3Bit N c tσ (sat3V N) (by omega))
            (!(slotSignPt N c hk tσ w₀ hwv (fun _ => false) true true
              (sat3Bit N c tσ (sat3V N) (by omega))))) = true := by
          rw [slotSignPt_val_pin N c hk hkv tσ w₀ hwv,
            slotSignPt_val_sign N c hk tσ w₀ hwv,
            slotSignPt_flip_pin N c hk hkv tσ w₀ hwv,
            slotSignPt_flip_sign N c hk tσ w₀ hwv, heval, Function.update_self]
          rfl
        have hV0a : sat3Family N (slotSignPt N c hk tσ w₀ hwv (fun _ => true) true true)
            = false := by
          rw [heval]
          rfl
        have hV0c : sat3Family N (Function.update
            (slotSignPt N c hk tσ w₀ hwv (fun _ => true) true true)
            (sat3Bit N c tσ (sat3V N) (by omega))
            (!(slotSignPt N c hk tσ w₀ hwv (fun _ => true) true true
              (sat3Bit N c tσ (sat3V N) (by omega))))) = true := by
          rw [slotSignPt_val_sign N c hk tσ w₀ hwv,
            slotSignPt_flip_sign N c hk tσ w₀ hwv, heval]
          rfl
        have hV0b : sat3Family N (Function.update (Function.update
            (slotSignPt N c hk tσ w₀ hwv (fun _ => true) true true)
            (sat3Bit N (sat3PinClause N c hk w₀) ⟨0, by omega⟩ (sat3V N) (by omega))
            (!(slotSignPt N c hk tσ w₀ hwv (fun _ => true) true true
              (sat3Bit N (sat3PinClause N c hk w₀) ⟨0, by omega⟩ (sat3V N)
                (by omega)))))
            (sat3Bit N c tσ (sat3V N) (by omega))
            (!(slotSignPt N c hk tσ w₀ hwv (fun _ => true) true true
              (sat3Bit N c tσ (sat3V N) (by omega))))) = false := by
          rw [slotSignPt_val_pin N c hk hkv tσ w₀ hwv,
            slotSignPt_val_sign N c hk tσ w₀ hwv,
            slotSignPt_flip_pin N c hk hkv tσ w₀ hwv,
            slotSignPt_flip_sign N c hk tσ w₀ hwv, heval, Function.update_self]
          rfl
        exact triples_kill_split_mixed (sat3Family N) S op g h hg hh hf
          (sat3Bit N c tσ w₀.val (by omega)) (sat3Bit N c tσ (sat3V N) (by omega))
          (sat3Bit N (sat3PinClause N c hk w₀) ⟨0, by omega⟩ (sat3V N) (by omega))
          (sat3Bit N c tσ (sat3V N) (by omega))
          (sat3Bit N (sat3PinClause N c hk w₀) ⟨0, by omega⟩ (sat3V N) (by omega))
          (sat3Bit N c tσ (sat3V N) (by omega))
          hselS hσ hne_sig_sel.symm hpinS hσ hne_sig_pin.symm hpinS hσ hne_sig_pin.symm
          (slotSignPt N c hk tσ w₀ hwv (fun _ => false) true false)
          (slotSignPt N c hk tσ w₀ hwv (fun _ => false) true true)
          (slotSignPt N c hk tσ w₀ hwv (fun _ => true) true true)
          hodd hV1a hV1b hV1c hV0a hV0b hV0c
      · rcases hciff with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact hσ h1
        · exact hM h2

/-- **THE HYPOTHESIS BECOMES A THEOREM (proved)**: SAT admits no bipartite split over a proper cut. -/
theorem sat3_no_bipartite_split_proper (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (hDN : sat3M N * sat3D N = N) : Sat3NoBipartiteSplitProper N :=
  sat3_no_split_of_all_pins_aligned N hv hm3 hk
    (sat3_all_pins_aligned_of_block_monolithic N hv hm3 hk
      (sat3_block_monolithic_of_mass N hv hm3 hk
        (sat3_mass_of_core N hv hm3 hk
          (sat3_core_of_all_selectors N hv hm3 hk
            (sat3_all_selectors_mass_no_split N hv hm3 hk hDN)))))

/-- **POSITIVE BOUNDARY CURVATURE (proved)**: every minimal SAT circuit has `coneExcess ≥ 1`. -/
theorem sat3_coneExcess_pos (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (hDN : sat3M N * sat3D N = N)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hmin : c.length = cbudget (sat3Family N)) :
    1 ≤ coneExcess c (c.length - 1) :=
  sat3_excess_pos_of_no_proper_split N hv hm3 hk
    (sat3_no_bipartite_split_proper N hv hm3 hk hDN) c hcomp hmin

/-- **THE UNCONDITIONAL RECORD (proved)**: `2·m·D ≤ cbudget (sat3Family N)`. -/
theorem sat3_cbudget_ge_2mD (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (hDN : sat3M N * sat3D N = N) :
    2 * (sat3M N * sat3D N) ≤ cbudget (sat3Family N) :=
  sat3_cbudget_2mD_of_no_proper_split N hv hm3 hk
    (sat3_no_bipartite_split_proper N hv hm3 hk hDN)

/-- **THE HEADLINE (proved)**: `2·N ≤ cbudget (sat3Family N)` — one strict step beyond the
connectivity floor `2·N − 1`, unconditionally. -/
theorem sat3_cbudget_ge_2N (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (hDN : sat3M N * sat3D N = N) :
    2 * N ≤ cbudget (sat3Family N) := by
  have h := sat3_cbudget_ge_2mD N hv hm3 hk hDN
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_no_bipartite_split_proper
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_coneExcess_pos
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cbudget_ge_2N
