import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFramePinSlotParametric

/-!
# N-Frame: the pin-slot assembly — parametric drag and window

Rung 20 of the multi-block arc (… → pin-slot pins → **assembly**).  This file completes the
parametric machinery: the private-kit drag and the cardinality-only window with the pin slot
`ps` as a parameter, so the pin channel can be routed to whichever sign column the rung-17
squeeze certifies live.

  `sat3ContextP_agree` — contexts with different pin vectors agree except at the slot-`ps`
        sign bits of differing pins.
  `sat3_pinslot_ctx_transfer` — the context transfer on `S`: differing pins' `ps`-sign bits
        off `S` suffice.
  `sat3RowPS` / `sat3RowPS_read` — the row family (patterns + constant private kit) over the
        parametric context.
  `sat3_pinslot_mix_transfer` — the mix: probe from `Sᶜ` onto a stored row yields the
        parametric eval instance; only pattern bits in `S` and `ps`-sign pin bits off `S`.
  `sat3_pinslot_selector_drag` — **PROVED**: `Σ_{c ∈ C} |V c| ≤ j` with the pin channel at ANY
        slot `ps` — no slot-1 conditions, pool gated only by the `ps`-sign column.
  `sat3_pinslot_pin_sign_count` / `sat3_pinslot_window` — **PROVED, the parametric window**:
        cardinality room alone (`m − |C| ≤ v`, `|⋃V| + |C| ≤ v`,
        `|⋃V| + |C| + Q_{ps} ≤ m − |C|`) prices `Σ_{c ∈ C} |V c| ≤ j`, where `Q_{ps}` counts
        pool blocks sign-poisoned AT THE CHOSEN SLOT only.

## Honest scope — the corrected cash-out

Pressure-testing the full band arithmetic BEFORE this build corrected the target.  With the
squeeze selecting a live pin slot (`Q_{ps} ≤ j + 2` for some `ps`, else all slots nearly full),
the parametric window fires at heavy bands whenever `Θ(m)` blocks are fully-in at some data
slot, yielding `j ≥ Θ(m²) = Θ(N)` — BUT the straddle channel caps the adversary's obligation:
up to `j` straddling blocks (rung 18) may carry `j·v` mass, so at `T = Θ(m·v)` the dichotomy
closes to `j ≥ min(Θ(m²), (T − slack)/(3v)) = Ω(m)`.  The honest rung-21 assembly target is
therefore `coneExcess = Ω(m) = Ω(√N)` UNIFORMLY AT EVERY BAND — closing the heavy-band gap of
rung 17 — while `(2+c)·N` remains blocked by the straddle/pool ceiling: `j` straddlers holding
`j·v` mass is the exact configuration no instrument in this framework prices beyond `Ω(m)`.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Context agreement and transfer -/

theorem sat3ContextP_agree (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b b' : Fin k → Bool) (ps : Fin 3) (i : Fin N)
    (hag : ∀ p : Fin k, i.val / sat3D N = (sat3PinClauseM N C hk p).val →
      i.val % sat3D N = ps.val * (sat3V N + 1) + sat3V N → b p = b' p) :
    sat3ContextP N C hk α b ps i = sat3ContextP N C hk α b' ps i := by
  show decide _ = decide _
  apply decide_eq_decide.mpr
  constructor
  · rintro (⟨p, hp1, hp2 | ⟨hp2, hp3⟩⟩ | hother)
    · exact Or.inl ⟨p, hp1, Or.inl hp2⟩
    · exact Or.inl ⟨p, hp1, Or.inr ⟨hp2, by rw [← hag p hp1 hp2]; exact hp3⟩⟩
    · exact Or.inr hother
  · rintro (⟨p, hp1, hp2 | ⟨hp2, hp3⟩⟩ | hother)
    · exact Or.inl ⟨p, hp1, Or.inl hp2⟩
    · exact Or.inl ⟨p, hp1, Or.inr ⟨hp2, by rw [hag p hp1 hp2]; exact hp3⟩⟩
    · exact Or.inr hother

theorem sat3_pinslot_ctx_transfer (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (V : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (ps : Fin 3) {S : Finset (Fin N)}
    (hsign : ∀ p : Fin k, (∃ c ∈ C, α p ∈ V c) →
      sat3Bit N (sat3PinClauseM N C hk p) ps (sat3V N) (by omega) ∉ S)
    (b b' : Fin k → Bool)
    (hbb : ∀ p : Fin k, b p ≠ b' p → (∃ c ∈ C, α p ∈ V c))
    (i : Fin N) (hi : i ∈ S) :
    sat3ContextP N C hk α b ps i = sat3ContextP N C hk α b' ps i := by
  apply sat3ContextP_agree
  intro p hp1 hp2
  by_contra hbne
  apply hsign p (hbb p hbne)
  have hiπ : sat3Bit N (sat3PinClauseM N C hk p) ps (sat3V N)
      (by omega) = i := by
    apply Fin.ext
    show (sat3PinClauseM N C hk p).val * sat3D N + ps.val * (sat3V N + 1) + sat3V N
      = i.val
    have hdm := Nat.div_add_mod i.val (sat3D N)
    rw [hp1, hp2] at hdm
    have hcm : sat3D N * (sat3PinClauseM N C hk p).val
        = (sat3PinClauseM N C hk p).val * sat3D N := Nat.mul_comm _ _
    omega
  rw [hiπ]
  exact hi

/-! ### The row family -/

/-- The parametric row for tuple `E`: all-false pins at slot `ps`, block `c` carrying the
tuple's slot-0 pattern AND the constant kit `{u c}`. -/
noncomputable def sat3RowPS (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (ps : Fin 3)
    (V : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (u : Fin (sat3M N) → Fin (sat3V N))
    (E : Finset ((_ : Fin (sat3M N)) × Fin (sat3V N))) : Fin N → Bool :=
  sat3PatchMulti N C (sat3ContextP N C hk α (fun _ => false) ps)
    (sat3KitP N (sat3TupleOf N V E) u)

theorem sat3RowPS_read (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (ps : Fin 3)
    (V : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (u : Fin (sat3M N) → Fin (sat3V N))
    (E : Finset ((_ : Fin (sat3M N)) × Fin (sat3V N)))
    (c : Fin (sat3M N)) (hcC : c ∈ C) (w : Fin (sat3V N)) :
    sat3RowPS N C hk α ps V u E
      (sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega))
      = decide (w ∈ sat3TupleOf N V E c) := by
  unfold sat3RowPS
  rw [sat3PatchMulti_own N C (sat3ContextP N C hk α (fun _ => false) ps)
    (sat3KitP N (sat3TupleOf N V E) u) c hcC]
  have hr : (sat3Bit N c ⟨0, by omega⟩ w.val
      (by have := w.isLt; omega)).val % sat3D N = w.val := by
    rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + w.val = w.val
    omega
  show decide _ = decide (w ∈ sat3TupleOf N V E c)
  apply decide_eq_decide.mpr
  constructor
  · rintro (⟨w', hw', hrem⟩ | hrem)
    · rw [hr] at hrem
      rw [show w = w' from Fin.ext hrem]
      exact hw'
    · rw [hr] at hrem
      have := w.isLt
      have := (u c).isLt
      omega
  · intro hw
    exact Or.inl ⟨w, hw, hr⟩

/-! ### The mix transfer -/

set_option maxHeartbeats 1600000 in
/-- **The parametric mix transfer (proved)**: overlaying the mode probe from `Sᶜ` onto a stored
row yields the parametric eval instance — pattern bits in `S`, `ps`-sign pin bits off `S`,
nothing else. -/
theorem sat3_pinslot_mix_transfer (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (ps : Fin 3)
    (V : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (u : Fin (sat3M N) → Fin (sat3V N))
    {S : Finset (Fin N)}
    (hdata : ∀ c ∈ C, ∀ w ∈ V c,
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)
    (hsign : ∀ p : Fin k, (∃ c ∈ C, α p ∈ insert (u c) (V c)) →
      sat3Bit N (sat3PinClauseM N C hk p) ps (sat3V N) (by omega) ∉ S)
    (cstar : Fin (sat3M N)) (hcstar : cstar ∈ C)
    (wstar : Fin (sat3V N)) (hwstarV : wstar ∈ V cstar)
    (E E'' : Finset ((_ : Fin (sat3M N)) × Fin (sat3V N))) :
    mixOn Sᶜ
      (sat3PatchMulti N C (sat3ContextP N C hk α (fun p =>
        decide (α p = wstar ∨ ∃ c ∈ C, c ≠ cstar ∧ α p = u c)) ps)
        (sat3KitP N (sat3TupleOf N V E) u))
      (sat3RowPS N C hk α ps V u E'')
      = sat3PatchMulti N C (sat3ContextP N C hk α (fun p =>
        decide (α p = wstar ∨ ∃ c ∈ C, c ≠ cstar ∧ α p = u c)) ps)
        (sat3KitP N (sat3TupleOf N V E'') u) := by
  classical
  set bvs : Fin k → Bool := fun p =>
    decide (α p = wstar ∨ ∃ c ∈ C, c ≠ cstar ∧ α p = u c) with hbvs
  funext i
  show (if i ∈ Sᶜ
      then sat3PatchMulti N C (sat3ContextP N C hk α bvs ps)
        (sat3KitP N (sat3TupleOf N V E) u) i
      else sat3RowPS N C hk α ps V u E'' i)
    = sat3PatchMulti N C (sat3ContextP N C hk α bvs ps)
        (sat3KitP N (sat3TupleOf N V E'') u) i
  by_cases hi : i ∈ Sᶜ
  · rw [if_pos hi]
    have hiNS : i ∉ S := Finset.mem_compl.mp hi
    show (if h : i.val / sat3D N < sat3M N then
        if (⟨i.val / sat3D N, h⟩ : Fin (sat3M N)) ∈ C
        then sat3KitP N (sat3TupleOf N V E) u ⟨i.val / sat3D N, h⟩ i
        else sat3ContextP N C hk α bvs ps i
      else sat3ContextP N C hk α bvs ps i)
      = (if h : i.val / sat3D N < sat3M N then
        if (⟨i.val / sat3D N, h⟩ : Fin (sat3M N)) ∈ C
        then sat3KitP N (sat3TupleOf N V E'') u ⟨i.val / sat3D N, h⟩ i
        else sat3ContextP N C hk α bvs ps i
      else sat3ContextP N C hk α bvs ps i)
    by_cases hdiv : i.val / sat3D N < sat3M N
    · rw [dif_pos hdiv, dif_pos hdiv]
      by_cases hmem : (⟨i.val / sat3D N, hdiv⟩ : Fin (sat3M N)) ∈ C
      · rw [if_pos hmem, if_pos hmem]
        show decide _ = decide _
        apply decide_eq_decide.mpr
        constructor
        · rintro (⟨w, hw, hrem⟩ | hkit)
          · exfalso
            apply hiNS
            have hiw : sat3Bit N ⟨i.val / sat3D N, hdiv⟩ ⟨0, by omega⟩ w.val
                (by have := w.isLt; omega) = i := by
              apply Fin.ext
              show i.val / sat3D N * sat3D N + 0 * (sat3V N + 1) + w.val = i.val
              have hdm := Nat.div_add_mod i.val (sat3D N)
              rw [hrem] at hdm
              have hcm : sat3D N * (i.val / sat3D N)
                  = i.val / sat3D N * sat3D N := Nat.mul_comm _ _
              omega
            rw [← hiw]
            exact hdata ⟨i.val / sat3D N, hdiv⟩ hmem w
              (sat3TupleOf_subset N V E _ hw)
          · exact Or.inr hkit
        · rintro (⟨w, hw, hrem⟩ | hkit)
          · exfalso
            apply hiNS
            have hiw : sat3Bit N ⟨i.val / sat3D N, hdiv⟩ ⟨0, by omega⟩ w.val
                (by have := w.isLt; omega) = i := by
              apply Fin.ext
              show i.val / sat3D N * sat3D N + 0 * (sat3V N + 1) + w.val = i.val
              have hdm := Nat.div_add_mod i.val (sat3D N)
              rw [hrem] at hdm
              have hcm : sat3D N * (i.val / sat3D N)
                  = i.val / sat3D N * sat3D N := Nat.mul_comm _ _
              omega
            rw [← hiw]
            exact hdata ⟨i.val / sat3D N, hdiv⟩ hmem w
              (sat3TupleOf_subset N V E'' _ hw)
          · exact Or.inr hkit
      · rw [if_neg hmem, if_neg hmem]
    · rw [dif_neg hdiv, dif_neg hdiv]
  · rw [if_neg hi]
    have hiS : i ∈ S := by
      by_contra hiS
      exact hi (Finset.mem_compl.mpr hiS)
    have hbb : ∀ p : Fin k, (fun _ : Fin k => false) p ≠ bvs p →
        (∃ c ∈ C, α p ∈ insert (u c) (V c)) := by
      intro p hp
      by_cases hval : α p = wstar ∨ ∃ c ∈ C, c ≠ cstar ∧ α p = u c
      · rcases hval with h | ⟨c, hc, -, h⟩
        · exact ⟨cstar, hcstar, Finset.mem_insert_of_mem (by rw [h]; exact hwstarV)⟩
        · exact ⟨c, hc, Finset.mem_insert.mpr (Or.inl (by rw [h]))⟩
      · exfalso
        apply hp
        show false = decide (α p = wstar ∨ ∃ c ∈ C, c ≠ cstar ∧ α p = u c)
        rw [decide_eq_false hval]
    have hctx : sat3ContextP N C hk α (fun _ => false) ps i
        = sat3ContextP N C hk α bvs ps i :=
      sat3_pinslot_ctx_transfer N C hk α (fun c => insert (u c) (V c)) ps hsign
        (fun _ => false) bvs hbb i hiS
    show (if h : i.val / sat3D N < sat3M N then
        if (⟨i.val / sat3D N, h⟩ : Fin (sat3M N)) ∈ C
        then sat3KitP N (sat3TupleOf N V E'') u ⟨i.val / sat3D N, h⟩ i
        else sat3ContextP N C hk α (fun _ => false) ps i
      else sat3ContextP N C hk α (fun _ => false) ps i)
      = (if h : i.val / sat3D N < sat3M N then
        if (⟨i.val / sat3D N, h⟩ : Fin (sat3M N)) ∈ C
        then sat3KitP N (sat3TupleOf N V E'') u ⟨i.val / sat3D N, h⟩ i
        else sat3ContextP N C hk α bvs ps i
      else sat3ContextP N C hk α bvs ps i)
    by_cases hdiv : i.val / sat3D N < sat3M N
    · rw [dif_pos hdiv, dif_pos hdiv]
      by_cases hmem : (⟨i.val / sat3D N, hdiv⟩ : Fin (sat3M N)) ∈ C
      · rw [if_pos hmem, if_pos hmem]
      · rw [if_neg hmem, if_neg hmem]
        exact hctx
    · rw [dif_neg hdiv, dif_neg hdiv]
      exact hctx

/-! ### The parametric drag -/

set_option maxHeartbeats 1600000 in
/-- **THE PARAMETRIC DRAG (proved)**: `Σ_{c ∈ C} |V c| ≤ j` with the pin channel at ANY slot
`ps` — the pool is gated only by the `ps`-sign column. -/
theorem sat3_pinslot_selector_drag (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (hα : Function.Injective α) (ps : Fin 3)
    (V : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (u : Fin (sat3M N) → Fin (sat3V N))
    (hdata : ∀ c ∈ C, ∀ w ∈ V c,
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)
    (hcov : ∀ c ∈ C, ∀ w ∈ V c, ∃ p : Fin k, α p = w)
    (hucov : ∀ c ∈ C, ∃ p : Fin k, α p = u c)
    (huinj : ∀ c ∈ C, ∀ c' ∈ C, u c = u c' → c = c')
    (hupatV : ∀ c ∈ C, ∀ c' ∈ C, u c ∉ V c')
    (hsign : ∀ p : Fin k, (∃ c ∈ C, α p ∈ insert (u c) (V c)) →
      sat3Bit N (sat3PinClauseM N C hk p) ps (sat3V N) (by omega) ∉ S) :
    ∑ c ∈ C, (V c).card ≤ j := by
  classical
  set D : Finset ((_ : Fin (sat3M N)) × Fin (sat3V N)) :=
    C.sigma (fun c => V c) with hD
  set Y : Finset (Fin N → Bool) := D.powerset.image (sat3RowPS N C hk α ps V u) with hY
  have hYcard : Y.card = 2 ^ D.card := by
    rw [hY, Finset.card_image_of_injOn, Finset.card_powerset]
    intro E hE E' hE' heq
    have hEsub := Finset.mem_powerset.mp (Finset.mem_coe.mp hE)
    have hE'sub := Finset.mem_powerset.mp (Finset.mem_coe.mp hE')
    ext ⟨c, w⟩
    by_cases hq : (⟨c, w⟩ : (_ : Fin (sat3M N)) × Fin (sat3V N)) ∈ D
    · have hcC : c ∈ C := (Finset.mem_sigma.mp hq).1
      have hwV : w ∈ V c := (Finset.mem_sigma.mp hq).2
      have h := congrFun heq
        (sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega))
      rw [sat3RowPS_read N C hk α ps V u E c hcC w,
        sat3RowPS_read N C hk α ps V u E' c hcC w] at h
      constructor
      · intro hq'
        have h1 : w ∈ sat3TupleOf N V E c :=
          (sat3TupleOf_mem N V E c w hwV).mpr hq'
        have h2 : w ∈ sat3TupleOf N V E' c :=
          of_decide_eq_true (by rw [← h]; exact decide_eq_true h1)
        exact (sat3TupleOf_mem N V E' c w hwV).mp h2
      · intro hq'
        have h1 : w ∈ sat3TupleOf N V E' c :=
          (sat3TupleOf_mem N V E' c w hwV).mpr hq'
        have h2 : w ∈ sat3TupleOf N V E c :=
          of_decide_eq_true (by rw [h]; exact decide_eq_true h1)
        exact (sat3TupleOf_mem N V E c w hwV).mp h2
    · constructor
      · intro hq'
        exact absurd (hEsub hq') hq
      · intro hq'
        exact absurd (hE'sub hq') hq
  have hdist : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' →
      ∃ x, sat3Family N (mixOn Sᶜ x y) ≠ sat3Family N (mixOn Sᶜ x y') := by
    intro y hy y' hy' hne
    rw [hY] at hy hy'
    obtain ⟨E, hEmem, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨E', hE'mem, rfl⟩ := Finset.mem_image.mp hy'
    have hEsub := Finset.mem_powerset.mp hEmem
    have hE'sub := Finset.mem_powerset.mp hE'mem
    have hEne : E ≠ E' := fun hcon => hne (by rw [hcon])
    have hex : ∃ q : (_ : Fin (sat3M N)) × Fin (sat3V N),
        q ∈ D ∧ ¬(q ∈ E ↔ q ∈ E') := by
      by_contra hcon
      push_neg at hcon
      apply hEne
      ext q
      by_cases hqD : q ∈ D
      · exact hcon q hqD
      · constructor
        · intro hq
          exact absurd (hEsub hq) hqD
        · intro hq
          exact absurd (hE'sub hq) hqD
    obtain ⟨⟨cstar, wstar⟩, hqD, hqd⟩ := hex
    have hcstar : cstar ∈ C := (Finset.mem_sigma.mp hqD).1
    have hwstarV : wstar ∈ V cstar := (Finset.mem_sigma.mp hqD).2
    obtain ⟨pstar, hpstar⟩ := hcov cstar hcstar wstar hwstarV
    have huw : ∀ c ∈ C, u c ≠ wstar := by
      intro c hc heq
      exact hupatV c hc cstar hcstar (by rw [heq]; exact hwstarV)
    refine ⟨sat3PatchMulti N C
      (sat3ContextP N C hk α (fun p =>
        decide (α p = wstar ∨ ∃ c ∈ C, c ≠ cstar ∧ α p = u c)) ps)
      (sat3KitP N (sat3TupleOf N V E) u), ?_⟩
    rw [sat3_pinslot_mix_transfer N C hk α ps V u hdata hsign
        cstar hcstar wstar hwstarV E E,
      sat3_pinslot_mix_transfer N C hk α ps V u hdata hsign
        cstar hcstar wstar hwstarV E E',
      sat3_pinslot_kit_eval N hv C hk α hα ps (sat3TupleOf N V E) u
        (fun c hc w hw => hcov c hc w (sat3TupleOf_subset N V E c hw))
        hucov huinj
        (fun c hc c' hc' hmem => hupatV c hc c' hc'
          (sat3TupleOf_subset N V E c' hmem))
        cstar hcstar wstar pstar hpstar huw,
      sat3_pinslot_kit_eval N hv C hk α hα ps (sat3TupleOf N V E') u
        (fun c hc w hw => hcov c hc w (sat3TupleOf_subset N V E' c hw))
        hucov huinj
        (fun c hc c' hc' hmem => hupatV c hc c' hc'
          (sat3TupleOf_subset N V E' c' hmem))
        cstar hcstar wstar pstar hpstar huw]
    intro heq
    apply hqd
    constructor
    · intro hq
      have h1 : wstar ∈ sat3TupleOf N V E cstar :=
        (sat3TupleOf_mem N V E cstar wstar hwstarV).mpr hq
      have h2 : wstar ∈ sat3TupleOf N V E' cstar :=
        of_decide_eq_true (by rw [← heq]; exact decide_eq_true h1)
      exact (sat3TupleOf_mem N V E' cstar wstar hwstarV).mp h2
    · intro hq
      have h1 : wstar ∈ sat3TupleOf N V E' cstar :=
        (sat3TupleOf_mem N V E' cstar wstar hwstarV).mpr hq
      have h2 : wstar ∈ sat3TupleOf N V E cstar :=
        of_decide_eq_true (by rw [heq]; exact decide_eq_true h1)
      exact (sat3TupleOf_mem N V E cstar wstar hwstarV).mp h2
  have hcap := cut_row_capacity (sat3Family N) S j hcut Y hdist
  rw [hYcard] at hcap
  have hDcard : D.card = ∑ c ∈ C, (V c).card := by
    rw [hD]
    exact Finset.card_sigma _ _
  by_contra hcon
  push_neg at hcon
  have hlt : (2 : ℕ) ^ j < 2 ^ D.card :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  omega

/-! ### The parametric window -/

/-- The pin census at slot `ps` transfers from pin indices to pool blocks. -/
theorem sat3_pinslot_pin_sign_count (N : ℕ) (C : Finset (Fin (sat3M N)))
    (ps : Fin 3) (S : Finset (Fin N)) :
    ((Finset.univ : Finset (Fin ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).card))).filter
      (fun p => sat3Bit N (sat3PinClauseM N C (le_refl _) p) ps (sat3V N)
        (by omega) ∈ S)).card
    = ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).filter (fun b =>
        sat3Bit N b ps (sat3V N) (by omega) ∈ S)).card := by
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

set_option maxHeartbeats 3200000 in
/-- **THE PARAMETRIC WINDOW (proved)**: cardinality room alone prices `Σ_{c ∈ C} |V c| ≤ j`,
with the pool gated only by the sign column of the CHOSEN pin slot. -/
theorem sat3_pinslot_window (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (C : Finset (Fin (sat3M N))) (ps : Fin 3)
    (V : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (hdata : ∀ c ∈ C, ∀ w ∈ V c,
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)
    (hkv : sat3M N - C.card ≤ sat3V N)
    (hspace : (C.biUnion V).card + C.card ≤ sat3V N)
    (hroom : (C.biUnion V).card + C.card
      + ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).filter (fun b =>
          sat3Bit N b ps (sat3V N) (by omega) ∈ S)).card
      ≤ sat3M N - C.card) :
    ∑ c ∈ C, (V c).card ≤ j := by
  classical
  have hpool : (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card = sat3M N - C.card :=
    sat3_pin_pool_card N C
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
  set W₀ : Finset (Fin (sat3V N)) := (C.biUnion V) ∪ U' with hW₀
  have hdisj : Disjoint (C.biUnion V) U' := by
    apply Finset.disjoint_left.mpr
    intro a ha ha'
    exact (Finset.mem_sdiff.mp (hU'sub ha')).2 ha
  have hW₀card : W₀.card = (C.biUnion V).card + C.card := by
    rw [hW₀, Finset.card_union_of_disjoint hdisj, hU'card]
  have hcover : (Finset.univ :
        Finset (Fin ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)))
      ⊆ ((Finset.univ :
          Finset (Fin ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).card))).filter
          (fun p => sat3Bit N (sat3PinClauseM N C (le_refl _) p) ps
            (sat3V N) (by omega) ∈ S))
        ∪ ((Finset.univ :
          Finset (Fin ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).card))).filter
          (fun p => sat3Bit N (sat3PinClauseM N C (le_refl _) p) ps
            (sat3V N) (by omega) ∉ S)) := by
    intro p _
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases hp : sat3Bit N (sat3PinClauseM N C (le_refl _) p) ps
        (sat3V N) (by omega) ∈ S
    · exact Or.inl ⟨Finset.mem_univ p, hp⟩
    · exact Or.inr ⟨Finset.mem_univ p, hp⟩
  have hcnt : (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card
      ≤ ((Finset.univ :
          Finset (Fin ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).card))).filter
          (fun p => sat3Bit N (sat3PinClauseM N C (le_refl _) p) ps
            (sat3V N) (by omega) ∈ S)).card
        + ((Finset.univ :
          Finset (Fin ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).card))).filter
          (fun p => sat3Bit N (sat3PinClauseM N C (le_refl _) p) ps
            (sat3V N) (by omega) ∉ S)).card := by
    calc (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card
        = (Finset.univ :
            Finset (Fin ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).card))).card := by
          rw [Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := Finset.card_le_card hcover
      _ ≤ _ := Finset.card_union_le _ _
  have hQ := sat3_pinslot_pin_sign_count N C ps S
  have hoff : W₀.card
      ≤ ((Finset.univ :
          Finset (Fin ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).card))).filter
          (fun p => sat3Bit N (sat3PinClauseM N C (le_refl _) p) ps
            (sat3V N) (by omega) ∉ S)).card := by
    omega
  obtain ⟨P', hP'sub, hP'card⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ :
      Finset (Fin ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).card))).filter
      (fun p => sat3Bit N (sat3PinClauseM N C (le_refl _) p) ps
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
  exact sat3_pinslot_selector_drag N hv hcut C (le_refl _) α hαinj ps V u hdata
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

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_pinslot_ctx_transfer
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_pinslot_mix_transfer
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_pinslot_selector_drag
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_pinslot_window
