import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMultiBlockEval

/-!
# N-Frame: the additive drag — per-block capacities add up across the cut

Rung 4 of the multi-block arc (patch → context → eval → **drag** → window).  The single-block
`sat3_selector_data_drag` prices ONE block's selector data against the trace: `|V₀| ≤ j`.  This
file makes the capacities ADD: with data blocks `C` and per-block selector sets `V c` inside `S`,
the row family is indexed by the FULL tuple `(T c)_{c ∈ C}` of sub-patterns — `2^{Σ_c |V c|}`
rows — and rung 3's kit eval reads any two tuples apart at a differing coordinate `(c*, w*)`.

Side convention (`S` = data side, `Sᶜ` = query/control side):
  • slot-0 data selectors of every `V c` lie IN `S` (`hdata`) — the stored patterns;
  • covering pin signs lie OFF `S` (`hsign`) — the reading modes;
  • slot-1 kit selectors at pattern positions lie OFF `S` (`hkit1`) — the neutralizers.

Staged:
  `sat3TupleOf` — sub-pattern tuples from subsets of the sigma-set `C.sigma V`,
        with `_subset` / `_mem`.
  `sat3SelPatM` / `sat3RowM` / `sat3RowM_read` — the row family: block `c` carries the slot-0
        indicator of `T c`; the point read identifies the tuple.
  `sat3_multi_ctx_transfer` — pin contexts agree on `S` when the differing pins cover pattern
        variables (their sign bits are off `S`).
  `sat3_multi_mix_transfer` — **the mix**: overlaying the reading mode `(c*, w*)` from `Sᶜ` onto
        a stored row produces exactly the rung-3 kit instance for that row's tuple.
  `sat3_multi_selector_data_drag` — **PROVED, the additive drag**:
        over any cut factorization, `Σ_{c ∈ C} |V c| ≤ j`.

This is what the multi-block arc was for: the single-block drag compares each block separately to
the same trace (`max_c |V c| ≤ j`); the additive drag charges the trace for ALL blocks at once
(`Σ_c |V c| ≤ j`) — the step toward upgrading `coneExcess = Ω(m)` to `Ω(N)`.

## Honest scope

The drag prices data against an ABSTRACT cut factorization.  Remaining rungs: the rebuilt window
(`m·j → j`, producing the factorization from a circuit cut) and the balance census assembling
`coneExcess = Ω(N)` / a `(2+c)·N` cbudget bound in the restricted model.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Stage A: sub-pattern tuples from subsets of the sigma-set -/

/-- The sub-pattern tuple encoded by a subset `E` of the sigma-set `C.sigma V`: block `c`'s
pattern is `{w ∈ V c | ⟨c, w⟩ ∈ E}`. -/
def sat3TupleOf (N : ℕ) (V : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (E : Finset ((_ : Fin (sat3M N)) × Fin (sat3V N))) :
    Fin (sat3M N) → Finset (Fin (sat3V N)) :=
  fun c => (V c).filter
    (fun w => (⟨c, w⟩ : (_ : Fin (sat3M N)) × Fin (sat3V N)) ∈ E)

theorem sat3TupleOf_subset (N : ℕ) (V : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (E : Finset ((_ : Fin (sat3M N)) × Fin (sat3V N))) (c : Fin (sat3M N)) :
    sat3TupleOf N V E c ⊆ V c :=
  Finset.filter_subset _ _

theorem sat3TupleOf_mem (N : ℕ) (V : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (E : Finset ((_ : Fin (sat3M N)) × Fin (sat3V N))) (c : Fin (sat3M N))
    (w : Fin (sat3V N)) (hw : w ∈ V c) :
    w ∈ sat3TupleOf N V E c
      ↔ (⟨c, w⟩ : (_ : Fin (sat3M N)) × Fin (sat3V N)) ∈ E := by
  unfold sat3TupleOf
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hw, h⟩⟩

/-! ### Stage B: the row family and its point read -/

/-- The pattern-only block contents: block `c` carries the slot-0 indicator of `T c` (no kit —
rows are reading-mode-independent; the kit arrives with the probe). -/
def sat3SelPatM (N : ℕ) (T : Fin (sat3M N) → Finset (Fin (sat3V N))) :
    Fin (sat3M N) → Fin N → Bool :=
  fun c => fun bit => decide (∃ w ∈ T c, bit.val % sat3D N = w.val)

/-- The row encoding tuple `E`: all-false pin signs, patterns `sat3TupleOf V E` in the data
blocks. -/
noncomputable def sat3RowM (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (V : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (E : Finset ((_ : Fin (sat3M N)) × Fin (sat3V N))) : Fin N → Bool :=
  sat3PatchMulti N C (sat3ContextM N C hk α (fun _ => false))
    (sat3SelPatM N (sat3TupleOf N V E))

/-- The point read: the slot-0 selector bit of `(c, w)` recovers the tuple membership. -/
theorem sat3RowM_read (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (V : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (E : Finset ((_ : Fin (sat3M N)) × Fin (sat3V N)))
    (c : Fin (sat3M N)) (hcC : c ∈ C) (w : Fin (sat3V N)) :
    sat3RowM N C hk α V E
      (sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega))
      = decide (w ∈ sat3TupleOf N V E c) := by
  unfold sat3RowM
  rw [sat3PatchMulti_own N C (sat3ContextM N C hk α (fun _ => false))
    (sat3SelPatM N (sat3TupleOf N V E)) c hcC]
  have hr : (sat3Bit N c ⟨0, by omega⟩ w.val
      (by have := w.isLt; omega)).val % sat3D N = w.val := by
    rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + w.val = w.val
    omega
  show decide _ = decide (w ∈ sat3TupleOf N V E c)
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨w', hw', hrem⟩
    rw [hr] at hrem
    rw [show w = w' from Fin.ext hrem]
    exact hw'
  · intro hw
    exact ⟨w, hw, hr⟩

/-! ### Stage C: the context transfer on `S` -/

/-- Pin contexts agree on `S` when every differing pin covers a pattern variable — those pins'
sign bits lie off `S` by `hsign`. -/
theorem sat3_multi_ctx_transfer (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (V : Fin (sat3M N) → Finset (Fin (sat3V N)))
    {S : Finset (Fin N)}
    (hsign : ∀ p : Fin k, (∃ c ∈ C, α p ∈ V c) →
      sat3Bit N (sat3PinClauseM N C hk p) ⟨0, by omega⟩ (sat3V N) (by omega) ∉ S)
    (b b' : Fin k → Bool)
    (hbb : ∀ p : Fin k, b p ≠ b' p → (∃ c ∈ C, α p ∈ V c))
    (i : Fin N) (hi : i ∈ S) :
    sat3ContextM N C hk α b i = sat3ContextM N C hk α b' i := by
  apply sat3ContextM_agree
  intro p hp1 hp2
  by_contra hbne
  apply hsign p (hbb p hbne)
  have hiπ : sat3Bit N (sat3PinClauseM N C hk p) ⟨0, by omega⟩ (sat3V N)
      (by omega) = i := by
    apply Fin.ext
    show (sat3PinClauseM N C hk p).val * sat3D N + 0 * (sat3V N + 1) + sat3V N
      = i.val
    have hdm := Nat.div_add_mod i.val (sat3D N)
    rw [hp1, hp2] at hdm
    have hcm : sat3D N * (sat3PinClauseM N C hk p).val
        = (sat3PinClauseM N C hk p).val * sat3D N := Nat.mul_comm _ _
    omega
  rw [hiπ]
  exact hi

/-! ### Stage D: the mix transfer -/

set_option maxHeartbeats 1600000 in
/-- **THE MIX TRANSFER (proved)**: overlaying the reading-mode probe (pins forcing `a w* = true`,
kit for mode `(c*, w*)` with the probe's own tuple `E`) from `Sᶜ` onto the stored row of tuple
`E''` produces exactly the rung-3 kit instance for `E''` — the stored data survives on `S`, the
reading mode arrives from `Sᶜ`. -/
theorem sat3_multi_mix_transfer (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (V : Fin (sat3M N) → Finset (Fin (sat3V N)))
    {S : Finset (Fin N)}
    (hdata : ∀ c ∈ C, ∀ w ∈ V c,
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)
    (hsign : ∀ p : Fin k, (∃ c ∈ C, α p ∈ V c) →
      sat3Bit N (sat3PinClauseM N C hk p) ⟨0, by omega⟩ (sat3V N) (by omega) ∉ S)
    (hkit1 : ∀ c ∈ C, ∀ c' ∈ C, ∀ w ∈ V c',
      sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)
    (cstar : Fin (sat3M N)) (hcstar : cstar ∈ C)
    (wstar : Fin (sat3V N)) (hwstar : wstar ∈ V cstar)
    (E E'' : Finset ((_ : Fin (sat3M N)) × Fin (sat3V N))) :
    mixOn Sᶜ
      (sat3PatchMulti N C (sat3ContextM N C hk α (fun p => decide (α p = wstar)))
        (sat3KitM N (sat3TupleOf N V E) cstar wstar))
      (sat3RowM N C hk α V E'')
      = sat3PatchMulti N C (sat3ContextM N C hk α (fun p => decide (α p = wstar)))
        (sat3KitM N (sat3TupleOf N V E'') cstar wstar) := by
  classical
  set bvs : Fin k → Bool := fun p => decide (α p = wstar) with hbvs
  funext i
  show (if i ∈ Sᶜ
      then sat3PatchMulti N C (sat3ContextM N C hk α bvs)
        (sat3KitM N (sat3TupleOf N V E) cstar wstar) i
      else sat3RowM N C hk α V E'' i)
    = sat3PatchMulti N C (sat3ContextM N C hk α bvs)
        (sat3KitM N (sat3TupleOf N V E'') cstar wstar) i
  by_cases hi : i ∈ Sᶜ
  · -- probe side: the kits differ only at slot-0 pattern selectors, which lie in `S`
    rw [if_pos hi]
    have hiNS : i ∉ S := Finset.mem_compl.mp hi
    show (if h : i.val / sat3D N < sat3M N then
        if (⟨i.val / sat3D N, h⟩ : Fin (sat3M N)) ∈ C
        then sat3KitM N (sat3TupleOf N V E) cstar wstar ⟨i.val / sat3D N, h⟩ i
        else sat3ContextM N C hk α bvs i
      else sat3ContextM N C hk α bvs i)
      = (if h : i.val / sat3D N < sat3M N then
        if (⟨i.val / sat3D N, h⟩ : Fin (sat3M N)) ∈ C
        then sat3KitM N (sat3TupleOf N V E'') cstar wstar ⟨i.val / sat3D N, h⟩ i
        else sat3ContextM N C hk α bvs i
      else sat3ContextM N C hk α bvs i)
    by_cases hdiv : i.val / sat3D N < sat3M N
    · rw [dif_pos hdiv, dif_pos hdiv]
      by_cases hmem : (⟨i.val / sat3D N, hdiv⟩ : Fin (sat3M N)) ∈ C
      · rw [if_pos hmem, if_pos hmem]
        show decide _ = decide _
        apply decide_eq_decide.mpr
        constructor
        · rintro (⟨w, hw, hrem⟩ | hkitb)
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
          · exact Or.inr hkitb
        · rintro (⟨w, hw, hrem⟩ | hkitb)
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
          · exact Or.inr hkitb
      · rw [if_neg hmem, if_neg hmem]
    · rw [dif_neg hdiv, dif_neg hdiv]
  · -- data side: the row's pattern is the kit's slot-0 part; the kit bit lies off `S`;
    -- the contexts agree on `S`
    rw [if_neg hi]
    have hiS : i ∈ S := by
      by_contra hiS
      exact hi (Finset.mem_compl.mpr hiS)
    have hbb : ∀ p : Fin k, (fun _ : Fin k => false) p ≠ bvs p →
        (∃ c ∈ C, α p ∈ V c) := by
      intro p hp
      by_cases hαp : α p = wstar
      · exact ⟨cstar, hcstar, by rw [hαp]; exact hwstar⟩
      · exfalso
        apply hp
        show false = decide (α p = wstar)
        rw [decide_eq_false hαp]
    have hctx : sat3ContextM N C hk α (fun _ => false) i
        = sat3ContextM N C hk α bvs i :=
      sat3_multi_ctx_transfer N C hk α V hsign (fun _ => false) bvs hbb i hiS
    show (if h : i.val / sat3D N < sat3M N then
        if (⟨i.val / sat3D N, h⟩ : Fin (sat3M N)) ∈ C
        then sat3SelPatM N (sat3TupleOf N V E'') ⟨i.val / sat3D N, h⟩ i
        else sat3ContextM N C hk α (fun _ => false) i
      else sat3ContextM N C hk α (fun _ => false) i)
      = (if h : i.val / sat3D N < sat3M N then
        if (⟨i.val / sat3D N, h⟩ : Fin (sat3M N)) ∈ C
        then sat3KitM N (sat3TupleOf N V E'') cstar wstar ⟨i.val / sat3D N, h⟩ i
        else sat3ContextM N C hk α bvs i
      else sat3ContextM N C hk α bvs i)
    by_cases hdiv : i.val / sat3D N < sat3M N
    · rw [dif_pos hdiv, dif_pos hdiv]
      by_cases hmem : (⟨i.val / sat3D N, hdiv⟩ : Fin (sat3M N)) ∈ C
      · rw [if_pos hmem, if_pos hmem]
        show decide _ = decide _
        apply decide_eq_decide.mpr
        constructor
        · intro hsel
          exact Or.inl hsel
        · rintro (hsel | ⟨-, hrem⟩)
          · exact hsel
          · exfalso
            apply hkit1 ⟨i.val / sat3D N, hdiv⟩ hmem cstar hcstar wstar hwstar
            have hiw : sat3Bit N ⟨i.val / sat3D N, hdiv⟩ ⟨1, by omega⟩ wstar.val
                (by have := wstar.isLt; omega) = i := by
              apply Fin.ext
              show i.val / sat3D N * sat3D N + 1 * (sat3V N + 1) + wstar.val
                = i.val
              have hdm := Nat.div_add_mod i.val (sat3D N)
              rw [hrem] at hdm
              have hcm : sat3D N * (i.val / sat3D N)
                  = i.val / sat3D N * sat3D N := Nat.mul_comm _ _
              omega
            rw [hiw]
            exact hiS
      · rw [if_neg hmem, if_neg hmem]
        exact hctx
    · rw [dif_neg hdiv, dif_neg hdiv]
      exact hctx

/-! ### Stage E: the additive drag -/

set_option maxHeartbeats 1600000 in
/-- **THE ADDITIVE DRAG (proved)**: per-block selector data inside `S`, covering pin signs and
slot-1 kit positions outside `S` — the per-block capacities ADD against the trace:
`Σ_{c ∈ C} |V c| ≤ j`. -/
theorem sat3_multi_selector_data_drag (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (hα : Function.Injective α)
    (V : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (hdata : ∀ c ∈ C, ∀ w ∈ V c,
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)
    (hcov : ∀ c ∈ C, ∀ w ∈ V c, ∃ p : Fin k, α p = w)
    (hsign : ∀ p : Fin k, (∃ c ∈ C, α p ∈ V c) →
      sat3Bit N (sat3PinClauseM N C hk p) ⟨0, by omega⟩ (sat3V N) (by omega) ∉ S)
    (hkit1 : ∀ c ∈ C, ∀ c' ∈ C, ∀ w ∈ V c',
      sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S) :
    ∑ c ∈ C, (V c).card ≤ j := by
  classical
  set D : Finset ((_ : Fin (sat3M N)) × Fin (sat3V N)) :=
    C.sigma (fun c => V c) with hD
  set Y : Finset (Fin N → Bool) := D.powerset.image (sat3RowM N C hk α V) with hY
  -- the row count: one row per subset of the sigma-set
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
      rw [sat3RowM_read N C hk α V E c hcC w,
        sat3RowM_read N C hk α V E' c hcC w] at h
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
  -- pairwise distinguishability over `Sᶜ`: read the tuples apart at a differing `(c*, w*)`
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
    have hwstar : wstar ∈ V cstar := (Finset.mem_sigma.mp hqD).2
    obtain ⟨pstar, hpstar⟩ := hcov cstar hcstar wstar hwstar
    refine ⟨sat3PatchMulti N C
      (sat3ContextM N C hk α (fun p => decide (α p = wstar)))
      (sat3KitM N (sat3TupleOf N V E) cstar wstar), ?_⟩
    rw [sat3_multi_mix_transfer N C hk α V hdata hsign hkit1
        cstar hcstar wstar hwstar E E,
      sat3_multi_mix_transfer N C hk α V hdata hsign hkit1
        cstar hcstar wstar hwstar E E',
      sat3_multi_kit_eval N hv C hk α hα (sat3TupleOf N V E)
        (fun c hc w hw => hcov c hc w (sat3TupleOf_subset N V E c hw))
        cstar hcstar wstar pstar hpstar,
      sat3_multi_kit_eval N hv C hk α hα (sat3TupleOf N V E')
        (fun c hc w hw => hcov c hc w (sat3TupleOf_subset N V E' c hw))
        cstar hcstar wstar pstar hpstar]
    intro heq
    apply hqd
    constructor
    · intro hq
      have h1 : wstar ∈ sat3TupleOf N V E cstar :=
        (sat3TupleOf_mem N V E cstar wstar hwstar).mpr hq
      have h2 : wstar ∈ sat3TupleOf N V E' cstar :=
        of_decide_eq_true (by rw [← heq]; exact decide_eq_true h1)
      exact (sat3TupleOf_mem N V E' cstar wstar hwstar).mp h2
    · intro hq
      have h1 : wstar ∈ sat3TupleOf N V E' cstar :=
        (sat3TupleOf_mem N V E' cstar wstar hwstar).mpr hq
      have h2 : wstar ∈ sat3TupleOf N V E cstar :=
        of_decide_eq_true (by rw [heq]; exact decide_eq_true h1)
      exact (sat3TupleOf_mem N V E cstar wstar hwstar).mp h2
  -- the capacity cap
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

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_mix_transfer
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_selector_data_drag
