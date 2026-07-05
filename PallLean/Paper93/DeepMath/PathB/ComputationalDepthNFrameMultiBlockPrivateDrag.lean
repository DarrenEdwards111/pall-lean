import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMultiBlockPrivateKit

/-!
# N-Frame: the private-kit drag — the additive drag with no slot-1 conditions

Rung 14 of the multi-block arc (… → private kit → **private drag**).  The rung-4 drag needed
its kit positions outside `S` (`hkit1`) because the kit was mode-dependent; the private kit is
constant across modes, so THE ROWS CARRY IT.  Rows and probe targets now share the identical
data-block content `sat3KitP (tupleOf E) u`, and the delicate S-side case of the mix transfer
becomes trivial: on `S`, row and target agree bit-for-bit inside every data block.  The slot-1
cleanliness hypothesis disappears from the drag:

  `sat3RowP` / `sat3RowP_read` — the row family: block `c` carries the slot-0 pattern of the
        tuple AND the constant kit `{u c}`; the point read still recovers the tuple.
  `sat3_private_mix_transfer` — **PROVED, the mix**: overlaying the mode probe from `Sᶜ` onto a
        stored row produces the private-kit eval instance — requiring only `hdata` (pattern
        bits in `S`) and `hsign` (covering-pin sign bits off `S`, now including the private
        pins).  NO condition on slot 1 anywhere in the data blocks.
  `sat3_private_selector_drag` — **PROVED, the drag**: `Σ_{c ∈ C} |V c| ≤ j` — the rung-4
        conclusion with the `hkit1` hypothesis GONE, at the cost of pins for the `|C|` privates
        (`hucov`) and private-position bookkeeping (`huinj`, `hupatV`).

Against rung 12: the stacked-pair shelter attacked exactly the `hkit1` hypothesis; the private
drag has no such hypothesis, so stacking no longer shelters payload from THIS drag.  The
rebuilt window/census chain on top of it — where the rung-12 stack terms should fall away — is
the next rung.

## Honest scope

The drag prices data against an ABSTRACT cut factorization; the rebuilt windows, censuses, and
the band arithmetic toward `coneExcess = Ω(T)` / a `(2+c)·N` cbudget bound are NOT rebuilt here.
The new pin bill (patterns + privates) tightens the room bookkeeping to
`|⋃V| + |C| + Q ≤ m − |C|`-scale and must be paid in those rungs.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The row family -/

/-- The private-kit row for tuple `E`: all-false pins, block `c` carrying the tuple's slot-0
pattern AND the constant kit `{u c}`. -/
noncomputable def sat3RowP (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (V : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (u : Fin (sat3M N) → Fin (sat3V N))
    (E : Finset ((_ : Fin (sat3M N)) × Fin (sat3V N))) : Fin N → Bool :=
  sat3PatchMulti N C (sat3ContextM N C hk α (fun _ => false))
    (sat3KitP N (sat3TupleOf N V E) u)

/-- The point read: the slot-0 selector bit of `(c, w)` recovers the tuple membership — the
constant kit lives at slot 1 and does not disturb it. -/
theorem sat3RowP_read (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (V : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (u : Fin (sat3M N) → Fin (sat3V N))
    (E : Finset ((_ : Fin (sat3M N)) × Fin (sat3V N)))
    (c : Fin (sat3M N)) (hcC : c ∈ C) (w : Fin (sat3V N)) :
    sat3RowP N C hk α V u E
      (sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega))
      = decide (w ∈ sat3TupleOf N V E c) := by
  unfold sat3RowP
  rw [sat3PatchMulti_own N C (sat3ContextM N C hk α (fun _ => false))
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
/-- **THE PRIVATE MIX TRANSFER (proved)**: overlaying the mode probe (pins forcing `w*` and the
foreign privates true, `u_{c*}` false; the probe's own tuple `E`) from `Sᶜ` onto the stored row
of tuple `E''` produces exactly the private-kit eval instance for `E''`.  Data blocks agree on
`S` bit-for-bit (row and target carry the SAME content); only pattern bits must lie in `S` and
covering-pin signs off `S` — no slot-1 condition. -/
theorem sat3_private_mix_transfer (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (V : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (u : Fin (sat3M N) → Fin (sat3V N))
    {S : Finset (Fin N)}
    (hdata : ∀ c ∈ C, ∀ w ∈ V c,
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)
    (hsign : ∀ p : Fin k, (∃ c ∈ C, α p ∈ insert (u c) (V c)) →
      sat3Bit N (sat3PinClauseM N C hk p) ⟨0, by omega⟩ (sat3V N) (by omega) ∉ S)
    (cstar : Fin (sat3M N)) (hcstar : cstar ∈ C)
    (wstar : Fin (sat3V N)) (hwstarV : wstar ∈ V cstar)
    (E E'' : Finset ((_ : Fin (sat3M N)) × Fin (sat3V N))) :
    mixOn Sᶜ
      (sat3PatchMulti N C (sat3ContextM N C hk α (fun p =>
        decide (α p = wstar ∨ ∃ c ∈ C, c ≠ cstar ∧ α p = u c)))
        (sat3KitP N (sat3TupleOf N V E) u))
      (sat3RowP N C hk α V u E'')
      = sat3PatchMulti N C (sat3ContextM N C hk α (fun p =>
        decide (α p = wstar ∨ ∃ c ∈ C, c ≠ cstar ∧ α p = u c)))
        (sat3KitP N (sat3TupleOf N V E'') u) := by
  classical
  set bvs : Fin k → Bool := fun p =>
    decide (α p = wstar ∨ ∃ c ∈ C, c ≠ cstar ∧ α p = u c) with hbvs
  funext i
  show (if i ∈ Sᶜ
      then sat3PatchMulti N C (sat3ContextM N C hk α bvs)
        (sat3KitP N (sat3TupleOf N V E) u) i
      else sat3RowP N C hk α V u E'' i)
    = sat3PatchMulti N C (sat3ContextM N C hk α bvs)
        (sat3KitP N (sat3TupleOf N V E'') u) i
  by_cases hi : i ∈ Sᶜ
  · -- probe side: the kits differ only at slot-0 pattern selectors, which lie in `S`
    rw [if_pos hi]
    have hiNS : i ∉ S := Finset.mem_compl.mp hi
    show (if h : i.val / sat3D N < sat3M N then
        if (⟨i.val / sat3D N, h⟩ : Fin (sat3M N)) ∈ C
        then sat3KitP N (sat3TupleOf N V E) u ⟨i.val / sat3D N, h⟩ i
        else sat3ContextM N C hk α bvs i
      else sat3ContextM N C hk α bvs i)
      = (if h : i.val / sat3D N < sat3M N then
        if (⟨i.val / sat3D N, h⟩ : Fin (sat3M N)) ∈ C
        then sat3KitP N (sat3TupleOf N V E'') u ⟨i.val / sat3D N, h⟩ i
        else sat3ContextM N C hk α bvs i
      else sat3ContextM N C hk α bvs i)
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
  · -- row side: data blocks carry the SAME content; the contexts agree on `S`
    rw [if_neg hi]
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
    have hctx : sat3ContextM N C hk α (fun _ => false) i
        = sat3ContextM N C hk α bvs i :=
      sat3_multi_ctx_transfer N C hk α (fun c => insert (u c) (V c)) hsign
        (fun _ => false) bvs hbb i hiS
    show (if h : i.val / sat3D N < sat3M N then
        if (⟨i.val / sat3D N, h⟩ : Fin (sat3M N)) ∈ C
        then sat3KitP N (sat3TupleOf N V E'') u ⟨i.val / sat3D N, h⟩ i
        else sat3ContextM N C hk α (fun _ => false) i
      else sat3ContextM N C hk α (fun _ => false) i)
      = (if h : i.val / sat3D N < sat3M N then
        if (⟨i.val / sat3D N, h⟩ : Fin (sat3M N)) ∈ C
        then sat3KitP N (sat3TupleOf N V E'') u ⟨i.val / sat3D N, h⟩ i
        else sat3ContextM N C hk α bvs i
      else sat3ContextM N C hk α bvs i)
    by_cases hdiv : i.val / sat3D N < sat3M N
    · rw [dif_pos hdiv, dif_pos hdiv]
      by_cases hmem : (⟨i.val / sat3D N, hdiv⟩ : Fin (sat3M N)) ∈ C
      · rw [if_pos hmem, if_pos hmem]
      · rw [if_neg hmem, if_neg hmem]
        exact hctx
    · rw [dif_neg hdiv, dif_neg hdiv]
      exact hctx

/-! ### The drag -/

set_option maxHeartbeats 1600000 in
/-- **THE PRIVATE-KIT DRAG (proved)**: per-block selector capacities ADD against the trace —
`Σ_{c ∈ C} |V c| ≤ j` — with NO slot-1 condition.  The rung-12 stacked-pair shelter attacked
exactly the hypothesis this drag no longer has.  Cost: pins must also cover the `|C|` privates,
which must be injective, outside every pattern set, and their covering-pin signs off `S`. -/
theorem sat3_private_selector_drag (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (hα : Function.Injective α)
    (V : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (u : Fin (sat3M N) → Fin (sat3V N))
    (hdata : ∀ c ∈ C, ∀ w ∈ V c,
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)
    (hcov : ∀ c ∈ C, ∀ w ∈ V c, ∃ p : Fin k, α p = w)
    (hucov : ∀ c ∈ C, ∃ p : Fin k, α p = u c)
    (huinj : ∀ c ∈ C, ∀ c' ∈ C, u c = u c' → c = c')
    (hupatV : ∀ c ∈ C, ∀ c' ∈ C, u c ∉ V c')
    (hsign : ∀ p : Fin k, (∃ c ∈ C, α p ∈ insert (u c) (V c)) →
      sat3Bit N (sat3PinClauseM N C hk p) ⟨0, by omega⟩ (sat3V N) (by omega) ∉ S) :
    ∑ c ∈ C, (V c).card ≤ j := by
  classical
  set D : Finset ((_ : Fin (sat3M N)) × Fin (sat3V N)) :=
    C.sigma (fun c => V c) with hD
  set Y : Finset (Fin N → Bool) := D.powerset.image (sat3RowP N C hk α V u) with hY
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
      rw [sat3RowP_read N C hk α V u E c hcC w,
        sat3RowP_read N C hk α V u E' c hcC w] at h
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
      (sat3ContextM N C hk α (fun p =>
        decide (α p = wstar ∨ ∃ c ∈ C, c ≠ cstar ∧ α p = u c)))
      (sat3KitP N (sat3TupleOf N V E) u), ?_⟩
    rw [sat3_private_mix_transfer N C hk α V u hdata hsign
        cstar hcstar wstar hwstarV E E,
      sat3_private_mix_transfer N C hk α V u hdata hsign
        cstar hcstar wstar hwstarV E E',
      sat3_private_kit_eval N hv C hk α hα (sat3TupleOf N V E) u
        (fun c hc w hw => hcov c hc w (sat3TupleOf_subset N V E c hw))
        hucov huinj
        (fun c hc c' hc' hmem => hupatV c hc c' hc'
          (sat3TupleOf_subset N V E c' hmem))
        cstar hcstar wstar pstar hpstar huw,
      sat3_private_kit_eval N hv C hk α hα (sat3TupleOf N V E') u
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

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3RowP_read
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_private_mix_transfer
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_private_selector_drag
