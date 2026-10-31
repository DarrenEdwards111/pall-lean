import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMultiBlockStraddle

/-!
# N-Frame: pin-slot-parametric pins — the foundation for the three-slot pin war

Rung 19 of the multi-block arc (… → straddle → **pin-slot pins**).  Rung 18's alignment law
forces low-excess heavy cuts nearly block-aligned; aligned-in blocks feed the private window
free of charge; the pool side is gated ONLY by pin sign bits (the drag never needed pool
SELECTOR bits off `S` — constant bits ride with the rows; the pin's mode-dependent bit is its
sign).  A heavy `S` can poison the slot-0 sign column, but rung 17's squeeze prices keeping ALL
THREE sign columns poisoned at all-slots-nearly-full (`|S| ≥ 3·m·(v−j)`-scale) — so pins that
can live at ANY slot win the war.  The slot swap cannot decouple pin slot from data slot (it
moves both), so this file rebuilds the pin machinery with the pin slot as a PARAMETER:

  `slotField_eq` — slot/field decomposition is injective (the collision workhorse).
  `sat3ContextP` — the multi-block pin context with pin literals at slot `ps`: pin `p` forces
        `a (α p) = bvec p` through a single slot-`ps` literal; tautology and designated blocks
        exactly as in `sat3ContextM` (which is the `ps = 0` instance in content).
  `sat3ContextP_pin_sel/_pin_miss/_pin_dead/_pin_sign` and the six tautology reads — the full
        read kit at any pin slot.
  `sat3Clause_single_slot_iff` — the single-live-literal clause analysis at ANY slot.
  `sat3_pinslot_pin_clause_iff` / `sat3_pinslot_taut_clause_sat` — the clause layer through the
        multi-patch, for ARBITRARY data contents `us`.
  `sat3_pinslot_kit_eval` — **PROVED, the workhorse**: the private-kit eval with pins at any
        slot `ps`: `sat3Family (patchMulti C (contextP bvec ps, sat3KitP)) = decide (w* ∈ T c*)`
        — the data-block layer (`sat3_private_data_clause_iff`) is reused unchanged.

## Honest scope

This is the eval foundation.  The parametric drag/mix-transfer, the windows and censuses at
pin slot `ps`, and the three-slot assembly (`∃ ps, Q_{ps} ≤ j + 2` from the squeeze ⇒ a live
pin slot at every band below all-slots-full) are the next rung; only then does the heavy-band
`coneExcess = Ω(N)` / `(2+c)·N` arithmetic get its final test.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The parametric context -/

/-- The pin-slot-parametric multi-block context: pin `p` forces `a (α p) = bvec p` through a
single slot-`ps` literal of its block; blocks outside `C ∪ pins` are tautologies; blocks of `C`
are left empty. -/
noncomputable def sat3ContextP (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (bvec : Fin k → Bool) (ps : Fin 3) : Fin N → Bool :=
  fun bit => decide (
    (∃ p : Fin k, bit.val / sat3D N = (sat3PinClauseM N C hk p).val ∧
      (bit.val % sat3D N = ps.val * (sat3V N + 1) + (α p).val ∨
        (bit.val % sat3D N = ps.val * (sat3V N + 1) + sat3V N ∧ bvec p = false)))
    ∨ (bit.val / sat3D N < sat3M N ∧
      (∀ c ∈ C, bit.val / sat3D N ≠ c.val) ∧
      (∀ p : Fin k, bit.val / sat3D N ≠ (sat3PinClauseM N C hk p).val) ∧
      (bit.val % sat3D N = 0 ∨ bit.val % sat3D N = sat3V N + 1 ∨
        bit.val % sat3D N = sat3V N + 1 + sat3V N)))

/-! ### The pin-block reads -/

theorem sat3ContextP_pin_sel (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool) (ps : Fin 3) (p : Fin k) :
    sat3ContextP N C hk α b ps
      (sat3Bit N (sat3PinClauseM N C hk p) ps (α p).val
        (by have := (α p).isLt; omega)) = true := by
  show decide _ = true
  rw [decide_eq_true_eq]
  left
  exact ⟨p, sat3Bit_clause N (sat3PinClauseM N C hk p) ps (α p).val
    (by have := (α p).isLt; omega),
    Or.inl (sat3Bit_rem N (sat3PinClauseM N C hk p) ps (α p).val
      (by have := (α p).isLt; omega))⟩

theorem sat3ContextP_pin_miss (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool) (ps : Fin 3) (p : Fin k)
    (i : Fin (sat3V N)) (hi : i ≠ α p) :
    sat3ContextP N C hk α b ps
      (sat3Bit N (sat3PinClauseM N C hk p) ps i.val
        (by have := i.isLt; omega)) = false := by
  have hd := sat3Bit_clause N (sat3PinClauseM N C hk p) ps i.val
    (by have := i.isLt; omega)
  have hr := sat3Bit_rem N (sat3PinClauseM N C hk p) ps i.val
    (by have := i.isLt; omega)
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro (⟨p', hdiv, hrem⟩ | ⟨-, -, hnot, -⟩)
  · rw [hd] at hdiv
    have hpp' := sat3PinClauseM_val_inj N C hk (hdiv.symm)
    subst hpp'
    rcases hrem with h | ⟨h, -⟩
    · rw [hr] at h
      obtain ⟨-, hfe⟩ := slotField_eq ps ps
        (by have := i.isLt; omega) (by have := (α p').isLt; omega) h
      exact hi (Fin.ext hfe)
    · rw [hr] at h
      obtain ⟨-, hfe⟩ := slotField_eq ps ps
        (by have := i.isLt; omega) (by omega) h
      have := i.isLt
      omega
  · exact hnot p hd

theorem sat3ContextP_pin_dead (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool) (ps : Fin 3) (p : Fin k)
    (t : Fin 3) (ht : t ≠ ps) (i : Fin (sat3V N)) :
    sat3ContextP N C hk α b ps
      (sat3Bit N (sat3PinClauseM N C hk p) t i.val
        (by have := i.isLt; omega)) = false := by
  have hd := sat3Bit_clause N (sat3PinClauseM N C hk p) t i.val
    (by have := i.isLt; omega)
  have hr := sat3Bit_rem N (sat3PinClauseM N C hk p) t i.val
    (by have := i.isLt; omega)
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro (⟨p', hdiv, hrem⟩ | ⟨-, -, hnot, -⟩)
  · rcases hrem with h | ⟨h, -⟩
    · rw [hr] at h
      obtain ⟨hte, -⟩ := slotField_eq t ps
        (by have := i.isLt; omega) (by have := (α p').isLt; omega) h
      exact ht hte
    · rw [hr] at h
      obtain ⟨hte, -⟩ := slotField_eq t ps
        (by have := i.isLt; omega) (by omega) h
      exact ht hte
  · exact hnot p hd

theorem sat3ContextP_pin_sign (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool) (ps : Fin 3) (p : Fin k) :
    sat3ContextP N C hk α b ps
      (sat3Bit N (sat3PinClauseM N C hk p) ps (sat3V N) (by omega))
      = decide (b p = false) := by
  have hd := sat3Bit_clause N (sat3PinClauseM N C hk p) ps (sat3V N) (by omega)
  have hr := sat3Bit_rem N (sat3PinClauseM N C hk p) ps (sat3V N) (by omega)
  cases hbp : b p
  · show decide _ = true
    rw [decide_eq_true_eq]
    left
    exact ⟨p, hd, Or.inr ⟨hr, hbp⟩⟩
  · show decide _ = false
    rw [decide_eq_false_iff_not]
    rintro (⟨p', hdiv, hrem⟩ | ⟨-, -, hnot, -⟩)
    · rw [hd] at hdiv
      have hpp' := sat3PinClauseM_val_inj N C hk (hdiv.symm)
      subst hpp'
      rcases hrem with h | ⟨-, hbf⟩
      · rw [hr] at h
        obtain ⟨-, hfe⟩ := slotField_eq ps ps
          (by omega) (by have := (α p').isLt; omega) h
        have := (α p').isLt
        omega
      · rw [hbp] at hbf
        exact Bool.noConfusion hbf
    · exact hnot p hd

/-! ### The tautology-block reads -/

theorem sat3ContextP_taut_sel0 (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool) (ps : Fin 3)
    (cl : Fin (sat3M N)) (hclC : cl ∉ C)
    (hnp : ∀ p : Fin k, cl.val ≠ (sat3PinClauseM N C hk p).val) :
    sat3ContextP N C hk α b ps (sat3Bit N cl ⟨0, by omega⟩ 0 (by omega)) = true := by
  have hd := sat3Bit_clause N cl ⟨0, by omega⟩ 0 (by omega)
  have hr : (sat3Bit N cl ⟨0, by omega⟩ 0 (by omega)).val % sat3D N = 0 := by
    rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + 0 = 0
    omega
  show decide _ = true
  rw [decide_eq_true_eq]
  right
  refine ⟨by rw [hd]; exact cl.isLt, ?_, ?_, Or.inl hr⟩
  · intro c' hc'
    rw [hd]
    intro hval
    apply hclC
    rw [show cl = c' from Fin.ext hval]
    exact hc'
  · intro p
    rw [hd]
    exact hnp p

theorem sat3ContextP_taut_miss0 (N : ℕ) (hv : 1 ≤ sat3V N)
    (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool) (ps : Fin 3)
    (cl : Fin (sat3M N)) (hclC : cl ∉ C)
    (hnp : ∀ p : Fin k, cl.val ≠ (sat3PinClauseM N C hk p).val)
    (i : Fin (sat3V N)) (hi : i ≠ (⟨0, hv⟩ : Fin (sat3V N))) :
    sat3ContextP N C hk α b ps
      (sat3Bit N cl ⟨0, by omega⟩ i.val (by have := i.isLt; omega)) = false := by
  have hd := sat3Bit_clause N cl ⟨0, by omega⟩ i.val (by have := i.isLt; omega)
  have hr : (sat3Bit N cl ⟨0, by omega⟩ i.val
      (by have := i.isLt; omega)).val % sat3D N = i.val := by
    rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + i.val = i.val
    omega
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro (⟨p', hdiv, -⟩ | ⟨-, -, -, hpat⟩)
  · rw [hd] at hdiv
    exact hnp p' hdiv
  · rw [hr] at hpat
    have hilt := i.isLt
    rcases hpat with h | h | h
    · exact hi (Fin.ext h)
    · omega
    · omega

theorem sat3ContextP_taut_sign0 (N : ℕ) (hv : 1 ≤ sat3V N)
    (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool) (ps : Fin 3)
    (cl : Fin (sat3M N)) (hclC : cl ∉ C)
    (hnp : ∀ p : Fin k, cl.val ≠ (sat3PinClauseM N C hk p).val) :
    sat3ContextP N C hk α b ps
      (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)) = false := by
  have hd := sat3Bit_clause N cl ⟨0, by omega⟩ (sat3V N) (by omega)
  have hr : (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)).val % sat3D N
      = sat3V N := by
    rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N
    omega
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro (⟨p', hdiv, -⟩ | ⟨-, -, -, hpat⟩)
  · rw [hd] at hdiv
    exact hnp p' hdiv
  · rw [hr] at hpat
    rcases hpat with h | h | h <;> omega

theorem sat3ContextP_taut_sel1 (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool) (ps : Fin 3)
    (cl : Fin (sat3M N)) (hclC : cl ∉ C)
    (hnp : ∀ p : Fin k, cl.val ≠ (sat3PinClauseM N C hk p).val) :
    sat3ContextP N C hk α b ps (sat3Bit N cl ⟨1, by omega⟩ 0 (by omega)) = true := by
  have hd := sat3Bit_clause N cl ⟨1, by omega⟩ 0 (by omega)
  have hr : (sat3Bit N cl ⟨1, by omega⟩ 0 (by omega)).val % sat3D N
      = sat3V N + 1 := by
    rw [sat3Bit_rem]
    show (1 : ℕ) * (sat3V N + 1) + 0 = sat3V N + 1
    omega
  show decide _ = true
  rw [decide_eq_true_eq]
  right
  refine ⟨by rw [hd]; exact cl.isLt, ?_, ?_, Or.inr (Or.inl hr)⟩
  · intro c' hc'
    rw [hd]
    intro hval
    apply hclC
    rw [show cl = c' from Fin.ext hval]
    exact hc'
  · intro p
    rw [hd]
    exact hnp p

theorem sat3ContextP_taut_miss1 (N : ℕ) (hv : 1 ≤ sat3V N)
    (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool) (ps : Fin 3)
    (cl : Fin (sat3M N)) (hclC : cl ∉ C)
    (hnp : ∀ p : Fin k, cl.val ≠ (sat3PinClauseM N C hk p).val)
    (i : Fin (sat3V N)) (hi : i ≠ (⟨0, hv⟩ : Fin (sat3V N))) :
    sat3ContextP N C hk α b ps
      (sat3Bit N cl ⟨1, by omega⟩ i.val (by have := i.isLt; omega)) = false := by
  have hd := sat3Bit_clause N cl ⟨1, by omega⟩ i.val (by have := i.isLt; omega)
  have hr : (sat3Bit N cl ⟨1, by omega⟩ i.val
      (by have := i.isLt; omega)).val % sat3D N = sat3V N + 1 + i.val := by
    rw [sat3Bit_rem]
    show (1 : ℕ) * (sat3V N + 1) + i.val = sat3V N + 1 + i.val
    omega
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro (⟨p', hdiv, -⟩ | ⟨-, -, -, hpat⟩)
  · rw [hd] at hdiv
    exact hnp p' hdiv
  · rw [hr] at hpat
    have hilt := i.isLt
    rcases hpat with h | h | h
    · omega
    · have h0 : i.val = 0 := by omega
      exact hi (Fin.ext h0)
    · omega

theorem sat3ContextP_taut_sign1 (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool) (ps : Fin 3)
    (cl : Fin (sat3M N)) (hclC : cl ∉ C)
    (hnp : ∀ p : Fin k, cl.val ≠ (sat3PinClauseM N C hk p).val) :
    sat3ContextP N C hk α b ps
      (sat3Bit N cl ⟨1, by omega⟩ (sat3V N) (by omega)) = true := by
  have hd := sat3Bit_clause N cl ⟨1, by omega⟩ (sat3V N) (by omega)
  have hr : (sat3Bit N cl ⟨1, by omega⟩ (sat3V N) (by omega)).val % sat3D N
      = sat3V N + 1 + sat3V N := by
    rw [sat3Bit_rem]
    show (1 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N + 1 + sat3V N
    omega
  show decide _ = true
  rw [decide_eq_true_eq]
  right
  refine ⟨by rw [hd]; exact cl.isLt, ?_, ?_, Or.inr (Or.inr hr)⟩
  · intro c' hc'
    rw [hd]
    intro hval
    apply hclC
    rw [show cl = c' from Fin.ext hval]
    exact hc'
  · intro p
    rw [hd]
    exact hnp p

/-! ### The clause layer -/

/-- The single-live-literal clause analysis at ANY slot. -/
theorem sat3Clause_single_slot_iff (N : ℕ) (x : Fin N → Bool)
    (a : Fin (sat3V N) → Bool) (cl : Fin (sat3M N)) (s : Fin 3) (j : Fin (sat3V N))
    (hj : x (sat3Bit N cl s j.val (by have := j.isLt; omega)) = true)
    (hothers : ∀ i : Fin (sat3V N), i ≠ j →
      x (sat3Bit N cl s i.val (by have := i.isLt; omega)) = false)
    (hdead : ∀ t : Fin 3, t ≠ s → ∀ i : Fin (sat3V N),
      x (sat3Bit N cl t i.val (by have := i.isLt; omega)) = false) :
    (∃ t, sat3Lit N x a cl t = true) ↔
      xor (a j) (x (sat3Bit N cl s (sat3V N) (by omega))) = true := by
  constructor
  · rintro ⟨t, ht⟩
    by_cases hts : t = s
    · subst hts
      rwa [sat3Lit_single N x a cl t j hj hothers] at ht
    · rw [sat3Lit_false_of_empty N x a cl t (hdead t hts)] at ht
      exact Bool.noConfusion ht
  · intro h
    refine ⟨s, ?_⟩
    rw [sat3Lit_single N x a cl s j hj hothers]
    exact h

set_option maxHeartbeats 800000 in
/-- A pin clause of the parametric-patched instance is satisfied iff the pinned literal fires —
for ANY data contents `us`. -/
theorem sat3_pinslot_pin_clause_iff (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool) (ps : Fin 3)
    (us : Fin (sat3M N) → Fin N → Bool) (a : Fin (sat3V N) → Bool) (p : Fin k) :
    (∃ t, sat3Lit N (sat3PatchMulti N C (sat3ContextP N C hk α b ps) us) a
        (sat3PinClauseM N C hk p) t = true) ↔
      xor (a (α p)) (decide (b p = false)) = true := by
  have hiff := sat3Clause_single_slot_iff N
    (sat3PatchMulti N C (sat3ContextP N C hk α b ps) us) a
    (sat3PinClauseM N C hk p) ps (α p)
    (by
      rw [sat3PatchMulti_out_block N C (sat3ContextP N C hk α b ps) us _
        (sat3PinClauseM_not_mem N C hk p)]
      exact sat3ContextP_pin_sel N C hk α b ps p)
    (fun i hi => by
      rw [sat3PatchMulti_out_block N C (sat3ContextP N C hk α b ps) us _
        (sat3PinClauseM_not_mem N C hk p)]
      exact sat3ContextP_pin_miss N C hk α b ps p i hi)
    (fun t ht i => by
      rw [sat3PatchMulti_out_block N C (sat3ContextP N C hk α b ps) us _
        (sat3PinClauseM_not_mem N C hk p)]
      exact sat3ContextP_pin_dead N C hk α b ps p t ht i)
  rw [show sat3PatchMulti N C (sat3ContextP N C hk α b ps) us
      (sat3Bit N (sat3PinClauseM N C hk p) ps (sat3V N) (by omega))
      = decide (b p = false) from by
    rw [sat3PatchMulti_out_block N C (sat3ContextP N C hk α b ps) us _
      (sat3PinClauseM_not_mem N C hk p)]
    exact sat3ContextP_pin_sign N C hk α b ps p] at hiff
  exact hiff

set_option maxHeartbeats 800000 in
/-- A tautology block of the parametric-patched instance is satisfied by every assignment. -/
theorem sat3_pinslot_taut_clause_sat (N : ℕ) (hv : 1 ≤ sat3V N)
    (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool) (ps : Fin 3)
    (us : Fin (sat3M N) → Fin N → Bool) (a : Fin (sat3V N) → Bool)
    (cl : Fin (sat3M N)) (h1 : cl ∉ C)
    (h2 : ∀ p : Fin k, cl.val ≠ (sat3PinClauseM N C hk p).val) :
    ∃ t, sat3Lit N (sat3PatchMulti N C (sat3ContextP N C hk α b ps) us) a cl t = true := by
  cases ha : a ⟨0, hv⟩
  · refine ⟨⟨1, by omega⟩, ?_⟩
    rw [sat3Lit_single N (sat3PatchMulti N C (sat3ContextP N C hk α b ps) us) a cl
        ⟨1, by omega⟩ ⟨0, hv⟩
        (by
          rw [sat3PatchMulti_out_block N C (sat3ContextP N C hk α b ps) us cl h1]
          exact sat3ContextP_taut_sel1 N C hk α b ps cl h1 h2)
        (fun i hi => by
          rw [sat3PatchMulti_out_block N C (sat3ContextP N C hk α b ps) us cl h1]
          exact sat3ContextP_taut_miss1 N hv C hk α b ps cl h1 h2 i hi),
      show sat3PatchMulti N C (sat3ContextP N C hk α b ps) us
          (sat3Bit N cl ⟨1, by omega⟩ (sat3V N) (by omega)) = true from by
        rw [sat3PatchMulti_out_block N C (sat3ContextP N C hk α b ps) us cl h1]
        exact sat3ContextP_taut_sign1 N C hk α b ps cl h1 h2,
      Bool.xor_true, ha]
    rfl
  · refine ⟨⟨0, by omega⟩, ?_⟩
    rw [sat3Lit_single N (sat3PatchMulti N C (sat3ContextP N C hk α b ps) us) a cl
        ⟨0, by omega⟩ ⟨0, hv⟩
        (by
          rw [sat3PatchMulti_out_block N C (sat3ContextP N C hk α b ps) us cl h1]
          exact sat3ContextP_taut_sel0 N C hk α b ps cl h1 h2)
        (fun i hi => by
          rw [sat3PatchMulti_out_block N C (sat3ContextP N C hk α b ps) us cl h1]
          exact sat3ContextP_taut_miss0 N hv C hk α b ps cl h1 h2 i hi),
      show sat3PatchMulti N C (sat3ContextP N C hk α b ps) us
          (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)) = false from by
        rw [sat3PatchMulti_out_block N C (sat3ContextP N C hk α b ps) us cl h1]
        exact sat3ContextP_taut_sign0 N hv C hk α b ps cl h1 h2,
      Bool.xor_false, ha]

/-! ### The eval -/

set_option maxHeartbeats 1600000 in
/-- **THE PIN-SLOT KIT EVAL (proved)**: the private-kit eval with pins at ANY slot `ps` — the
data-block layer is reused unchanged; only the pin channel moved. -/
theorem sat3_pinslot_kit_eval (N : ℕ) (hv : 1 ≤ sat3V N)
    (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (hα : Function.Injective α) (ps : Fin 3)
    (T : Fin (sat3M N) → Finset (Fin (sat3V N)))
    (u : Fin (sat3M N) → Fin (sat3V N))
    (hcov : ∀ c ∈ C, ∀ w ∈ T c, ∃ p : Fin k, α p = w)
    (hucov : ∀ c ∈ C, ∃ p : Fin k, α p = u c)
    (huinj : ∀ c ∈ C, ∀ c' ∈ C, u c = u c' → c = c')
    (hupat : ∀ c ∈ C, ∀ c' ∈ C, u c ∉ T c')
    (cstar : Fin (sat3M N)) (hcstar : cstar ∈ C)
    (wstar : Fin (sat3V N)) (pstar : Fin k) (hpstar : α pstar = wstar)
    (huw : ∀ c ∈ C, u c ≠ wstar) :
    sat3Family N (sat3PatchMulti N C
      (sat3ContextP N C hk α (fun p =>
        decide (α p = wstar ∨ ∃ c ∈ C, c ≠ cstar ∧ α p = u c)) ps)
      (sat3KitP N T u))
      = decide (wstar ∈ T cstar) := by
  classical
  set bvec : Fin k → Bool := fun p =>
    decide (α p = wstar ∨ ∃ c ∈ C, c ≠ cstar ∧ α p = u c) with hbvec
  set x : Fin N → Bool :=
    sat3PatchMulti N C (sat3ContextP N C hk α bvec ps) (sat3KitP N T u) with hx
  have hbvec_u : ∀ c ∈ C, ∀ p : Fin k, α p = u c →
      bvec p = decide (c ≠ cstar) := by
    intro c hc p hp
    by_cases hne : c = cstar
    · rw [hne] at hp hc ⊢
      have : bvec p = false := by
        apply decide_eq_false
        rintro (h | ⟨c', hc', hne', h⟩)
        · exact huw cstar hc (hp.symm.trans h)
        · exact hne' (huinj cstar hc c' hc' (hp.symm.trans h)).symm
      rw [this, decide_eq_false (by simp : ¬(cstar ≠ cstar))]
    · have : bvec p = true := by
        apply decide_eq_true
        exact Or.inr ⟨c, hc, hne, hp⟩
      rw [this, decide_eq_true hne]
  by_cases hsat : wstar ∈ T cstar
  · rw [decide_eq_true hsat]
    set awit : Fin (sat3V N) → Bool :=
      fun i => if h : ∃ p : Fin k, α p = i then bvec (Classical.choose h) else true
      with hawit
    have hawit_at : ∀ p : Fin k, awit (α p) = bvec p := by
      intro p
      show (if h : ∃ p' : Fin k, α p' = α p then bvec (Classical.choose h) else true)
        = bvec p
      have hex : ∃ p' : Fin k, α p' = α p := ⟨p, rfl⟩
      rw [dif_pos hex]
      exact congrArg bvec (hα (Classical.choose_spec hex))
    have hawit_wstar : awit wstar = true := by
      rw [← hpstar, hawit_at pstar]
      exact decide_eq_true (Or.inl hpstar)
    have hawit_u : ∀ c ∈ C, c ≠ cstar → awit (u c) = true := by
      intro c hc hne
      obtain ⟨p, hp⟩ := hucov c hc
      rw [← hp, hawit_at p, hbvec_u c hc p hp]
      exact decide_eq_true hne
    rw [sat3Family_iff]
    refine ⟨awit, sat3Eval_true_of_all N x awit ?_⟩
    intro cl
    by_cases hclC : cl ∈ C
    · by_cases hclstar : cl = cstar
      · refine (sat3_private_data_clause_iff N C (sat3ContextP N C hk α bvec ps) T u
          awit cl hclC).mpr (Or.inl ⟨wstar, ?_, hawit_wstar⟩)
        rw [hclstar]
        exact hsat
      · exact sat3_private_kit_neutralized N C (sat3ContextP N C hk α bvec ps) T u
          awit cl hclC (hawit_u cl hclC hclstar)
    · by_cases hpin : ∃ p : Fin k, sat3PinClauseM N C hk p = cl
      · obtain ⟨p, rfl⟩ := hpin
        refine (sat3_pinslot_pin_clause_iff N C hk α bvec ps (sat3KitP N T u)
          awit p).mpr ?_
        rw [hawit_at p]
        cases bvec p <;> rfl
      · exact sat3_pinslot_taut_clause_sat N hv C hk α bvec ps (sat3KitP N T u)
          awit cl hclC (fun p h => hpin ⟨p, Fin.ext h.symm⟩)
  · rw [decide_eq_false hsat]
    apply decide_eq_false
    rintro ⟨A, hA⟩
    have hforce : ∀ p : Fin k, A (α p) = bvec p := by
      intro p
      exact xor_decide_eq _ _
        ((sat3_pinslot_pin_clause_iff N C hk α bvec ps (sat3KitP N T u) A p).mp
          (sat3Eval_clause_true N x A hA (sat3PinClauseM N C hk p)))
    rcases (sat3_private_data_clause_iff N C (sat3ContextP N C hk α bvec ps) T u
        A cstar hcstar).mp (sat3Eval_clause_true N x A hA cstar)
      with ⟨w, hwT, hAw⟩ | hAu
    · obtain ⟨p, hp⟩ := hcov cstar hcstar w hwT
      have h1 : bvec p = true := by
        rw [← hforce p, hp]
        exact hAw
      have h1' : decide (α p = wstar ∨ ∃ c ∈ C, c ≠ cstar ∧ α p = u c) = true := h1
      rcases of_decide_eq_true h1' with h | ⟨c', hc', -, h⟩
      · have hww : w = wstar := by
          rw [← hp]
          exact h
        rw [hww] at hwT
        exact hsat hwT
      · have hwu : w = u c' := by
          rw [← hp]
          exact h
        rw [hwu] at hwT
        exact hupat c' hc' cstar hcstar hwT
    · obtain ⟨p, hp⟩ := hucov cstar hcstar
      have h1 : bvec p = decide (cstar ≠ cstar) := hbvec_u cstar hcstar p hp
      rw [decide_eq_false (by simp : ¬(cstar ≠ cstar))] at h1
      have h2 : A (u cstar) = false := by
        rw [← hp, hforce p, h1]
      rw [hAu] at h2
      exact Bool.noConfusion h2

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3ContextP_pin_sign
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3Clause_single_slot_iff
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_pinslot_pin_clause_iff
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_pinslot_kit_eval
