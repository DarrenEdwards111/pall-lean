import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMultiBlockPatch

/-!
# N-Frame: the multi-block context — pins avoiding a set of designated blocks

Rung 2 of the multi-block additive-drag arc (patch → **context** → eval → drag/window).  The
single-block `sat3ContextG` pins every clause except one designated block; the additive drag
designates a SET `C` of data blocks at once, so the pin enumeration must avoid all of `C`.

  `sat3PinClauseM` — the pin enumeration: an injection `Fin k → Fin m` landing outside `C`
        (through `(univ \ C).equivFin`), with injectivity and the pool count `m − |C|`.
  `sat3ContextM` — the context: pin clause `p` forces `a (α p) = bvec p`, blocks outside
        `C ∪ pins` are tautologies, blocks of `C` are left empty (they carry the patch).
  `sat3ContextM_agree` / `_designated` / `_pin_sign` / `_injective` — the four core lemmas,
        faithful mirrors of the `sat3ContextG` versions.
  `sat3ContextM_pin_sel` / `_pin_miss` / `_pin_dead` and the six tautology reads — the whole
        read kit exported at context level, so the eval rung consumes them directly.

## Honest scope

Context plumbing — no lower-bound content.  The single-block context is NOT definitionally the
`C = {c}` instance (the pin enumerations differ by a reindexing), and no bridge is needed: the
eval rung works natively with `sat3ContextM`.  Remaining rungs: the multi-block eval (slot-1
kits neutralizing the other data blocks), the additive drag (`j ≥ Σ_c d_c`), the rebuilt
window.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The pin enumeration -/

/-- The `p`-th pin clause: the `p`-th element of the block pool outside `C`. -/
noncomputable def sat3PinClauseM (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card) (p : Fin k) :
    Fin (sat3M N) :=
  ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).equivFin.symm (Fin.castLE hk p)).val

theorem sat3PinClauseM_not_mem (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card) (p : Fin k) :
    sat3PinClauseM N C hk p ∉ C := by
  have hmem := ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).equivFin.symm
    (Fin.castLE hk p)).prop
  exact (Finset.mem_sdiff.mp hmem).2

theorem sat3PinClauseM_inj (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card) :
    Function.Injective (sat3PinClauseM N C hk) := by
  intro p p' h
  have h1 : ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).equivFin.symm
      (Fin.castLE hk p))
      = ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).equivFin.symm
      (Fin.castLE hk p')) := Subtype.ext h
  have h2 := (((Finset.univ : Finset (Fin (sat3M N))) \ C)).equivFin.symm.injective h1
  exact Fin.castLE_injective hk h2

theorem sat3PinClauseM_val_inj (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card) {p p' : Fin k}
    (h : (sat3PinClauseM N C hk p).val = (sat3PinClauseM N C hk p').val) : p = p' :=
  sat3PinClauseM_inj N C hk (Fin.ext h)

/-- The pin pool size: `m − |C|`. -/
theorem sat3_pin_pool_card (N : ℕ) (C : Finset (Fin (sat3M N))) :
    (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card = sat3M N - C.card := by
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]

/-! ### The context -/

/-- The multi-block pin context: pin clause `p` forces `a (α p) = bvec p`, blocks outside
`C ∪ pins` are tautologies, blocks of `C` are left empty. -/
noncomputable def sat3ContextM (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (bvec : Fin k → Bool) : Fin N → Bool :=
  fun bit => decide (
    (∃ p : Fin k, bit.val / sat3D N = (sat3PinClauseM N C hk p).val ∧
      (bit.val % sat3D N = (α p).val ∨
        (bit.val % sat3D N = sat3V N ∧ bvec p = false)))
    ∨ (bit.val / sat3D N < sat3M N ∧
      (∀ c ∈ C, bit.val / sat3D N ≠ c.val) ∧
      (∀ p : Fin k, bit.val / sat3D N ≠ (sat3PinClauseM N C hk p).val) ∧
      (bit.val % sat3D N = 0 ∨ bit.val % sat3D N = sat3V N + 1 ∨
        bit.val % sat3D N = sat3V N + 1 + sat3V N)))

/-! ### The four core lemmas -/

theorem sat3ContextM_agree (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b b' : Fin k → Bool) (i : Fin N)
    (hag : ∀ p : Fin k, i.val / sat3D N = (sat3PinClauseM N C hk p).val →
      i.val % sat3D N = sat3V N → b p = b' p) :
    sat3ContextM N C hk α b i = sat3ContextM N C hk α b' i := by
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

/-- The context vanishes on every designated block. -/
theorem sat3ContextM_designated (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool) (i : Fin N)
    (c : Fin (sat3M N)) (hc : c ∈ C) (hdiv : i.val / sat3D N = c.val) :
    sat3ContextM N C hk α b i = false := by
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro (⟨p, hp1, -⟩ | ⟨-, hne, -, -⟩)
  · have hpc : sat3PinClauseM N C hk p = c := Fin.ext (hp1.symm.trans hdiv)
    apply sat3PinClauseM_not_mem N C hk p
    rw [hpc]
    exact hc
  · exact hne c hc hdiv

/-- The pin-sign read. -/
theorem sat3ContextM_pin_sign (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool) (p : Fin k) :
    sat3ContextM N C hk α b
      (sat3Bit N (sat3PinClauseM N C hk p) ⟨0, by omega⟩ (sat3V N) (by omega))
      = decide (b p = false) := by
  have hd := sat3Bit_clause N (sat3PinClauseM N C hk p) ⟨0, by omega⟩ (sat3V N)
    (by omega)
  have hr : (sat3Bit N (sat3PinClauseM N C hk p) ⟨0, by omega⟩ (sat3V N)
      (by omega)).val % sat3D N = sat3V N := by
    rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N
    omega
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
        have := (α p').isLt
        omega
      · rw [hbp] at hbf
        exact Bool.noConfusion hbf
    · exact hnot p hd

/-- Distinct sign vectors give distinct contexts. -/
theorem sat3ContextM_injective (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) :
    Function.Injective (fun bvec : Fin k → Bool => sat3ContextM N C hk α bvec) := by
  intro b b' heq
  funext p
  have heq' : sat3ContextM N C hk α b = sat3ContextM N C hk α b' := heq
  have h := congrFun heq'
    (sat3Bit N (sat3PinClauseM N C hk p) ⟨0, by omega⟩ (sat3V N) (by omega))
  rw [sat3ContextM_pin_sign N C hk α b p,
    sat3ContextM_pin_sign N C hk α b' p] at h
  cases hb : b p <;> cases hb' : b' p
  · rfl
  · rw [hb, hb'] at h
    exact Bool.noConfusion h
  · rw [hb, hb'] at h
    exact Bool.noConfusion h
  · rfl

/-! ### The pin-block read kit -/

theorem sat3ContextM_pin_sel (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool) (p : Fin k) :
    sat3ContextM N C hk α b
      (sat3Bit N (sat3PinClauseM N C hk p) ⟨0, by omega⟩ (α p).val
        (by have := (α p).isLt; omega)) = true := by
  show decide _ = true
  rw [decide_eq_true_eq]
  left
  refine ⟨p, sat3Bit_clause N (sat3PinClauseM N C hk p) ⟨0, by omega⟩ (α p).val
    (by have := (α p).isLt; omega), Or.inl ?_⟩
  rw [sat3Bit_rem]
  show (0 : ℕ) * (sat3V N + 1) + (α p).val = (α p).val
  omega

theorem sat3ContextM_pin_miss (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool) (p : Fin k)
    (i : Fin (sat3V N)) (hi : i ≠ α p) :
    sat3ContextM N C hk α b
      (sat3Bit N (sat3PinClauseM N C hk p) ⟨0, by omega⟩ i.val
        (by have := i.isLt; omega)) = false := by
  have hd := sat3Bit_clause N (sat3PinClauseM N C hk p) ⟨0, by omega⟩ i.val
    (by have := i.isLt; omega)
  have hr : (sat3Bit N (sat3PinClauseM N C hk p) ⟨0, by omega⟩ i.val
      (by have := i.isLt; omega)).val % sat3D N = i.val := by
    rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + i.val = i.val
    omega
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro (⟨p', hdiv, hrem⟩ | ⟨-, -, hnot, -⟩)
  · rw [hd] at hdiv
    have hpp' := sat3PinClauseM_val_inj N C hk (hdiv.symm)
    subst hpp'
    rcases hrem with h | ⟨h, -⟩
    · rw [hr] at h
      exact hi (Fin.ext h)
    · rw [hr] at h
      have := i.isLt
      omega
  · exact hnot p hd

theorem sat3ContextM_pin_dead (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool) (p : Fin k)
    (t : Fin 3) (ht : 1 ≤ t.val) (i : Fin (sat3V N)) :
    sat3ContextM N C hk α b
      (sat3Bit N (sat3PinClauseM N C hk p) t i.val
        (by have := i.isLt; omega)) = false := by
  have hd := sat3Bit_clause N (sat3PinClauseM N C hk p) t i.val
    (by have := i.isLt; omega)
  have hr := sat3Bit_rem N (sat3PinClauseM N C hk p) t i.val
    (by have := i.isLt; omega)
  have hbound : sat3V N + 1 ≤ t.val * (sat3V N + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro (⟨p', hdiv, hrem⟩ | ⟨-, -, hnot, -⟩)
  · have := (α p').isLt
    rcases hrem with h | ⟨h, -⟩ <;> rw [hr] at h <;> omega
  · exact hnot p hd

/-! ### The tautology-block read kit -/

theorem sat3ContextM_taut_sel0 (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool)
    (cl : Fin (sat3M N)) (hclC : cl ∉ C)
    (hnp : ∀ p : Fin k, cl.val ≠ (sat3PinClauseM N C hk p).val) :
    sat3ContextM N C hk α b (sat3Bit N cl ⟨0, by omega⟩ 0 (by omega)) = true := by
  have hd := sat3Bit_clause N cl ⟨0, by omega⟩ 0 (by omega)
  have hr : (sat3Bit N cl ⟨0, by omega⟩ 0 (by omega)).val % sat3D N = 0 := by
    rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + 0 = 0
    omega
  show decide _ = true
  rw [decide_eq_true_eq]
  right
  refine ⟨?_, ?_, ?_, Or.inl hr⟩
  · rw [hd]
    exact cl.isLt
  · intro c' hc'
    rw [hd]
    intro hval
    apply hclC
    rw [show cl = c' from Fin.ext hval]
    exact hc'
  · intro p
    rw [hd]
    exact hnp p

theorem sat3ContextM_taut_miss0 (N : ℕ) (hv : 1 ≤ sat3V N)
    (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool)
    (cl : Fin (sat3M N)) (hclC : cl ∉ C)
    (hnp : ∀ p : Fin k, cl.val ≠ (sat3PinClauseM N C hk p).val)
    (i : Fin (sat3V N)) (hi : i ≠ (⟨0, hv⟩ : Fin (sat3V N))) :
    sat3ContextM N C hk α b
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

theorem sat3ContextM_taut_sign0 (N : ℕ) (hv : 1 ≤ sat3V N)
    (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool)
    (cl : Fin (sat3M N)) (hclC : cl ∉ C)
    (hnp : ∀ p : Fin k, cl.val ≠ (sat3PinClauseM N C hk p).val) :
    sat3ContextM N C hk α b
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

theorem sat3ContextM_taut_sel1 (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool)
    (cl : Fin (sat3M N)) (hclC : cl ∉ C)
    (hnp : ∀ p : Fin k, cl.val ≠ (sat3PinClauseM N C hk p).val) :
    sat3ContextM N C hk α b (sat3Bit N cl ⟨1, by omega⟩ 0 (by omega)) = true := by
  have hd := sat3Bit_clause N cl ⟨1, by omega⟩ 0 (by omega)
  have hr : (sat3Bit N cl ⟨1, by omega⟩ 0 (by omega)).val % sat3D N
      = sat3V N + 1 := by
    rw [sat3Bit_rem]
    show (1 : ℕ) * (sat3V N + 1) + 0 = sat3V N + 1
    omega
  show decide _ = true
  rw [decide_eq_true_eq]
  right
  refine ⟨?_, ?_, ?_, Or.inr (Or.inl hr)⟩
  · rw [hd]
    exact cl.isLt
  · intro c' hc'
    rw [hd]
    intro hval
    apply hclC
    rw [show cl = c' from Fin.ext hval]
    exact hc'
  · intro p
    rw [hd]
    exact hnp p

theorem sat3ContextM_taut_miss1 (N : ℕ) (hv : 1 ≤ sat3V N)
    (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool)
    (cl : Fin (sat3M N)) (hclC : cl ∉ C)
    (hnp : ∀ p : Fin k, cl.val ≠ (sat3PinClauseM N C hk p).val)
    (i : Fin (sat3V N)) (hi : i ≠ (⟨0, hv⟩ : Fin (sat3V N))) :
    sat3ContextM N C hk α b
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

theorem sat3ContextM_taut_sign1 (N : ℕ) (C : Finset (Fin (sat3M N))) {k : ℕ}
    (hk : k ≤ (((Finset.univ : Finset (Fin (sat3M N))) \ C)).card)
    (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool)
    (cl : Fin (sat3M N)) (hclC : cl ∉ C)
    (hnp : ∀ p : Fin k, cl.val ≠ (sat3PinClauseM N C hk p).val) :
    sat3ContextM N C hk α b
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
  refine ⟨?_, ?_, ?_, Or.inr (Or.inr hr)⟩
  · rw [hd]
    exact cl.isLt
  · intro c' hc'
    rw [hd]
    intro hval
    apply hclC
    rw [show cl = c' from Fin.ext hval]
    exact hc'
  · intro p
    rw [hd]
    exact hnp p

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3ContextM_agree
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3ContextM_pin_sign
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3ContextM_injective
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3ContextM_taut_sign1
