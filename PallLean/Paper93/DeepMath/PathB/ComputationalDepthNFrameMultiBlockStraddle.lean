import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMultiBlockSignSqueeze

/-!
# N-Frame: the straddle drag — the first heavy-band instrument

Rung 18 of the multi-block arc (… → sign squeeze → **straddle**).  At heavy bands
(`T ≥ m·v/2`) every pin-based tool dies: pins need mode-dependent bits in `Sᶜ`, and a heavy `S`
can swallow them all.  The attack must be PINLESS — and the encoding has exactly one pinless
channel: the EMPTY CLAUSE (`sat3Family_false_of_empty_clause`, the 0-corner).  Rows toggle one
`S`-side slot-0 selector per straddling block; the probe zeroes the designated block's
`Sᶜ`-side and keep-alives every other block with a positive literal; the all-true assignment
witnesses satisfiability.  The mixed instance evaluates to `[designated block nonempty]` — no
pins, no sign conditions, no pool room, no band restriction:

  `sat3Bit_eq_slot0` — layout-bit collision analysis (block, slot, field recovered).
  `sat3_straddle_drag` — **PROVED, the pinless drag**: blocks with a slot-0 selector bit on
        EACH side of the cut satisfy `|C| ≤ j` — `2^|C|` emptiness patterns are pairwise
        distinguishable through the cut.
  `sat3_straddle_census` — the census form: `#{c : slot-0 straddling} ≤ j`, unconditionally.
  `sat3_straddle_band` — **PROVED, the alignment law**: every balanced cut of a minimal SAT
        circuit has at most `coneExcess + 1` slot-0-straddling blocks — minimal circuits'
        balanced cone supports respect block boundaries up to the cone excess, AT EVERY BAND
        including the heaviest.

Why this matters for the endgame: low-`coneExcess` heavy cuts are forced NEARLY BLOCK-ALIGNED,
and aligned cuts hand the cleanliness-free private window its `hdata` hypothesis for free
(a fully-in block contains ALL its pattern bits).  The remaining fight at heavy bands is the
pool side: aligned-out blocks are full pin blocks, but their slot-0 SELECTOR bits can be
poisoned by `S` (only slot-0 pins are formalized) — pricing that requires the pin-slot-
parametric rebuild (pins at slot 1/2), a counting war the adversary cannot win across all
three slots at once.  That is the named next rung; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Bit collision analysis -/

theorem sat3Bit_eq_slot0 (N : ℕ) (c c' : Fin (sat3M N)) (t : Fin 3) (f f' : ℕ)
    (hf : f < sat3V N + 1) (hf' : f' < sat3V N + 1)
    (h : sat3Bit N c t f hf = sat3Bit N c' ⟨0, by omega⟩ f' hf') :
    c = c' ∧ t = ⟨0, by omega⟩ ∧ f = f' := by
  have hdiv : c.val = c'.val := by
    have h1 := sat3Bit_clause N c t f hf
    have h2 := sat3Bit_clause N c' ⟨0, by omega⟩ f' hf'
    rw [← h1, ← h2, h]
  have hrem : t.val * (sat3V N + 1) + f = 0 * (sat3V N + 1) + f' := by
    have h1 := sat3Bit_rem N c t f hf
    have h2 := sat3Bit_rem N c' ⟨0, by omega⟩ f' hf'
    rw [← h1, ← h2, h]
  rcases t with ⟨tv, htv⟩
  interval_cases tv
  · refine ⟨Fin.ext hdiv, Fin.ext rfl, ?_⟩
    have hr : (0 : ℕ) * (sat3V N + 1) + f = 0 * (sat3V N + 1) + f' := hrem
    omega
  · exfalso
    have hr : (1 : ℕ) * (sat3V N + 1) + f = 0 * (sat3V N + 1) + f' := hrem
    omega
  · exfalso
    have hr : (2 : ℕ) * (sat3V N + 1) + f = 0 * (sat3V N + 1) + f' := hrem
    omega

theorem sat3Bit_congr_field (N : ℕ) (c : Fin (sat3M N)) (w w' : Fin (sat3V N))
    (h : w = w') :
    sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega)
      = sat3Bit N c ⟨0, by omega⟩ w'.val (by have := w'.isLt; omega) := by
  subst h
  rfl

/-! ### The straddle drag -/

set_option maxHeartbeats 3200000 in
/-- **THE STRADDLE DRAG (proved, pinless)**: blocks carrying a slot-0 selector bit on EACH side
of the cut number at most `j`.  Rows toggle emptiness; probes isolate one block through the
0-corner; the all-true assignment witnesses the live side.  No pins, no sign conditions, no
pool room, no band restriction. -/
theorem sat3_straddle_drag (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (C : Finset (Fin (sat3M N)))
    (wIn wOut : Fin (sat3M N) → Fin (sat3V N))
    (hIn : ∀ c ∈ C, sat3Bit N c ⟨0, by omega⟩ (wIn c).val
      (by have := (wIn c).isLt; omega) ∈ S)
    (hOut : ∀ c ∈ C, sat3Bit N c ⟨0, by omega⟩ (wOut c).val
      (by have := (wOut c).isLt; omega) ∉ S) :
    C.card ≤ j := by
  classical
  set row : Finset (Fin (sat3M N)) → Fin N → Bool := fun E => fun i =>
    decide ((∃ c ∈ C, c ∈ E ∧ i = sat3Bit N c ⟨0, by omega⟩ (wIn c).val
        (by have := (wIn c).isLt; omega))
      ∨ (∃ b : Fin (sat3M N), b ∉ C ∧ i ∈ S
          ∧ i = sat3Bit N b ⟨0, by omega⟩ 0 (by omega))) with hrow
  have hrow_read : ∀ (E : Finset (Fin (sat3M N))), ∀ c ∈ C,
      row E (sat3Bit N c ⟨0, by omega⟩ (wIn c).val
        (by have := (wIn c).isLt; omega)) = decide (c ∈ E) := by
    intro E c hc
    rw [hrow]
    show decide _ = decide (c ∈ E)
    apply decide_eq_decide.mpr
    constructor
    · rintro (⟨c', hc', hcE', heq⟩ | ⟨b, hbC, -, heq⟩)
      · obtain ⟨hblk, -, -⟩ := sat3Bit_eq_slot0 N c c' _ _ _ _ _ heq
        rw [hblk]
        exact hcE'
      · obtain ⟨hblk, -, -⟩ := sat3Bit_eq_slot0 N c b _ _ _ _ _ heq
        exact absurd (hblk ▸ hc) hbC
    · intro hcE
      exact Or.inl ⟨c, hc, hcE, rfl⟩
  set Y : Finset (Fin N → Bool) := C.powerset.image row with hY
  have hYcard : Y.card = 2 ^ C.card := by
    rw [hY, Finset.card_image_of_injOn, Finset.card_powerset]
    intro E hE E' hE' heq
    have hEsub := Finset.mem_powerset.mp (Finset.mem_coe.mp hE)
    have hE'sub := Finset.mem_powerset.mp (Finset.mem_coe.mp hE')
    ext c
    by_cases hc : c ∈ C
    · have h := congrFun heq (sat3Bit N c ⟨0, by omega⟩ (wIn c).val
        (by have := (wIn c).isLt; omega))
      rw [hrow_read E c hc, hrow_read E' c hc] at h
      constructor
      · intro h'
        exact of_decide_eq_true (by rw [← h]; exact decide_eq_true h')
      · intro h'
        exact of_decide_eq_true (by rw [h]; exact decide_eq_true h')
    · constructor
      · intro h'
        exact absurd (hEsub h') hc
      · intro h'
        exact absurd (hE'sub h') hc
  have hdist : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' →
      ∃ x, sat3Family N (mixOn Sᶜ x y) ≠ sat3Family N (mixOn Sᶜ x y') := by
    intro y hy y' hy' hne
    rw [hY] at hy hy'
    obtain ⟨E, hEmem, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨E', hE'mem, rfl⟩ := Finset.mem_image.mp hy'
    have hEsub := Finset.mem_powerset.mp hEmem
    have hE'sub := Finset.mem_powerset.mp hE'mem
    have hEne : E ≠ E' := fun hcon => hne (by rw [hcon])
    have hex : ∃ c₀ ∈ C, ¬(c₀ ∈ E ↔ c₀ ∈ E') := by
      by_contra hcon
      push_neg at hcon
      apply hEne
      ext q
      by_cases hq : q ∈ C
      · exact hcon q hq
      · constructor
        · intro h'
          exact absurd (hEsub h') hq
        · intro h'
          exact absurd (hE'sub h') hq
    obtain ⟨c₀, hc₀C, hqd⟩ := hex
    set probe : Fin N → Bool := fun i =>
      decide ((∃ c ∈ C, c ≠ c₀ ∧ i = sat3Bit N c ⟨0, by omega⟩ (wOut c).val
          (by have := (wOut c).isLt; omega))
        ∨ (∃ b : Fin (sat3M N), b ∉ C ∧ i ∉ S
            ∧ i = sat3Bit N b ⟨0, by omega⟩ 0 (by omega))) with hprobe
    -- sign bits read false through the mix
    have hsign_read : ∀ (E'' : Finset (Fin (sat3M N))) (cl : Fin (sat3M N)) (t : Fin 3),
        mixOn Sᶜ probe (row E'') (sat3Bit N cl t (sat3V N) (by omega)) = false := by
      intro E'' cl t
      show (if sat3Bit N cl t (sat3V N) (by omega) ∈ Sᶜ
        then probe (sat3Bit N cl t (sat3V N) (by omega))
        else row E'' (sat3Bit N cl t (sat3V N) (by omega))) = false
      by_cases hs : sat3Bit N cl t (sat3V N) (by omega) ∈ Sᶜ
      · rw [if_pos hs, hprobe]
        show decide _ = false
        rw [decide_eq_false_iff_not]
        rintro (⟨c, -, -, heq⟩ | ⟨b, -, -, heq⟩)
        · obtain ⟨-, -, hfld⟩ := sat3Bit_eq_slot0 N cl c _ _ _ _ _ heq
          have := (wOut c).isLt
          omega
        · obtain ⟨-, -, hfld⟩ := sat3Bit_eq_slot0 N cl b _ _ _ _ _ heq
          omega
      · rw [if_neg hs, hrow]
        show decide _ = false
        rw [decide_eq_false_iff_not]
        rintro (⟨c, -, -, heq⟩ | ⟨b, -, -, heq⟩)
        · obtain ⟨-, -, hfld⟩ := sat3Bit_eq_slot0 N cl c _ _ _ _ _ heq
          have := (wIn c).isLt
          omega
        · obtain ⟨-, -, hfld⟩ := sat3Bit_eq_slot0 N cl b _ _ _ _ _ heq
          omega
    -- the designated block reads all-zero when its datum is off
    have hc₀_read : ∀ (E'' : Finset (Fin (sat3M N))), c₀ ∉ E'' →
        ∀ (t : Fin 3) (i : Fin (sat3V N)),
        mixOn Sᶜ probe (row E'')
          (sat3Bit N c₀ t i.val (by have := i.isLt; omega)) = false := by
      intro E'' hmem t i
      show (if sat3Bit N c₀ t i.val (by have := i.isLt; omega) ∈ Sᶜ
        then probe (sat3Bit N c₀ t i.val (by have := i.isLt; omega))
        else row E'' (sat3Bit N c₀ t i.val (by have := i.isLt; omega))) = false
      by_cases hs : sat3Bit N c₀ t i.val (by have := i.isLt; omega) ∈ Sᶜ
      · rw [if_pos hs, hprobe]
        show decide _ = false
        rw [decide_eq_false_iff_not]
        rintro (⟨c, -, hne, heq⟩ | ⟨b, hbC, -, heq⟩)
        · obtain ⟨hblk, -, -⟩ := sat3Bit_eq_slot0 N c₀ c _ _ _ _ _ heq
          exact hne hblk.symm
        · obtain ⟨hblk, -, -⟩ := sat3Bit_eq_slot0 N c₀ b _ _ _ _ _ heq
          exact hbC (hblk ▸ hc₀C)
      · rw [if_neg hs, hrow]
        show decide _ = false
        rw [decide_eq_false_iff_not]
        rintro (⟨c, -, hcE, heq⟩ | ⟨b, hbC, -, heq⟩)
        · obtain ⟨hblk, -, -⟩ := sat3Bit_eq_slot0 N c₀ c _ _ _ _ _ heq
          exact hmem (hblk ▸ hcE)
        · obtain ⟨hblk, -, -⟩ := sat3Bit_eq_slot0 N c₀ b _ _ _ _ _ heq
          exact hbC (hblk ▸ hc₀C)
    -- the evaluation: the mixed instance reads the designated block's emptiness
    have hval : ∀ (E'' : Finset (Fin (sat3M N))),
        sat3Family N (mixOn Sᶜ probe (row E'')) = decide (c₀ ∈ E'') := by
      intro E''
      by_cases hmem : c₀ ∈ E''
      · rw [decide_eq_true hmem]
        apply sat3Family_of_witness N _ (fun _ => true)
        apply sat3Eval_true_of_all
        intro cl
        by_cases hclC : cl ∈ C
        · by_cases hclE : cl ∈ E''
          · refine ⟨⟨0, by omega⟩, sat3Lit_true_of_selected N _ _ cl ⟨0, by omega⟩
              (wIn cl) ?_ ?_⟩
            · have hbit := hIn cl hclC
              show (if sat3Bit N cl ⟨0, by omega⟩ (wIn cl).val
                  (by have := (wIn cl).isLt; omega) ∈ Sᶜ
                then probe _ else row E'' _) = true
              rw [if_neg (fun hmemc => (Finset.mem_compl.mp hmemc) hbit),
                hrow_read E'' cl hclC]
              exact decide_eq_true hclE
            · rw [hsign_read E'' cl ⟨0, by omega⟩]
              rfl
          · have hclne : cl ≠ c₀ := fun h => hclE (by rw [h]; exact hmem)
            refine ⟨⟨0, by omega⟩, sat3Lit_true_of_selected N _ _ cl ⟨0, by omega⟩
              (wOut cl) ?_ ?_⟩
            · have hbit := hOut cl hclC
              show (if sat3Bit N cl ⟨0, by omega⟩ (wOut cl).val
                  (by have := (wOut cl).isLt; omega) ∈ Sᶜ
                then probe _ else row E'' _) = true
              rw [if_pos (Finset.mem_compl.mpr hbit), hprobe]
              show decide _ = true
              rw [decide_eq_true_eq]
              exact Or.inl ⟨cl, hclC, hclne, rfl⟩
            · rw [hsign_read E'' cl ⟨0, by omega⟩]
              rfl
        · refine ⟨⟨0, by omega⟩, sat3Lit_true_of_selected N _ _ cl ⟨0, by omega⟩
            ⟨0, hv⟩ ?_ ?_⟩
          · show (if sat3Bit N cl ⟨0, by omega⟩ ((⟨0, hv⟩ : Fin (sat3V N))).val
                (by have := (⟨0, hv⟩ : Fin (sat3V N)).isLt; omega) ∈ Sᶜ
              then probe _ else row E'' _) = true
            by_cases hbS : sat3Bit N cl ⟨0, by omega⟩
                ((⟨0, hv⟩ : Fin (sat3V N))).val
                (by have := (⟨0, hv⟩ : Fin (sat3V N)).isLt; omega) ∈ S
            · rw [if_neg (fun hmemc => (Finset.mem_compl.mp hmemc) hbS), hrow]
              show decide _ = true
              rw [decide_eq_true_eq]
              exact Or.inr ⟨cl, hclC, hbS, rfl⟩
            · rw [if_pos (Finset.mem_compl.mpr hbS), hprobe]
              show decide _ = true
              rw [decide_eq_true_eq]
              exact Or.inr ⟨cl, hclC, hbS, rfl⟩
          · rw [hsign_read E'' cl ⟨0, by omega⟩]
            rfl
      · rw [decide_eq_false hmem]
        apply sat3Family_false_of_empty_clause N _ c₀
        intro t i
        exact hc₀_read E'' hmem t i
    refine ⟨probe, ?_⟩
    rw [hval E, hval E']
    intro heq
    apply hqd
    constructor
    · intro h'
      exact of_decide_eq_true (by rw [← heq]; exact decide_eq_true h')
    · intro h'
      exact of_decide_eq_true (by rw [heq]; exact decide_eq_true h')
  have hcap := cut_row_capacity (sat3Family N) S j hcut Y hdist
  rw [hYcard] at hcap
  by_contra hcon
  push_neg at hcon
  have hlt : (2 : ℕ) ^ j < 2 ^ C.card :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  omega

/-! ### The census and the alignment law -/

set_option maxHeartbeats 800000 in
/-- **The straddle census (proved)**: the number of slot-0-straddling blocks is at most `j`,
unconditionally — at every band. -/
theorem sat3_straddle_census (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j) :
    ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
      (∃ w : Fin (sat3V N), sat3Bit N c ⟨0, by omega⟩ w.val
        (by have := w.isLt; omega) ∈ S)
      ∧ (∃ w : Fin (sat3V N), sat3Bit N c ⟨0, by omega⟩ w.val
        (by have := w.isLt; omega) ∉ S))).card ≤ j := by
  classical
  set uIn : Fin (sat3M N) → Fin (sat3V N) := fun c =>
    if h : ∃ w : Fin (sat3V N), sat3Bit N c ⟨0, by omega⟩ w.val
        (by have := w.isLt; omega) ∈ S
    then h.choose else ⟨0, hv⟩ with huIn
  set uOut : Fin (sat3M N) → Fin (sat3V N) := fun c =>
    if h : ∃ w : Fin (sat3V N), sat3Bit N c ⟨0, by omega⟩ w.val
        (by have := w.isLt; omega) ∉ S
    then h.choose else ⟨0, hv⟩ with huOut
  have hIn : ∀ c ∈ ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
      (∃ w : Fin (sat3V N), sat3Bit N c ⟨0, by omega⟩ w.val
        (by have := w.isLt; omega) ∈ S)
      ∧ (∃ w : Fin (sat3V N), sat3Bit N c ⟨0, by omega⟩ w.val
        (by have := w.isLt; omega) ∉ S))),
      sat3Bit N c ⟨0, by omega⟩ (uIn c).val
        (by have := (uIn c).isLt; omega) ∈ S := by
    intro c hc
    have hex := (Finset.mem_filter.mp hc).2.1
    have hueq : uIn c = hex.choose := by
      rw [huIn]
      show (if h : ∃ w : Fin (sat3V N), sat3Bit N c ⟨0, by omega⟩ w.val
          (by have := w.isLt; omega) ∈ S
        then h.choose else ⟨0, hv⟩) = hex.choose
      rw [dif_pos hex]
    rw [sat3Bit_congr_field N c (uIn c) hex.choose hueq]
    exact hex.choose_spec
  have hOut : ∀ c ∈ ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
      (∃ w : Fin (sat3V N), sat3Bit N c ⟨0, by omega⟩ w.val
        (by have := w.isLt; omega) ∈ S)
      ∧ (∃ w : Fin (sat3V N), sat3Bit N c ⟨0, by omega⟩ w.val
        (by have := w.isLt; omega) ∉ S))),
      sat3Bit N c ⟨0, by omega⟩ (uOut c).val
        (by have := (uOut c).isLt; omega) ∉ S := by
    intro c hc
    have hex := (Finset.mem_filter.mp hc).2.2
    have hueq : uOut c = hex.choose := by
      rw [huOut]
      show (if h : ∃ w : Fin (sat3V N), sat3Bit N c ⟨0, by omega⟩ w.val
          (by have := w.isLt; omega) ∉ S
        then h.choose else ⟨0, hv⟩) = hex.choose
      rw [dif_pos hex]
    rw [sat3Bit_congr_field N c (uOut c) hex.choose hueq]
    exact hex.choose_spec
  exact sat3_straddle_drag N hv hcut _ uIn uOut hIn hOut

/-- **THE ALIGNMENT LAW (proved)**: every balanced cut of a minimal SAT circuit has at most
`coneExcess + 1` slot-0-straddling blocks — balanced cone supports respect block boundaries up
to the cone excess, at EVERY band including the heaviest. -/
theorem sat3_straddle_band (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cc : List (CGate N)) (hcomp : computes cc (sat3Family N))
    (hmin : cc.length = cbudget (sat3Family N))
    (T : ℕ) (hT : 2 ≤ T)
    (hband : 2 * T - 1 ≤ (varsOf cc (cc.length - 1)).card) :
    ∃ S : Finset (Fin N), T ≤ S.card ∧ S.card ≤ 2 * T - 2 ∧
      ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
        (∃ w : Fin (sat3V N), sat3Bit N c ⟨0, by omega⟩ w.val
          (by have := w.isLt; omega) ∈ S)
        ∧ (∃ w : Fin (sat3V N), sat3Bit N c ⟨0, by omega⟩ w.val
          (by have := w.isLt; omega) ∉ S))).card
      ≤ coneExcess cc (cc.length - 1) + 1 := by
  classical
  obtain ⟨S, hT1, hT2, j, hj, hcut⟩ :=
    sat3_balanced_cut N hv hm3 hk cc hcomp hmin T hT hband
  exact ⟨S, hT1, hT2, (sat3_straddle_census N hv hcut).trans hj⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_straddle_drag
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_straddle_census
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_straddle_band
