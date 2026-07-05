import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameBalancedWireCut

/-!
# N-Frame: generalized pins — the row machinery reads arbitrary variable subsets

The pin construction untied from its hardwired `pin j ↔ variable j` coupling: `sat3ContextG` pins
variable `α j` through pin block `j`, for an **arbitrary injective** `α`.  The unpinned-selector
refuge closes: the reading kit can now be placed on any variable.

  `sat3ContextG` + reads — the generalized context; the tautology layer is `α`-independent and the
        pin reads move to `α`-fields.
  `sat3ContextG_probe_eval` — **PROVED, the workhorse**: `f(patch(ctxG α bvec, probe (α j₀) sgn))
        = xor (bvec j₀) sgn` — double forcing at arbitrary pinned variables.
  `sat3ContextG_agree` / `sat3ContextG_designated` / `sat3ContextG_injective` — the support layer.
  `sat3_generalized_pin_drag` — **PROVED, the payoff**: for any `CutFactorization` of SAT over `S`
        with a `j`-bit trace, any block `c`, and any injective `α`: at most `j` pins have their pin
        sign inside `S` while their `α`-selector in block `c` lies outside `S` — cross-block
        sign-to-selector tension at trace strength, with the variable assignment free.

## Honest scope

With `α` free, the drag applies to every (pins-in-`S`, selectors-off-`S`) matching, so a balanced
cut must starve one side of every such matching — the min-form corollary (an injection-extension
construction) and the selector-data families for the all-signs-out regime are the remaining rungs
toward `Ω(m)` rows over a balanced cut.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- The generalized pin context: pin block `j` pins variable `α j` with sign `bvec j`; all other
outside blocks are tautologies; the designated block is empty. -/
def sat3ContextG (N : ℕ) (c : Fin (sat3M N)) {k : ℕ} (hk : k + 1 ≤ sat3M N)
    (α : Fin k → Fin (sat3V N)) (bvec : Fin k → Bool) : Fin N → Bool :=
  fun bit => decide (
    (∃ j : Fin k, bit.val / sat3D N = (sat3PinClause N c hk j).val ∧
      (bit.val % sat3D N = (α j).val ∨ (bit.val % sat3D N = sat3V N ∧ bvec j = false)))
    ∨ (bit.val / sat3D N < sat3M N ∧ bit.val / sat3D N ≠ c.val ∧
      (∀ j : Fin k, bit.val / sat3D N ≠ (sat3PinClause N c hk j).val) ∧
      (bit.val % sat3D N = 0 ∨ bit.val % sat3D N = sat3V N + 1 ∨
        bit.val % sat3D N = sat3V N + 1 + sat3V N)))

/-- `bvec` enters the generalized context only at pin-sign bits. -/
theorem sat3ContextG_agree (N : ℕ) (c : Fin (sat3M N)) {k : ℕ}
    (hk : k + 1 ≤ sat3M N) (α : Fin k → Fin (sat3V N))
    (b b' : Fin k → Bool) (i : Fin N)
    (hag : ∀ j : Fin k, i.val / sat3D N = (sat3PinClause N c hk j).val →
      i.val % sat3D N = sat3V N → b j = b' j) :
    sat3ContextG N c hk α b i = sat3ContextG N c hk α b' i := by
  show decide _ = decide _
  apply decide_eq_decide.mpr
  constructor
  · rintro (⟨j, hj1, hj2 | ⟨hj2, hj3⟩⟩ | hother)
    · exact Or.inl ⟨j, hj1, Or.inl hj2⟩
    · exact Or.inl ⟨j, hj1, Or.inr ⟨hj2, by rw [← hag j hj1 hj2]; exact hj3⟩⟩
    · exact Or.inr hother
  · rintro (⟨j, hj1, hj2 | ⟨hj2, hj3⟩⟩ | hother)
    · exact Or.inl ⟨j, hj1, Or.inl hj2⟩
    · exact Or.inl ⟨j, hj1, Or.inr ⟨hj2, by rw [hag j hj1 hj2]; exact hj3⟩⟩
    · exact Or.inr hother

/-- The generalized context vanishes on the designated block. -/
theorem sat3ContextG_designated (N : ℕ) (c : Fin (sat3M N)) {k : ℕ}
    (hk : k + 1 ≤ sat3M N) (α : Fin k → Fin (sat3V N)) (b : Fin k → Bool)
    (i : Fin N) (hdiv : i.val / sat3D N = c.val) :
    sat3ContextG N c hk α b i = false := by
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro (⟨j, hj1, -⟩ | ⟨-, hne, -, -⟩)
  · exact sat3PinClause_ne N c hk j (hj1.symm.trans hdiv)
  · exact hne hdiv

/-- The pin-sign read of the generalized context. -/
theorem sat3ContextG_pin_sign (N : ℕ) (c : Fin (sat3M N)) {k : ℕ}
    (hk : k + 1 ≤ sat3M N) (hkv : k ≤ sat3V N) (α : Fin k → Fin (sat3V N))
    (b : Fin k → Bool) (j : Fin k) :
    sat3ContextG N c hk α b
      (sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N) (by omega))
      = decide (b j = false) := by
  have hd := sat3Bit_clause N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N) (by omega)
  have hr : (sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N)
      (by omega)).val % sat3D N = sat3V N := by
    rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N
    omega
  cases hbj : b j
  · show decide _ = true
    rw [decide_eq_true_eq]
    left
    exact ⟨j, hd, Or.inr ⟨hr, hbj⟩⟩
  · show decide _ = false
    rw [decide_eq_false_iff_not]
    rintro (⟨j', hdiv, hrem⟩ | ⟨-, -, hnot, -⟩)
    · rw [hd] at hdiv
      have hjj' := sat3PinClause_val_inj N c hk hdiv
      subst hjj'
      rcases hrem with h | ⟨-, hbf⟩
      · rw [hr] at h
        have := (α j).isLt
        omega
      · rw [hbj] at hbf
        exact Bool.noConfusion hbf
    · exact hnot j hd

/-- Distinct sign vectors give distinct generalized contexts. -/
theorem sat3ContextG_injective (N : ℕ) (c : Fin (sat3M N)) {k : ℕ}
    (hk : k + 1 ≤ sat3M N) (hkv : k ≤ sat3V N) (α : Fin k → Fin (sat3V N)) :
    Function.Injective (fun bvec : Fin k → Bool => sat3ContextG N c hk α bvec) := by
  intro b b' heq
  funext j
  have heq' : sat3ContextG N c hk α b = sat3ContextG N c hk α b' := heq
  have h := congrFun heq'
    (sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N) (by omega))
  rw [sat3ContextG_pin_sign N c hk hkv α b j,
    sat3ContextG_pin_sign N c hk hkv α b' j] at h
  cases hb : b j <;> cases hb' : b' j
  · rfl
  · rw [hb, hb'] at h
    exact Bool.noConfusion h
  · rw [hb, hb'] at h
    exact Bool.noConfusion h
  · rfl

set_option maxHeartbeats 1600000 in
/-- **THE GENERALIZED-PIN WORKHORSE (proved)**: the probe on variable `α j₀` reads the pin apart —
double forcing at arbitrary pinned variables. -/
theorem sat3ContextG_probe_eval (N : ℕ) (hv : 1 ≤ sat3V N) {k : ℕ}
    (hk : k + 1 ≤ sat3M N) (hkv : k ≤ sat3V N) (c : Fin (sat3M N))
    (α : Fin k → Fin (sat3V N)) (hα : Function.Injective α)
    (bvec : Fin k → Bool) (j₀ : Fin k) (sgn : Bool) :
    sat3Family N (sat3Patch N c (sat3ContextG N c hk α bvec)
      (sat3Probe N (α j₀) sgn)) = xor (bvec j₀) sgn := by
  classical
  have hDpos : 0 < sat3D N := sat3D_pos N
  set y : Fin N → Bool := sat3ContextG N c hk α bvec with hy
  set u : Fin N → Bool := sat3Probe N (α j₀) sgn with hu
  have hσne : ∀ j : Fin k, sat3PinClause N c hk j ≠ c :=
    fun j h => sat3PinClause_ne N c hk j (congrArg Fin.val h)
  -- pin-clause reads
  have hpin_sel : ∀ j : Fin k,
      sat3Patch N c y u (sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (α j).val
        (by have := (α j).isLt; omega)) = true := by
    intro j
    rw [sat3Patch_out N c y u _ (hσne j)]
    show decide _ = true
    rw [decide_eq_true_eq]
    left
    refine ⟨j, sat3Bit_clause N (sat3PinClause N c hk j) ⟨0, by omega⟩ (α j).val
      (by have := (α j).isLt; omega), Or.inl ?_⟩
    rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + (α j).val = (α j).val
    omega
  have hpin_miss : ∀ (j : Fin k) (i : Fin (sat3V N)), i ≠ α j →
      sat3Patch N c y u (sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ i.val
        (by have := i.isLt; omega)) = false := by
    intro j i hij
    rw [sat3Patch_out N c y u _ (hσne j)]
    have hd := sat3Bit_clause N (sat3PinClause N c hk j) ⟨0, by omega⟩ i.val
      (by have := i.isLt; omega)
    have hr : (sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ i.val
        (by have := i.isLt; omega)).val % sat3D N = i.val := by
      rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + i.val = i.val
      omega
    show decide _ = false
    rw [decide_eq_false_iff_not]
    rintro (⟨j', hdiv, hrem⟩ | ⟨-, -, hnot, -⟩)
    · rw [hd] at hdiv
      have hjj' := sat3PinClause_val_inj N c hk hdiv
      subst hjj'
      rcases hrem with h | ⟨h, -⟩
      · rw [hr] at h
        exact hij (Fin.ext h)
      · rw [hr] at h
        have := i.isLt
        omega
    · exact hnot j hd
  have hpin_sign : ∀ j : Fin k,
      sat3Patch N c y u (sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N)
        (by omega)) = decide (bvec j = false) := by
    intro j
    rw [sat3Patch_out N c y u _ (hσne j)]
    exact sat3ContextG_pin_sign N c hk hkv α bvec j
  have hpin_dead : ∀ (j : Fin k) (t : Fin 3), 1 ≤ t.val → ∀ i : Fin (sat3V N),
      sat3Patch N c y u (sat3Bit N (sat3PinClause N c hk j) t i.val
        (by have := i.isLt; omega)) = false := by
    intro j t ht i
    rw [sat3Patch_out N c y u _ (hσne j)]
    have hd := sat3Bit_clause N (sat3PinClause N c hk j) t i.val (by have := i.isLt; omega)
    have hr := sat3Bit_rem N (sat3PinClause N c hk j) t i.val (by have := i.isLt; omega)
    have hbound : sat3V N + 1 ≤ t.val * (sat3V N + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    show decide _ = false
    rw [decide_eq_false_iff_not]
    rintro (⟨j', hdiv, hrem⟩ | ⟨-, -, hnot, -⟩)
    · have hj' := (α j').isLt
      rcases hrem with h | ⟨h, -⟩ <;> rw [hr] at h <;> omega
    · exact hnot j hd
  -- tautology-clause reads (α-independent)
  have htaut_sel0 : ∀ cl : Fin (sat3M N), cl ≠ c →
      (∀ j : Fin k, cl.val ≠ (sat3PinClause N c hk j).val) →
      sat3Patch N c y u (sat3Bit N cl ⟨0, by omega⟩ 0 (by omega)) = true := by
    intro cl hclc hnp
    rw [sat3Patch_out N c y u cl hclc]
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
    · rw [hd]
      exact fun hh => hclc (Fin.ext hh)
    · intro j'
      rw [hd]
      exact hnp j'
  have htaut_miss0 : ∀ cl : Fin (sat3M N), cl ≠ c →
      (∀ j : Fin k, cl.val ≠ (sat3PinClause N c hk j).val) →
      ∀ i : Fin (sat3V N), i ≠ (⟨0, hv⟩ : Fin (sat3V N)) →
      sat3Patch N c y u (sat3Bit N cl ⟨0, by omega⟩ i.val (by have := i.isLt; omega))
        = false := by
    intro cl hclc hnp i hij
    rw [sat3Patch_out N c y u cl hclc]
    have hd := sat3Bit_clause N cl ⟨0, by omega⟩ i.val (by have := i.isLt; omega)
    have hr : (sat3Bit N cl ⟨0, by omega⟩ i.val (by have := i.isLt; omega)).val % sat3D N
        = i.val := by
      rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + i.val = i.val
      omega
    show decide _ = false
    rw [decide_eq_false_iff_not]
    rintro (⟨j', hdiv, -⟩ | ⟨-, -, -, hpat⟩)
    · rw [hd] at hdiv
      exact hnp j' hdiv
    · rw [hr] at hpat
      have hilt := i.isLt
      rcases hpat with h | h | h
      · exact hij (Fin.ext h)
      · omega
      · omega
  have htaut_sign0 : ∀ cl : Fin (sat3M N), cl ≠ c →
      (∀ j : Fin k, cl.val ≠ (sat3PinClause N c hk j).val) →
      sat3Patch N c y u (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)) = false := by
    intro cl hclc hnp
    rw [sat3Patch_out N c y u cl hclc]
    have hd := sat3Bit_clause N cl ⟨0, by omega⟩ (sat3V N) (by omega)
    have hr : (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)).val % sat3D N
        = sat3V N := by
      rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N
      omega
    show decide _ = false
    rw [decide_eq_false_iff_not]
    rintro (⟨j', hdiv, -⟩ | ⟨-, -, -, hpat⟩)
    · rw [hd] at hdiv
      exact hnp j' hdiv
    · rw [hr] at hpat
      rcases hpat with h | h | h <;> omega
  have htaut_sel1 : ∀ cl : Fin (sat3M N), cl ≠ c →
      (∀ j : Fin k, cl.val ≠ (sat3PinClause N c hk j).val) →
      sat3Patch N c y u (sat3Bit N cl ⟨1, by omega⟩ 0 (by omega)) = true := by
    intro cl hclc hnp
    rw [sat3Patch_out N c y u cl hclc]
    have hd := sat3Bit_clause N cl ⟨1, by omega⟩ 0 (by omega)
    have hr : (sat3Bit N cl ⟨1, by omega⟩ 0 (by omega)).val % sat3D N = sat3V N + 1 := by
      rw [sat3Bit_rem]
      show (1 : ℕ) * (sat3V N + 1) + 0 = sat3V N + 1
      omega
    show decide _ = true
    rw [decide_eq_true_eq]
    right
    refine ⟨?_, ?_, ?_, Or.inr (Or.inl hr)⟩
    · rw [hd]
      exact cl.isLt
    · rw [hd]
      exact fun hh => hclc (Fin.ext hh)
    · intro j'
      rw [hd]
      exact hnp j'
  have htaut_miss1 : ∀ cl : Fin (sat3M N), cl ≠ c →
      (∀ j : Fin k, cl.val ≠ (sat3PinClause N c hk j).val) →
      ∀ i : Fin (sat3V N), i ≠ (⟨0, hv⟩ : Fin (sat3V N)) →
      sat3Patch N c y u (sat3Bit N cl ⟨1, by omega⟩ i.val (by have := i.isLt; omega))
        = false := by
    intro cl hclc hnp i hij
    rw [sat3Patch_out N c y u cl hclc]
    have hd := sat3Bit_clause N cl ⟨1, by omega⟩ i.val (by have := i.isLt; omega)
    have hr : (sat3Bit N cl ⟨1, by omega⟩ i.val (by have := i.isLt; omega)).val % sat3D N
        = sat3V N + 1 + i.val := by
      rw [sat3Bit_rem]
      show (1 : ℕ) * (sat3V N + 1) + i.val = sat3V N + 1 + i.val
      omega
    show decide _ = false
    rw [decide_eq_false_iff_not]
    rintro (⟨j', hdiv, -⟩ | ⟨-, -, -, hpat⟩)
    · rw [hd] at hdiv
      exact hnp j' hdiv
    · rw [hr] at hpat
      have hilt := i.isLt
      rcases hpat with h | h | h
      · omega
      · have h0 : i.val = 0 := by omega
        exact hij (Fin.ext h0)
      · omega
  have htaut_sign1 : ∀ cl : Fin (sat3M N), cl ≠ c →
      (∀ j : Fin k, cl.val ≠ (sat3PinClause N c hk j).val) →
      sat3Patch N c y u (sat3Bit N cl ⟨1, by omega⟩ (sat3V N) (by omega)) = true := by
    intro cl hclc hnp
    rw [sat3Patch_out N c y u cl hclc]
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
    · rw [hd]
      exact fun hh => hclc (Fin.ext hh)
    · intro j'
      rw [hd]
      exact hnp j'
  -- probe reads (block c)
  have hprobe_sel :
      sat3Patch N c y u (sat3Bit N c ⟨0, by omega⟩ (α j₀).val
        (by have := (α j₀).isLt; omega)) = true := by
    rw [sat3Patch_own N c y u]
    show decide _ = true
    rw [decide_eq_true_eq]
    left
    rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + (α j₀).val = (α j₀).val
    omega
  have hprobe_miss : ∀ i : Fin (sat3V N), i ≠ α j₀ →
      sat3Patch N c y u (sat3Bit N c ⟨0, by omega⟩ i.val (by have := i.isLt; omega))
        = false := by
    intro i hi
    rw [sat3Patch_own N c y u]
    have hr : (sat3Bit N c ⟨0, by omega⟩ i.val (by have := i.isLt; omega)).val % sat3D N
        = i.val := by
      rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + i.val = i.val
      omega
    show decide _ = false
    rw [decide_eq_false_iff_not]
    rintro (h | ⟨h, -⟩)
    · rw [hr] at h
      exact hi (Fin.ext h)
    · rw [hr] at h
      have := i.isLt
      omega
  have hprobe_sign :
      sat3Patch N c y u (sat3Bit N c ⟨0, by omega⟩ (sat3V N) (by omega)) = sgn := by
    rw [sat3Patch_own N c y u]
    have hr : (sat3Bit N c ⟨0, by omega⟩ (sat3V N) (by omega)).val % sat3D N
        = sat3V N := by
      rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N
      omega
    cases sgn
    · show decide _ = false
      rw [decide_eq_false_iff_not]
      rintro (h | ⟨-, h⟩)
      · rw [hr] at h
        have := (α j₀).isLt
        omega
      · exact Bool.noConfusion h
    · show decide _ = true
      rw [decide_eq_true_eq]
      right
      exact ⟨hr, rfl⟩
  have hprobe_dead : ∀ (t : Fin 3), 1 ≤ t.val → ∀ i : Fin (sat3V N),
      sat3Patch N c y u (sat3Bit N c t i.val (by have := i.isLt; omega)) = false := by
    intro t ht i
    rw [sat3Patch_own N c y u]
    have hr := sat3Bit_rem N c t i.val (by have := i.isLt; omega)
    have hbound : sat3V N + 1 ≤ t.val * (sat3V N + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have hvjlt := (α j₀).isLt
    have hilt := i.isLt
    show decide _ = false
    rw [decide_eq_false_iff_not]
    rintro (h | ⟨h, -⟩) <;> rw [hr] at h <;> omega
  -- clause-level analysis
  have hLit_pin : ∀ (a : Fin (sat3V N) → Bool) (j : Fin k),
      (∃ t, sat3Lit N (sat3Patch N c y u) a (sat3PinClause N c hk j) t = true) ↔
        xor (a (α j)) (decide (bvec j = false)) = true := by
    intro a j
    have hiff := sat3Clause_single_iff N (sat3Patch N c y u) a (sat3PinClause N c hk j)
      (α j) (hpin_sel j) (hpin_miss j)
      (hpin_dead j ⟨1, by omega⟩ (by show (1 : ℕ) ≤ 1; omega))
      (hpin_dead j ⟨2, by omega⟩ (by show (1 : ℕ) ≤ 2; omega))
    rw [hpin_sign j] at hiff
    exact hiff
  have hLit_c : ∀ a : Fin (sat3V N) → Bool,
      (∃ t, sat3Lit N (sat3Patch N c y u) a c t = true) ↔ xor (a (α j₀)) sgn = true := by
    intro a
    have hiff := sat3Clause_single_iff N (sat3Patch N c y u) a c (α j₀)
      hprobe_sel hprobe_miss
      (hprobe_dead ⟨1, by omega⟩ (by show (1 : ℕ) ≤ 1; omega))
      (hprobe_dead ⟨2, by omega⟩ (by show (1 : ℕ) ≤ 2; omega))
    rw [hprobe_sign] at hiff
    exact hiff
  have hLit_taut : ∀ (a : Fin (sat3V N) → Bool) (cl : Fin (sat3M N)), cl ≠ c →
      (∀ j : Fin k, cl.val ≠ (sat3PinClause N c hk j).val) →
      ∃ t, sat3Lit N (sat3Patch N c y u) a cl t = true := by
    intro a cl hclc hnp
    cases ha : a ⟨0, hv⟩
    · refine ⟨⟨1, by omega⟩, ?_⟩
      rw [sat3Lit_single N (sat3Patch N c y u) a cl ⟨1, by omega⟩ ⟨0, hv⟩
        (htaut_sel1 cl hclc hnp) (htaut_miss1 cl hclc hnp),
        htaut_sign1 cl hclc hnp, Bool.xor_true, ha]
      rfl
    · refine ⟨⟨0, by omega⟩, ?_⟩
      rw [sat3Lit_single N (sat3Patch N c y u) a cl ⟨0, by omega⟩ ⟨0, hv⟩
        (htaut_sel0 cl hclc hnp) (htaut_miss0 cl hclc hnp),
        htaut_sign0 cl hclc hnp, Bool.xor_false, ha]
  -- final assembly
  cases hxor : xor (bvec j₀) sgn
  · -- refutation
    cases hfam : sat3Family N (sat3Patch N c y u)
    · rfl
    · exfalso
      obtain ⟨a, ha⟩ := (sat3Family_iff N _).mp hfam
      have hpin := (hLit_pin a j₀).mp
        (sat3Eval_clause_true N _ a ha (sat3PinClause N c hk j₀))
      have hcc := (hLit_c a).mp (sat3Eval_clause_true N _ a ha c)
      have haj : a (α j₀) = bvec j₀ := xor_decide_eq _ _ hpin
      rw [haj, hxor] at hcc
      exact Bool.noConfusion hcc
  · -- construction: the pinned assignment satisfies everything
    set awit : Fin (sat3V N) → Bool :=
      fun i => if h : ∃ j : Fin k, α j = i then bvec (Classical.choose h) else true
      with hawit
    have hawit_at : ∀ j : Fin k, awit (α j) = bvec j := by
      intro j
      show (if h : ∃ j' : Fin k, α j' = α j then bvec (Classical.choose h) else true)
        = bvec j
      have hex : ∃ j' : Fin k, α j' = α j := ⟨j, rfl⟩
      rw [dif_pos hex]
      exact congrArg bvec (hα (Classical.choose_spec hex))
    rw [sat3Family_iff]
    refine ⟨awit, sat3Eval_true_of_all N _ awit ?_⟩
    intro cl
    by_cases hclc : cl = c
    · rw [hclc]
      refine (hLit_c awit).mpr ?_
      rw [hawit_at j₀]
      exact hxor
    · by_cases hpin : ∃ j : Fin k, sat3PinClause N c hk j = cl
      · obtain ⟨j, rfl⟩ := hpin
        refine (hLit_pin awit j).mpr ?_
        rw [hawit_at j]
        cases bvec j <;> rfl
      · exact hLit_taut awit cl hclc (fun j h => hpin ⟨j, Fin.ext h.symm⟩)

set_option maxHeartbeats 1600000 in
/-- **THE GENERALIZED PIN DRAG (proved)**: over any cut factorization of SAT, for every block and
every injective variable assignment, at most `j` pins have their pin sign inside `S` while their
assigned selector in the block lies outside `S`. -/
theorem sat3_generalized_pin_drag (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (c : Fin (sat3M N)) (α : Fin (sat3M N - 2) → Fin (sat3V N))
    (hα : Function.Injective α) :
    ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
      sat3Bit N (sat3PinClause N c hk p) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∈ S ∧
      sat3Bit N c ⟨0, by omega⟩ (α p).val
        (by have := (α p).isLt; omega) ∉ S)).card ≤ j := by
  classical
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  set Jf := (Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
    sat3Bit N (sat3PinClause N c hk p) ⟨0, by omega⟩ (sat3V N)
      (by omega) ∈ S ∧
    sat3Bit N c ⟨0, by omega⟩ (α p).val
      (by have := (α p).isLt; omega) ∉ S) with hJf
  set e : (↥Jf → Bool) → (Fin (sat3M N - 2) → Bool) :=
    fun bb p => if hmem : p ∈ Jf then bb ⟨p, hmem⟩ else false with he
  have heval : ∀ (bb : ↥Jf → Bool) (w : ↥Jf), e bb w.val = bb w := by
    intro bb w
    show (if hmem : w.val ∈ Jf then bb ⟨w.val, hmem⟩ else false) = bb w
    rw [dif_pos w.prop, Subtype.coe_eta]
  have heinj : Function.Injective e := by
    intro bb bb' heq
    funext w
    rw [← heval bb w, ← heval bb' w, heq]
  set Y : Finset (Fin N → Bool) :=
    Finset.univ.image (fun bb : ↥Jf → Bool => sat3ContextG N c hk α (e bb)) with hY
  have hYcard : Y.card = 2 ^ Jf.card := by
    rw [hY, Finset.card_image_of_injective _
        (fun bb bb' heq => heinj (sat3ContextG_injective N c hk hkv α heq)),
      Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_bool]
  have hdist : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' →
      ∃ x, sat3Family N (mixOn Sᶜ x y) ≠ sat3Family N (mixOn Sᶜ x y') := by
    intro y hy y' hy' hne
    rw [hY] at hy hy'
    obtain ⟨bb, -, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨bb', -, rfl⟩ := Finset.mem_image.mp hy'
    have hbne : e bb ≠ e bb' := fun hh' => hne (by rw [hh'])
    obtain ⟨p₀, hp₀ne⟩ := Function.ne_iff.mp hbne
    have hp₀J : p₀ ∈ Jf := by
      by_contra hmem
      apply hp₀ne
      show (if hm : p₀ ∈ Jf then bb ⟨p₀, hm⟩ else false)
        = (if hm : p₀ ∈ Jf then bb' ⟨p₀, hm⟩ else false)
      rw [dif_neg hmem, dif_neg hmem]
    have hp₀mem := Finset.mem_filter.mp (hJf ▸ hp₀J)
    have hselJ := hp₀mem.2.2
    set uu := sat3Probe N (α p₀) false with huudef
    -- the probe is live only at the assigned selector, which lies off S
    have hprobe0 : ∀ i : Fin N, i.val / sat3D N = c.val → i ∈ S →
        uu i = false := by
      intro i hdiv hi
      rw [huudef]
      show decide _ = false
      rw [decide_eq_false_iff_not]
      rintro (hsel | ⟨-, hcon⟩)
      · apply hselJ
        have hiπ : sat3Bit N c ⟨0, by omega⟩ (α p₀).val
            (by have := (α p₀).isLt; omega) = i := by
          apply Fin.ext
          show c.val * sat3D N + 0 * (sat3V N + 1) + (α p₀).val = i.val
          have hdm := Nat.div_add_mod i.val (sat3D N)
          rw [hdiv, hsel] at hdm
          have hcm : sat3D N * c.val = c.val * sat3D N := Nat.mul_comm _ _
          omega
        rw [hiπ]
        exact hi
      · exact Bool.noConfusion hcon
    have hagree : ∀ i : Fin N, i ∉ S →
        sat3ContextG N c hk α (e bb) i = sat3ContextG N c hk α (e bb') i := by
      intro i hi
      apply sat3ContextG_agree
      intro p hp1 hp2
      by_cases hmem : p ∈ Jf
      · exfalso
        have hπ := (Finset.mem_filter.mp (hJf ▸ hmem)).2.1
        apply hi
        have hiπ : sat3Bit N (sat3PinClause N c hk p) ⟨0, by omega⟩ (sat3V N)
            (by omega) = i := by
          apply Fin.ext
          show (sat3PinClause N c hk p).val * sat3D N + 0 * (sat3V N + 1)
            + sat3V N = i.val
          have hdm := Nat.div_add_mod i.val (sat3D N)
          rw [hp1, hp2] at hdm
          have hcm : sat3D N * (sat3PinClause N c hk p).val
              = (sat3PinClause N c hk p).val * sat3D N := Nat.mul_comm _ _
          omega
        rw [← hiπ]
        exact hπ
      · show (if hm : p ∈ Jf then bb ⟨p, hm⟩ else false)
          = (if hm : p ∈ Jf then bb' ⟨p, hm⟩ else false)
        rw [dif_neg hmem, dif_neg hmem]
    refine ⟨sat3Patch N c (sat3ContextG N c hk α (e bb)) uu, ?_⟩
    have hmix1 : mixOn Sᶜ (sat3Patch N c (sat3ContextG N c hk α (e bb)) uu)
        (sat3ContextG N c hk α (e bb))
        = sat3Patch N c (sat3ContextG N c hk α (e bb)) uu := by
      funext i
      show (if i ∈ Sᶜ then sat3Patch N c (sat3ContextG N c hk α (e bb)) uu i
        else sat3ContextG N c hk α (e bb) i)
        = sat3Patch N c (sat3ContextG N c hk α (e bb)) uu i
      by_cases hi : i ∈ Sᶜ
      · rw [if_pos hi]
      · rw [if_neg hi]
        have hiS : i ∈ S := by
          by_contra hiS
          exact hi (Finset.mem_compl.mpr hiS)
        show sat3ContextG N c hk α (e bb) i
          = (if i.val / sat3D N = c.val then uu i
            else sat3ContextG N c hk α (e bb) i)
        by_cases hdiv : i.val / sat3D N = c.val
        · rw [if_pos hdiv, sat3ContextG_designated N c hk α (e bb) i hdiv,
            hprobe0 i hdiv hiS]
        · rw [if_neg hdiv]
    have hmix2 : mixOn Sᶜ (sat3Patch N c (sat3ContextG N c hk α (e bb)) uu)
        (sat3ContextG N c hk α (e bb'))
        = sat3Patch N c (sat3ContextG N c hk α (e bb')) uu := by
      funext i
      show (if i ∈ Sᶜ then sat3Patch N c (sat3ContextG N c hk α (e bb)) uu i
        else sat3ContextG N c hk α (e bb') i)
        = sat3Patch N c (sat3ContextG N c hk α (e bb')) uu i
      by_cases hi : i ∈ Sᶜ
      · rw [if_pos hi]
        have hiNS : i ∉ S := Finset.mem_compl.mp hi
        show (if i.val / sat3D N = c.val then uu i
            else sat3ContextG N c hk α (e bb) i)
          = (if i.val / sat3D N = c.val then uu i
            else sat3ContextG N c hk α (e bb') i)
        by_cases hdiv : i.val / sat3D N = c.val
        · rw [if_pos hdiv, if_pos hdiv]
        · rw [if_neg hdiv, if_neg hdiv]
          exact hagree i hiNS
      · rw [if_neg hi]
        have hiS : i ∈ S := by
          by_contra hiS
          exact hi (Finset.mem_compl.mpr hiS)
        show sat3ContextG N c hk α (e bb') i
          = (if i.val / sat3D N = c.val then uu i
            else sat3ContextG N c hk α (e bb') i)
        by_cases hdiv : i.val / sat3D N = c.val
        · rw [if_pos hdiv, sat3ContextG_designated N c hk α (e bb') i hdiv,
            hprobe0 i hdiv hiS]
        · rw [if_neg hdiv]
    rw [hmix1, hmix2, huudef,
      sat3ContextG_probe_eval N hv hk hkv c α hα (e bb) p₀ false,
      sat3ContextG_probe_eval N hv hk hkv c α hα (e bb') p₀ false]
    intro heq
    exact hp₀ne (xor_left_inj _ _ _ heq)
  have hcap := cut_row_capacity (sat3Family N) S j hcut Y hdist
  rw [hYcard] at hcap
  by_contra hcon
  push_neg at hcon
  have hlt : (2 : ℕ) ^ j < 2 ^ Jf.card :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3ContextG_probe_eval
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_generalized_pin_drag
