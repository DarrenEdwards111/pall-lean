import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSATSquare
import Mathlib.Data.Fintype.BigOperators

/-!
# N-Frame: the per-block subfunction count for SAT — the discriminating quantity

The blockwise tear count alone does not separate SAT from majority.  This file proves the quantity that does the
discriminating work in a Nečiporuk-shape argument: **every clause block of `sat3Family` carries exponentially many
distinct subfunctions** as the outside context varies.

**Construction.**  A context is built from three kinds of clauses outside the chosen block `c`:
  * **pinning clauses** `σ j` (the clause list with `c` skipped): clause `σ j` has a single live selector on variable
    `j` in slot 0 with sign `¬(bvec j)` — it is satisfied by an assignment `a` **iff `a j = bvec j`**;
  * **tautology fillers**: slot 0 encodes `a₀`, slot 1 encodes `¬a₀` — satisfied by every assignment;
  * the block `c` itself is overridden by the probe, a single-literal clause on a pinned variable.

The workhorse identity `sat3Context_probe_eval` computes the subfunction value *exactly*: probing pinned variable `j₀`
with sign `sgn` returns `xor (bvec j₀) sgn`.  Hence contexts with different pin vectors give **different**
subfunctions, read apart by a one-literal probe.

  `sat3Context_probe_eval` — **PROVED, the workhorse**: the subfunction value at the probe is `xor (bvec j₀) sgn`.
  `sat3_block_subfunctions_distinct` — **PROVED**: different pin vectors ⇒ distinct subfunctions on block `c`.
  `sat3_block_subfunction_count` — **PROVED, the count**: block `c` carries **exactly `2^k`** distinct subfunctions
        from `k`-variable pin contexts (`k + 1 ≤ m`, `k ≤ v`).
  `sat3M_pred_le_sat3V` — **PROVED**: the layout always admits `k = sat3M N − 1` (since `m·D ≤ N < (v+1)²`).
  `sat3_block_subfunction_count_pred` — **PROVED, the concrete headline**: every block carries at least
        `2^(sat3M N − 1) ≈ 2^(√N/3)` distinct subfunctions.

## Honest scope

This is the Nečiporuk counting substrate: summed over the `m` blocks it gives `m·(m−1) ≈ N/9` bits of subfunction
information, and each block's subfunctions need `≥ m−1` bits to index.  What remains **open** — and is *not* claimed —
is the cost interface: that a dimension-3 transducer of volume `V` can only realise `g(V)` distinct subfunctions per
block (the width-3 class decomposition).  Without it, no volume lower bound follows.  Nothing here is `NEXP ⊄ ACC⁰`
or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The patch, pin-clause embedding, context, and probe -/

/-- Override block `c` of the context `y` by the probe `u`. -/
def sat3Patch (N : ℕ) (c : Fin (sat3M N)) (y u : Fin N → Bool) : Fin N → Bool :=
  fun b => if b.val / sat3D N = c.val then u b else y b

theorem sat3Patch_out (N : ℕ) (c : Fin (sat3M N)) (y u : Fin N → Bool)
    (cl : Fin (sat3M N)) (hcl : cl ≠ c) (t : Fin 3) (f : ℕ) (hf : f < sat3V N + 1) :
    sat3Patch N c y u (sat3Bit N cl t f hf) = y (sat3Bit N cl t f hf) := by
  show (if (sat3Bit N cl t f hf).val / sat3D N = c.val
      then u (sat3Bit N cl t f hf) else y (sat3Bit N cl t f hf)) = y (sat3Bit N cl t f hf)
  rw [sat3Bit_clause]
  exact if_neg (fun h => hcl (Fin.ext h))

theorem sat3Patch_own (N : ℕ) (c : Fin (sat3M N)) (y u : Fin N → Bool)
    (t : Fin 3) (f : ℕ) (hf : f < sat3V N + 1) :
    sat3Patch N c y u (sat3Bit N c t f hf) = u (sat3Bit N c t f hf) := by
  show (if (sat3Bit N c t f hf).val / sat3D N = c.val
      then u (sat3Bit N c t f hf) else y (sat3Bit N c t f hf)) = u (sat3Bit N c t f hf)
  rw [sat3Bit_clause]
  exact if_pos rfl

/-- The `j`-th pinning clause: the clause list with block `c` skipped. -/
def sat3PinClause (N : ℕ) (c : Fin (sat3M N)) {k : ℕ} (hk : k + 1 ≤ sat3M N)
    (j : Fin k) : Fin (sat3M N) :=
  if j.val < c.val then ⟨j.val, by have := j.isLt; omega⟩
  else ⟨j.val + 1, by have := j.isLt; omega⟩

theorem sat3PinClause_val (N : ℕ) (c : Fin (sat3M N)) {k : ℕ} (hk : k + 1 ≤ sat3M N)
    (j : Fin k) :
    (sat3PinClause N c hk j).val = if j.val < c.val then j.val else j.val + 1 := by
  unfold sat3PinClause
  by_cases h : j.val < c.val
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem sat3PinClause_ne (N : ℕ) (c : Fin (sat3M N)) {k : ℕ} (hk : k + 1 ≤ sat3M N)
    (j : Fin k) : (sat3PinClause N c hk j).val ≠ c.val := by
  rw [sat3PinClause_val]
  by_cases h : j.val < c.val
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    omega

theorem sat3PinClause_val_inj (N : ℕ) (c : Fin (sat3M N)) {k : ℕ} (hk : k + 1 ≤ sat3M N)
    {j j' : Fin k} (h : (sat3PinClause N c hk j).val = (sat3PinClause N c hk j').val) :
    j = j' := by
  rw [sat3PinClause_val, sat3PinClause_val] at h
  apply Fin.ext
  split_ifs at h <;> omega

/-- The pin context: pinning clauses force `a j = bvec j`, all other outside clauses are tautologies, block `c` is
left empty (it is overridden by the probe anyway). -/
def sat3Context (N : ℕ) (c : Fin (sat3M N)) {k : ℕ} (hk : k + 1 ≤ sat3M N)
    (bvec : Fin k → Bool) : Fin N → Bool :=
  fun bit => decide (
    (∃ j : Fin k, bit.val / sat3D N = (sat3PinClause N c hk j).val ∧
      (bit.val % sat3D N = j.val ∨ (bit.val % sat3D N = sat3V N ∧ bvec j = false)))
    ∨ (bit.val / sat3D N < sat3M N ∧ bit.val / sat3D N ≠ c.val ∧
      (∀ j : Fin k, bit.val / sat3D N ≠ (sat3PinClause N c hk j).val) ∧
      (bit.val % sat3D N = 0 ∨ bit.val % sat3D N = sat3V N + 1 ∨
        bit.val % sat3D N = sat3V N + 1 + sat3V N)))

/-- The probe: a single-literal clause on variable `vj` with sign `sgn`, laid out in whatever block reads it. -/
def sat3Probe (N : ℕ) (vj : Fin (sat3V N)) (sgn : Bool) : Fin N → Bool :=
  fun bit => decide (bit.val % sat3D N = vj.val ∨ (bit.val % sat3D N = sat3V N ∧ sgn = true))

/-! ### Generic clause-analysis helpers -/

/-- Destructor: a satisfied instance satisfies every clause in some slot. -/
theorem sat3Eval_clause_true (N : ℕ) (x : Fin N → Bool) (a : Fin (sat3V N) → Bool)
    (h : sat3Eval N x a = true) (cl : Fin (sat3M N)) :
    ∃ t, sat3Lit N x a cl t = true := by
  have hall := List.all_eq_true.mp h cl (List.mem_finRange cl)
  obtain ⟨t, -, ht⟩ := List.any_eq_true.mp hall
  exact ⟨t, ht⟩

/-- A clause with slots 1, 2 empty and a single live slot-0 selector on `j` is satisfied iff the literal
`a j ⊕ sign` holds. -/
theorem sat3Clause_single_iff (N : ℕ) (x : Fin N → Bool) (a : Fin (sat3V N) → Bool)
    (cl : Fin (sat3M N)) (j : Fin (sat3V N))
    (hj : x (sat3Bit N cl ⟨0, by omega⟩ j.val (by have := j.isLt; omega)) = true)
    (hothers : ∀ i : Fin (sat3V N), i ≠ j →
      x (sat3Bit N cl ⟨0, by omega⟩ i.val (by have := i.isLt; omega)) = false)
    (hdead1 : ∀ i : Fin (sat3V N),
      x (sat3Bit N cl ⟨1, by omega⟩ i.val (by have := i.isLt; omega)) = false)
    (hdead2 : ∀ i : Fin (sat3V N),
      x (sat3Bit N cl ⟨2, by omega⟩ i.val (by have := i.isLt; omega)) = false) :
    (∃ t, sat3Lit N x a cl t = true) ↔
      xor (a j) (x (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega))) = true := by
  constructor
  · rintro ⟨t, ht⟩
    rcases t with ⟨tv, htv⟩
    interval_cases tv
    · rwa [sat3Lit_single N x a cl _ j hj hothers] at ht
    · rw [sat3Lit_false_of_empty N x a cl _ hdead1] at ht
      exact Bool.noConfusion ht
    · rw [sat3Lit_false_of_empty N x a cl _ hdead2] at ht
      exact Bool.noConfusion ht
  · intro h
    refine ⟨⟨0, by omega⟩, ?_⟩
    rw [sat3Lit_single N x a cl ⟨0, by omega⟩ j hj hothers]
    exact h

/-- Boolean helper: `u ⊕ decide (w = false) = true` forces `u = w`. -/
theorem xor_decide_eq (u w : Bool) (h : xor u (decide (w = false)) = true) : u = w := by
  cases u <;> cases w <;> revert h <;> decide

/-! ### The workhorse: the subfunction value at the probe -/

/-- **The workhorse (proved)**: under the pin context `bvec`, probing block `c` with a single literal on pinned
variable `j₀` with sign `sgn` evaluates the whole instance to exactly `xor (bvec j₀) sgn`. -/
theorem sat3Context_probe_eval (N : ℕ) (hv : 1 ≤ sat3V N) {k : ℕ}
    (hk : k + 1 ≤ sat3M N) (hkv : k ≤ sat3V N) (c : Fin (sat3M N))
    (bvec : Fin k → Bool) (j₀ : Fin k) (vj : Fin (sat3V N)) (hvj : vj.val = j₀.val)
    (sgn : Bool) :
    sat3Family N (sat3Patch N c (sat3Context N c hk bvec) (sat3Probe N vj sgn))
      = xor (bvec j₀) sgn := by
  have hDpos : 0 < sat3D N := sat3D_pos N
  set y : Fin N → Bool := sat3Context N c hk bvec with hy
  set u : Fin N → Bool := sat3Probe N vj sgn with hu
  have hσne : ∀ j : Fin k, sat3PinClause N c hk j ≠ c :=
    fun j h => sat3PinClause_ne N c hk j (congrArg Fin.val h)
  -- pin-clause reads
  have hpin_sel : ∀ j : Fin k,
      sat3Patch N c y u (sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ j.val
        (by have := j.isLt; omega)) = true := by
    intro j
    rw [sat3Patch_out N c y u _ (hσne j)]
    show decide _ = true
    rw [decide_eq_true_eq]
    left
    refine ⟨j, sat3Bit_clause N (sat3PinClause N c hk j) ⟨0, by omega⟩ j.val
      (by have := j.isLt; omega), Or.inl ?_⟩
    rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + j.val = j.val
    omega
  have hpin_miss : ∀ (j : Fin k) (i : Fin (sat3V N)),
      i ≠ (⟨j.val, by have := j.isLt; omega⟩ : Fin (sat3V N)) →
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
    have hd := sat3Bit_clause N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N) (by omega)
    have hr : (sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N)
        (by omega)).val % sat3D N = sat3V N := by
      rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N
      omega
    cases hbj : bvec j
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
          have := j.isLt
          omega
        · rw [hbj] at hbf
          exact Bool.noConfusion hbf
      · exact hnot j hd
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
    · have hj' := j'.isLt
      rcases hrem with h | ⟨h, -⟩ <;> rw [hr] at h <;> omega
    · exact hnot j hd
  -- tautology-clause reads
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
      sat3Patch N c y u (sat3Bit N c ⟨0, by omega⟩ vj.val (by have := vj.isLt; omega))
        = true := by
    rw [sat3Patch_own N c y u]
    show decide _ = true
    rw [decide_eq_true_eq]
    left
    rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + vj.val = vj.val
    omega
  have hprobe_miss : ∀ i : Fin (sat3V N), i ≠ vj →
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
        have := vj.isLt
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
    have hvjlt := vj.isLt
    have hilt := i.isLt
    show decide _ = false
    rw [decide_eq_false_iff_not]
    rintro (h | ⟨h, -⟩) <;> rw [hr] at h <;> omega
  -- clause-level analysis
  have hLit_pin : ∀ (a : Fin (sat3V N) → Bool) (j : Fin k),
      (∃ t, sat3Lit N (sat3Patch N c y u) a (sat3PinClause N c hk j) t = true) ↔
        xor (a ⟨j.val, by have := j.isLt; omega⟩) (decide (bvec j = false)) = true := by
    intro a j
    have hiff := sat3Clause_single_iff N (sat3Patch N c y u) a (sat3PinClause N c hk j)
      ⟨j.val, by have := j.isLt; omega⟩ (hpin_sel j) (hpin_miss j)
      (hpin_dead j ⟨1, by omega⟩ (by show (1 : ℕ) ≤ 1; omega))
      (hpin_dead j ⟨2, by omega⟩ (by show (1 : ℕ) ≤ 2; omega))
    rw [hpin_sign j] at hiff
    exact hiff
  have hLit_c : ∀ a : Fin (sat3V N) → Bool,
      (∃ t, sat3Lit N (sat3Patch N c y u) a c t = true) ↔ xor (a vj) sgn = true := by
    intro a
    have hiff := sat3Clause_single_iff N (sat3Patch N c y u) a c vj hprobe_sel hprobe_miss
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
  · -- refutation: any satisfying assignment is pinned to bvec at j₀, but the probe demands the opposite
    cases hfam : sat3Family N (sat3Patch N c y u)
    · rfl
    · exfalso
      obtain ⟨a, ha⟩ := (sat3Family_iff N _).mp hfam
      have hpin := (hLit_pin a j₀).mp
        (sat3Eval_clause_true N _ a ha (sat3PinClause N c hk j₀))
      have hcc := (hLit_c a).mp (sat3Eval_clause_true N _ a ha c)
      have haj : a ⟨j₀.val, by have := j₀.isLt; omega⟩ = bvec j₀ := xor_decide_eq _ _ hpin
      have hmkvj : (⟨j₀.val, by have := j₀.isLt; omega⟩ : Fin (sat3V N)) = vj :=
        Fin.ext hvj.symm
      rw [hmkvj] at haj
      rw [haj] at hcc
      rw [hxor] at hcc
      exact Bool.noConfusion hcc
  · -- construction: the pinned assignment satisfies everything
    set awit : Fin (sat3V N) → Bool :=
      fun i => if h : i.val < k then bvec ⟨i.val, h⟩ else false with hawit
    have hawit_at : ∀ (j : Fin k) (vi : Fin (sat3V N)), vi.val = j.val → awit vi = bvec j := by
      intro j vi hvij
      have hlt : vi.val < k := by
        rw [hvij]
        exact j.isLt
      show (if h : vi.val < k then bvec ⟨vi.val, h⟩ else false) = bvec j
      rw [dif_pos hlt]
      exact congrArg bvec (Fin.ext hvij)
    rw [sat3Family_iff]
    refine ⟨awit, sat3Eval_true_of_all N _ awit ?_⟩
    intro cl
    by_cases hclc : cl = c
    · rw [hclc]
      refine (hLit_c awit).mpr ?_
      rw [hawit_at j₀ vj hvj]
      exact hxor
    · by_cases hpin : ∃ j : Fin k, sat3PinClause N c hk j = cl
      · obtain ⟨j, rfl⟩ := hpin
        refine (hLit_pin awit j).mpr ?_
        rw [hawit_at j ⟨j.val, by have := j.isLt; omega⟩ rfl]
        cases bvec j <;> rfl
      · exact hLit_taut awit cl hclc (fun j h => hpin ⟨j, Fin.ext h.symm⟩)

/-! ### Distinctness and the count -/

/-- **Distinct subfunctions (proved)**: different pin vectors give different subfunctions on block `c`, read apart by
a one-literal probe. -/
theorem sat3_block_subfunctions_distinct (N : ℕ) (hv : 1 ≤ sat3V N) {k : ℕ}
    (hk : k + 1 ≤ sat3M N) (hkv : k ≤ sat3V N) (c : Fin (sat3M N))
    (b b' : Fin k → Bool) (hne : b ≠ b') :
    ∃ uu : Fin N → Bool,
      sat3Family N (sat3Patch N c (sat3Context N c hk b) uu) ≠
      sat3Family N (sat3Patch N c (sat3Context N c hk b') uu) := by
  have hex : ∃ j₀ : Fin k, b j₀ ≠ b' j₀ := by
    by_contra hcon
    push_neg at hcon
    exact hne (funext hcon)
  obtain ⟨j₀, hj₀⟩ := hex
  refine ⟨sat3Probe N ⟨j₀.val, by have := j₀.isLt; omega⟩ (!(b j₀)), ?_⟩
  rw [sat3Context_probe_eval N hv hk hkv c b j₀
      ⟨j₀.val, by have := j₀.isLt; omega⟩ rfl (!(b j₀)),
    sat3Context_probe_eval N hv hk hkv c b' j₀
      ⟨j₀.val, by have := j₀.isLt; omega⟩ rfl (!(b j₀))]
  cases hb : b j₀ <;> cases hb' : b' j₀
  · exact absurd (hb.trans hb'.symm) hj₀
  · decide
  · decide
  · exact absurd (hb.trans hb'.symm) hj₀

/-- **The per-block subfunction count (proved)**: block `c` carries exactly `2^k` distinct subfunctions from the
`k`-variable pin contexts. -/
theorem sat3_block_subfunction_count (N : ℕ) (hv : 1 ≤ sat3V N) {k : ℕ}
    (hk : k + 1 ≤ sat3M N) (hkv : k ≤ sat3V N) (c : Fin (sat3M N)) :
    (Finset.univ.image (fun bvec : Fin k → Bool =>
      (fun uu : Fin N → Bool =>
        sat3Family N (sat3Patch N c (sat3Context N c hk bvec) uu)))).card = 2 ^ k := by
  have hinj : Function.Injective (fun bvec : Fin k → Bool =>
      (fun uu : Fin N → Bool =>
        sat3Family N (sat3Patch N c (sat3Context N c hk bvec) uu))) := by
    intro b b' heq
    by_contra hne
    obtain ⟨uu, huu⟩ := sat3_block_subfunctions_distinct N hv hk hkv c b b' hne
    exact huu (congrFun heq uu)
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]

/-- The layout always admits `k = sat3M N − 1` pinned variables: `m·D ≤ N < (v+1)²` forces `3m < v + 1`. -/
theorem sat3M_pred_le_sat3V (N : ℕ) : sat3M N - 1 ≤ sat3V N := by
  have h1 : sat3M N * sat3D N ≤ N := Nat.div_mul_le_self N (sat3D N)
  have h2 : N < (sat3V N + 1) * (sat3V N + 1) := Nat.lt_succ_sqrt N
  have h3 : sat3M N * 3 * (sat3V N + 1) = sat3M N * sat3D N := by
    show sat3M N * 3 * (sat3V N + 1) = sat3M N * (3 * (sat3V N + 1))
    rw [Nat.mul_assoc]
  have h4 : sat3M N * 3 * (sat3V N + 1) < (sat3V N + 1) * (sat3V N + 1) := by omega
  have h5 : sat3M N * 3 < sat3V N + 1 := lt_of_mul_lt_mul_right h4 (Nat.zero_le _)
  omega

/-- **The concrete headline (proved)**: every clause block of `sat3Family` carries at least
`2^(sat3M N − 1) ≈ 2^(√N/3)` distinct subfunctions — the Nečiporuk counting substrate. -/
theorem sat3_block_subfunction_count_pred (N : ℕ) (hv : 1 ≤ sat3V N) (hm1 : 1 ≤ sat3M N)
    (c : Fin (sat3M N)) :
    ∃ Y : (Fin (sat3M N - 1) → Bool) → (Fin N → Bool),
      (Finset.univ.image (fun bvec : Fin (sat3M N - 1) → Bool =>
        (fun uu : Fin N → Bool => sat3Family N (sat3Patch N c (Y bvec) uu)))).card
        = 2 ^ (sat3M N - 1) := by
  have hk : (sat3M N - 1) + 1 ≤ sat3M N := by omega
  exact ⟨fun bvec => sat3Context N c hk bvec,
    sat3_block_subfunction_count N hv hk (sat3M_pred_le_sat3V N) c⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3Context_probe_eval
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_block_subfunction_count
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_block_subfunction_count_pred
