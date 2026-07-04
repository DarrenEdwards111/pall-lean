import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDAGWireSurgery

/-!
# N-Frame: no dead bits — every layout coordinate of SAT is live, and the `≈ N` circuit bound

The DAG battlefield's dependency layer, completed.  The wire-surgery file proved the one-kill engine and reached
`m·v + (m−2)`; but in this circuit model `var` gates are gates, so the true ceiling of every one-per-variable
method — dependency counting and one-kill chains alike — is the number of *live coordinates*.  This file shows
that for the SAT layout that number is **all of them**:

  `sat3_sel_pair` / `sat3_sign_pair` / `sat3_layout_pair` — **PROVED**: every one of the `3·m·v` selector bits
        (all three slots) and every one of the `3·m` sign bits (all three slots) carries a 1/0 forcing pair.
        Selectors flip an empty clause into a satisfiable one; signs flip the lone literal of clause `c` against
        the support of every other clause — a genuine sign conflict, not an empty clause.
  `sat3_cbudget_all_bits` — **PROVED, the record**:

        `m·D = 3·m·v + 3·m ≤ cbudget (sat3Family N)`,   i.e.   `N − O(√N) ≤ cbudget (sat3Family N)`

        (`sat3_cbudget_near_N`: `N ≤ cbudget + D`) — every gate-count short of the full input count is
        impossible: SAT has **no dead coordinates**.  This subsumes the dependency record `m·v`
        (`sat3_cbudget_lb`) and the wire-surgery schedule `m·v + (m−2)`.

## Honest scope

This is the exact ceiling of first-order methods in this model: any dependency count or live one-kill chain is
bounded by the input count, and SAT now meets it (up to the `< D` layout padding).  Everything beyond is
second-order: internal-gate counting (the connectivity bound — binary gates must *merge* `≈ N` inputs, worth
another `≈ N`), Schnorr/Stockmeyer multi-kill case analysis, and the genuinely open fan-out/cone accounting —
the named rungs toward superlinear.  The mountain — `sat3Target`, super-polynomial `cbudget` despite sharing —
is untouched by linear bounds and is not claimed.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Field arithmetic: the layout map is injective -/

theorem slotField_ne {v : ℕ} (t t' : Fin 3) {i j : ℕ} (hi : i < v + 1) (hj : j < v + 1)
    (hne : i ≠ j) : t.val * (v + 1) + i ≠ t'.val * (v + 1) + j := by
  intro h
  have h' : (v + 1) * t.val + i = (v + 1) * t'.val + j := by
    rw [Nat.mul_comm (v + 1) t.val, Nat.mul_comm (v + 1) t'.val]
    exact h
  have hmod : i % (v + 1) = j % (v + 1) := by
    rw [← Nat.mul_add_mod (v + 1) t.val i, ← Nat.mul_add_mod (v + 1) t'.val j, h']
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hmod
  exact hne hmod

theorem slotField_eq {v : ℕ} (t t' : Fin 3) {i j : ℕ} (hi : i < v + 1) (hj : j < v + 1)
    (h : t.val * (v + 1) + i = t'.val * (v + 1) + j) : t = t' ∧ i = j := by
  have hij : i = j := by
    by_contra hne
    exact slotField_ne t t' hi hj hne h
  subst hij
  refine ⟨?_, rfl⟩
  have hmul : t.val * (v + 1) = t'.val * (v + 1) := by omega
  exact Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega) hmul)

/-- **The layout map is injective (proved)** — distinct `(clause, slot, field)` triples are distinct bits. -/
theorem sat3Bit_inj (N : ℕ) {c c' : Fin (sat3M N)} {t t' : Fin 3} {f f' : ℕ}
    (hf : f < sat3V N + 1) (hf' : f' < sat3V N + 1)
    (h : sat3Bit N c t f hf = sat3Bit N c' t' f' hf') : c = c' ∧ t = t' ∧ f = f' := by
  have hdiv : c.val = c'.val := by
    rw [← sat3Bit_clause N c t f hf, ← sat3Bit_clause N c' t' f' hf', h]
  have hrem : t.val * (sat3V N + 1) + f = t'.val * (sat3V N + 1) + f' := by
    rw [← sat3Bit_rem N c t f hf, ← sat3Bit_rem N c' t' f' hf', h]
  obtain ⟨ht, hff⟩ := slotField_eq t t' hf hf' hrem
  exact ⟨Fin.ext hdiv, ht, hff⟩

theorem sat3Bit_ne_of_clause (N : ℕ) {c c' : Fin (sat3M N)} (t t' : Fin 3) {f f' : ℕ}
    (hf : f < sat3V N + 1) (hf' : f' < sat3V N + 1) (h : c.val ≠ c'.val) :
    sat3Bit N c t f hf ≠ sat3Bit N c' t' f' hf' :=
  fun hcon => h (congrArg Fin.val (sat3Bit_inj N hf hf' hcon).1)

theorem sat3Bit_ne_of_field (N : ℕ) {c c' : Fin (sat3M N)} (t t' : Fin 3) {f f' : ℕ}
    (hf : f < sat3V N + 1) (hf' : f' < sat3V N + 1) (h : f ≠ f') :
    sat3Bit N c t f hf ≠ sat3Bit N c' t' f' hf' :=
  fun hcon => h (sat3Bit_inj N hf hf' hcon).2.2

/-! ### The support pattern and the two witness families -/

/-- The outer support: every clause other than `c` is the single positive-signed literal `¬x₀`
(slot-0 selector 0 on, slot-0 sign on). -/
def sat3Support (N : ℕ) (c : Fin (sat3M N)) : Fin N → Bool :=
  fun bb => decide (bb.val / sat3D N < sat3M N ∧ bb.val / sat3D N ≠ c.val ∧
    (bb.val % sat3D N = 0 ∨ bb.val % sat3D N = sat3V N))

theorem sat3Support_block_c (N : ℕ) (c : Fin (sat3M N)) (bb : Fin N)
    (h : bb.val / sat3D N = c.val) : sat3Support N c bb = false := by
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro ⟨-, hne, -⟩
  exact hne h

theorem sat3Support_sel0 (N : ℕ) (c cl : Fin (sat3M N)) (hne : cl.val ≠ c.val) :
    sat3Support N c (sat3Bit N cl ⟨0, by omega⟩ 0 (by omega)) = true := by
  show decide _ = true
  rw [decide_eq_true_eq]
  refine ⟨?_, ?_, Or.inl ?_⟩
  · rw [sat3Bit_clause]
    exact cl.isLt
  · rw [sat3Bit_clause]
    exact hne
  · rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + 0 = 0
    omega

theorem sat3Support_sign0 (N : ℕ) (c cl : Fin (sat3M N)) (hne : cl.val ≠ c.val) :
    sat3Support N c (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)) = true := by
  show decide _ = true
  rw [decide_eq_true_eq]
  refine ⟨?_, ?_, Or.inr ?_⟩
  · rw [sat3Bit_clause]
    exact cl.isLt
  · rw [sat3Bit_clause]
    exact hne
  · rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N
    omega

theorem sat3Support_sel_other (N : ℕ) (c cl : Fin (sat3M N)) (i : Fin (sat3V N))
    (h0 : i.val ≠ 0) :
    sat3Support N c (sat3Bit N cl ⟨0, by omega⟩ i.val (by have := i.isLt; omega)) = false := by
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro ⟨-, -, hrem | hrem⟩ <;> rw [sat3Bit_rem] at hrem
  · have h' : (0 : ℕ) * (sat3V N + 1) + i.val = 0 := hrem
    omega
  · have h' : (0 : ℕ) * (sat3V N + 1) + i.val = sat3V N := hrem
    have := i.isLt
    omega

theorem sat3Support_dead (N : ℕ) (c cl : Fin (sat3M N)) (t' : Fin 3) (ht' : 1 ≤ t'.val)
    (i : Fin (sat3V N)) :
    sat3Support N c (sat3Bit N cl t' i.val (by have := i.isLt; omega)) = false := by
  have hbig : sat3V N + 1 ≤ t'.val * (sat3V N + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro ⟨-, -, hrem | hrem⟩ <;> rw [sat3Bit_rem] at hrem <;> omega

/-- The selector witness: the support outside `c`, and inside `c` only the slot-`t` sign is on — the flipped
selector becomes clause `c`'s lone (negated) literal. -/
def sat3SelWitness (N : ℕ) (c : Fin (sat3M N)) (t : Fin 3) : Fin N → Bool :=
  fun bb => sat3Support N c bb ||
    decide (bb.val / sat3D N = c.val ∧
      bb.val % sat3D N = t.val * (sat3V N + 1) + sat3V N)

/-- The sign witness: the support outside `c`, and inside `c` only the slot-`t` selector 0 is on — the flipped
sign toggles clause `c`'s lone literal between `¬x₀` (consistent) and `x₀` (conflicting). -/
def sat3SignWitness (N : ℕ) (c : Fin (sat3M N)) (t : Fin 3) : Fin N → Bool :=
  fun bb => sat3Support N c bb ||
    decide (bb.val / sat3D N = c.val ∧
      bb.val % sat3D N = t.val * (sat3V N + 1))

theorem sat3SelWitness_out (N : ℕ) (c : Fin (sat3M N)) (t : Fin 3) (bb : Fin N)
    (h : bb.val / sat3D N ≠ c.val) :
    sat3SelWitness N c t bb = sat3Support N c bb := by
  have hd : decide (bb.val / sat3D N = c.val ∧
      bb.val % sat3D N = t.val * (sat3V N + 1) + sat3V N) = false :=
    decide_eq_false (fun hcon => h hcon.1)
  show (sat3Support N c bb || decide (bb.val / sat3D N = c.val ∧
      bb.val % sat3D N = t.val * (sat3V N + 1) + sat3V N)) = sat3Support N c bb
  rw [hd, Bool.or_false]

theorem sat3SignWitness_out (N : ℕ) (c : Fin (sat3M N)) (t : Fin 3) (bb : Fin N)
    (h : bb.val / sat3D N ≠ c.val) :
    sat3SignWitness N c t bb = sat3Support N c bb := by
  have hd : decide (bb.val / sat3D N = c.val ∧
      bb.val % sat3D N = t.val * (sat3V N + 1)) = false :=
    decide_eq_false (fun hcon => h hcon.1)
  show (sat3Support N c bb || decide (bb.val / sat3D N = c.val ∧
      bb.val % sat3D N = t.val * (sat3V N + 1))) = sat3Support N c bb
  rw [hd, Bool.or_false]

theorem sat3SelWitness_in (N : ℕ) (c : Fin (sat3M N)) (t : Fin 3) (bb : Fin N)
    (h : bb.val / sat3D N = c.val) :
    sat3SelWitness N c t bb
      = decide (bb.val % sat3D N = t.val * (sat3V N + 1) + sat3V N) := by
  show (sat3Support N c bb || decide (bb.val / sat3D N = c.val ∧
      bb.val % sat3D N = t.val * (sat3V N + 1) + sat3V N))
    = decide (bb.val % sat3D N = t.val * (sat3V N + 1) + sat3V N)
  rw [sat3Support_block_c N c bb h, Bool.false_or]
  exact decide_eq_decide.mpr ⟨fun hh => hh.2, fun hp => ⟨h, hp⟩⟩

theorem sat3SignWitness_in (N : ℕ) (c : Fin (sat3M N)) (t : Fin 3) (bb : Fin N)
    (h : bb.val / sat3D N = c.val) :
    sat3SignWitness N c t bb
      = decide (bb.val % sat3D N = t.val * (sat3V N + 1)) := by
  show (sat3Support N c bb || decide (bb.val / sat3D N = c.val ∧
      bb.val % sat3D N = t.val * (sat3V N + 1)))
    = decide (bb.val % sat3D N = t.val * (sat3V N + 1))
  rw [sat3Support_block_c N c bb h, Bool.false_or]
  exact decide_eq_decide.mpr ⟨fun hh => hh.2, fun hp => ⟨h, hp⟩⟩

/-! ### The selector pairs: all three slots -/

/-- **The general selector pair (proved)**: every selector bit — any clause, any slot, any variable — carries a
1/0 forcing pair. -/
theorem sat3_sel_pair (N : ℕ) (hv : 1 ≤ sat3V N) (c : Fin (sat3M N)) (t : Fin 3)
    (j : Fin (sat3V N)) :
    ∃ x₁ x₀ : Fin N → Bool, sat3Family N x₁ = true ∧ sat3Family N x₀ = false ∧
      ∀ b : Fin N, x₁ b ≠ x₀ b →
        b = sat3Bit N c t j.val (by have := j.isLt; omega) := by
  refine ⟨Function.update (sat3SelWitness N c t)
      (sat3Bit N c t j.val (by have := j.isLt; omega)) true,
    Function.update (sat3SelWitness N c t)
      (sat3Bit N c t j.val (by have := j.isLt; omega)) false, ?_, ?_, ?_⟩
  · -- flipped on: satisfiable by the all-false assignment
    apply sat3Family_of_witness N _ (fun _ => false)
    apply sat3Eval_true_of_all
    intro cl
    by_cases hcl : cl = c
    · subst hcl
      refine ⟨t, sat3Lit_true_of_selected N _ _ cl t j ?_ ?_⟩
      · rw [Function.update_self]
      · have hne : sat3Bit N cl t (sat3V N) (by omega)
            ≠ sat3Bit N cl t j.val (by have := j.isLt; omega) :=
          sat3Bit_ne_of_field N t t _ _ (by have := j.isLt; omega)
        rw [Function.update_of_ne hne]
        rw [sat3SelWitness_in N cl t _ (sat3Bit_clause N cl t (sat3V N) (by omega))]
        have hd : decide (t.val * (sat3V N + 1) + sat3V N
            = t.val * (sat3V N + 1) + sat3V N) = true := decide_eq_true rfl
        rw [sat3Bit_rem, hd]
        rfl
    · have hclv : cl.val ≠ c.val := fun h => hcl (Fin.ext h)
      refine ⟨⟨0, by omega⟩, sat3Lit_true_of_selected N _ _ cl ⟨0, by omega⟩ ⟨0, hv⟩ ?_ ?_⟩
      · have hne : sat3Bit N cl ⟨0, by omega⟩ (⟨0, hv⟩ : Fin (sat3V N)).val (by omega)
            ≠ sat3Bit N c t j.val (by have := j.isLt; omega) :=
          sat3Bit_ne_of_clause N _ t _ _ hclv
        rw [Function.update_of_ne hne]
        rw [sat3SelWitness_out N c t _ (by
          rw [sat3Bit_clause]
          exact hclv)]
        exact sat3Support_sel0 N c cl hclv
      · have hne : sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)
            ≠ sat3Bit N c t j.val (by have := j.isLt; omega) :=
          sat3Bit_ne_of_clause N _ t _ _ hclv
        rw [Function.update_of_ne hne]
        rw [sat3SelWitness_out N c t _ (by
          rw [sat3Bit_clause]
          exact hclv)]
        rw [sat3Support_sign0 N c cl hclv]
        rfl
  · -- flipped off: clause `c` is empty
    apply sat3Family_false_of_empty_clause N _ c
    intro t' i
    by_cases hb : sat3Bit N c t' i.val (by have := i.isLt; omega)
        = sat3Bit N c t j.val (by have := j.isLt; omega)
    · rw [hb, Function.update_self]
    · rw [Function.update_of_ne hb]
      rw [sat3SelWitness_in N c t _ (sat3Bit_clause N c t' i.val (by have := i.isLt; omega))]
      rw [sat3Bit_rem]
      exact decide_eq_false (slotField_ne t' t (by have := i.isLt; omega) (by omega)
        (by have := i.isLt; omega))
  · intro b hb
    by_contra hne
    apply hb
    rw [Function.update_of_ne hne, Function.update_of_ne hne]

/-! ### The sign pairs: all three slots -/

/-- **The general sign pair (proved)**: every sign bit — any clause, any slot — carries a 1/0 forcing pair: the
off-value creates a genuine sign conflict against the support, not an empty clause. -/
theorem sat3_sign_pair (N : ℕ) (hv : 1 ≤ sat3V N) (hm2 : 2 ≤ sat3M N)
    (c : Fin (sat3M N)) (t : Fin 3) :
    ∃ x₁ x₀ : Fin N → Bool, sat3Family N x₁ = true ∧ sat3Family N x₀ = false ∧
      ∀ b : Fin N, x₁ b ≠ x₀ b → b = sat3Bit N c t (sat3V N) (by omega) := by
  have hsel0 : ∀ a : Bool,
      Function.update (sat3SignWitness N c t) (sat3Bit N c t (sat3V N) (by omega)) a
        (sat3Bit N c t (⟨0, hv⟩ : Fin (sat3V N)).val (by omega)) = true := by
    intro a
    have hne : sat3Bit N c t (⟨0, hv⟩ : Fin (sat3V N)).val (by omega)
        ≠ sat3Bit N c t (sat3V N) (by omega) :=
      sat3Bit_ne_of_field N t t _ _ (by omega)
    rw [Function.update_of_ne hne]
    rw [sat3SignWitness_in N c t _ (sat3Bit_clause N c t 0 (by omega))]
    rw [sat3Bit_rem]
    apply decide_eq_true
    show t.val * (sat3V N + 1) + 0 = t.val * (sat3V N + 1)
    omega
  have hothers : ∀ (a : Bool) (i : Fin (sat3V N)), i ≠ ⟨0, hv⟩ →
      Function.update (sat3SignWitness N c t) (sat3Bit N c t (sat3V N) (by omega)) a
        (sat3Bit N c t i.val (by have := i.isLt; omega)) = false := by
    intro a i hi
    have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
    have hne : sat3Bit N c t i.val (by have := i.isLt; omega)
        ≠ sat3Bit N c t (sat3V N) (by omega) :=
      sat3Bit_ne_of_field N t t _ _ (by have := i.isLt; omega)
    rw [Function.update_of_ne hne]
    rw [sat3SignWitness_in N c t _ (sat3Bit_clause N c t i.val (by have := i.isLt; omega))]
    rw [sat3Bit_rem]
    apply decide_eq_false
    intro hcon
    have hcon' : t.val * (sat3V N + 1) + i.val = t.val * (sat3V N + 1) + 0 := by omega
    exact slotField_ne t t (by have := i.isLt; omega) (by omega) hi0 hcon'
  have hdead : ∀ (a : Bool) (t' : Fin 3), t' ≠ t → ∀ i : Fin (sat3V N),
      Function.update (sat3SignWitness N c t) (sat3Bit N c t (sat3V N) (by omega)) a
        (sat3Bit N c t' i.val (by have := i.isLt; omega)) = false := by
    intro a t' htt i
    have hne : sat3Bit N c t' i.val (by have := i.isLt; omega)
        ≠ sat3Bit N c t (sat3V N) (by omega) :=
      sat3Bit_ne_of_field N t' t _ _ (by have := i.isLt; omega)
    rw [Function.update_of_ne hne]
    rw [sat3SignWitness_in N c t _ (sat3Bit_clause N c t' i.val (by have := i.isLt; omega))]
    rw [sat3Bit_rem]
    apply decide_eq_false
    intro hcon
    have h' : t'.val * (sat3V N + 1) + i.val = t.val * (sat3V N + 1) + 0 := by omega
    exact htt (slotField_eq t' t (by have := i.isLt; omega) (by omega) h').1
  refine ⟨Function.update (sat3SignWitness N c t)
      (sat3Bit N c t (sat3V N) (by omega)) true,
    Function.update (sat3SignWitness N c t)
      (sat3Bit N c t (sat3V N) (by omega)) false, ?_, ?_, ?_⟩
  · -- sign on: all clauses are consistent negative literals, `a ≡ false` satisfies
    apply sat3Family_of_witness N _ (fun _ => false)
    apply sat3Eval_true_of_all
    intro cl
    by_cases hcl : cl = c
    · subst hcl
      refine ⟨t, sat3Lit_true_of_selected N _ _ cl t ⟨0, hv⟩ (hsel0 true) ?_⟩
      rw [Function.update_self]
      rfl
    · have hclv : cl.val ≠ c.val := fun h => hcl (Fin.ext h)
      refine ⟨⟨0, by omega⟩, sat3Lit_true_of_selected N _ _ cl ⟨0, by omega⟩ ⟨0, hv⟩ ?_ ?_⟩
      · have hne : sat3Bit N cl ⟨0, by omega⟩ (⟨0, hv⟩ : Fin (sat3V N)).val (by omega)
            ≠ sat3Bit N c t (sat3V N) (by omega) :=
          sat3Bit_ne_of_clause N _ t _ _ hclv
        rw [Function.update_of_ne hne]
        rw [sat3SignWitness_out N c t _ (by
          rw [sat3Bit_clause]
          exact hclv)]
        exact sat3Support_sel0 N c cl hclv
      · have hne : sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)
            ≠ sat3Bit N c t (sat3V N) (by omega) :=
          sat3Bit_ne_of_clause N _ t _ _ hclv
        rw [Function.update_of_ne hne]
        rw [sat3SignWitness_out N c t _ (by
          rw [sat3Bit_clause]
          exact hclv)]
        rw [sat3Support_sign0 N c cl hclv]
        rfl
  · -- sign off: clause `c` demands `x₀`, every other clause demands `¬x₀`
    apply decide_eq_false
    rintro ⟨a, ha⟩
    -- clause `c` forces `a 0 = true`
    obtain ⟨t', hlit⟩ := sat3Eval_clause_true N _ a ha c
    have ha0 : a ⟨0, hv⟩ = true := by
      by_cases htt : t' = t
      · subst htt
        rw [sat3Lit_single N _ a c t' ⟨0, hv⟩ (hsel0 false)
          (fun i hi => hothers false i hi)] at hlit
        rw [Function.update_self] at hlit
        rwa [Bool.xor_false] at hlit
      · rw [sat3Lit_false_of_empty N _ a c t' (fun i => hdead false t' htt i)] at hlit
        exact Bool.noConfusion hlit
    -- a foreign clause forces `a 0 = false`
    set c'' : Fin (sat3M N) := if c.val = 0 then ⟨1, hm2⟩ else ⟨0, by omega⟩ with hc''
    have hc''v : c''.val ≠ c.val := by
      rw [hc'']
      by_cases hz : c.val = 0
      · rw [if_pos hz, hz]
        show (1 : ℕ) ≠ 0
        omega
      · rw [if_neg hz]
        show (0 : ℕ) ≠ c.val
        omega
    have hread : ∀ (t'' : Fin 3) (fI : ℕ) (hfI : fI < sat3V N + 1),
        Function.update (sat3SignWitness N c t) (sat3Bit N c t (sat3V N) (by omega)) false
          (sat3Bit N c'' t'' fI hfI) = sat3Support N c (sat3Bit N c'' t'' fI hfI) := by
      intro t'' fI hfI
      have hne : sat3Bit N c'' t'' fI hfI ≠ sat3Bit N c t (sat3V N) (by omega) :=
        sat3Bit_ne_of_clause N t'' t _ _ hc''v
      rw [Function.update_of_ne hne]
      exact sat3SignWitness_out N c t _ (by
        rw [sat3Bit_clause]
        exact hc''v)
    have hcc := sat3Eval_clause_true N _ a ha c''
    have hiff := sat3Clause_single_iff N
      (Function.update (sat3SignWitness N c t) (sat3Bit N c t (sat3V N) (by omega)) false)
      a c'' ⟨0, hv⟩
      (by
        rw [hread ⟨0, by omega⟩ (⟨0, hv⟩ : Fin (sat3V N)).val (by omega)]
        exact sat3Support_sel0 N c c'' hc''v)
      (by
        intro i hi
        rw [hread ⟨0, by omega⟩ i.val (by have := i.isLt; omega)]
        exact sat3Support_sel_other N c c'' i (fun h => hi (Fin.ext h)))
      (by
        intro i
        rw [hread ⟨1, by omega⟩ i.val (by have := i.isLt; omega)]
        exact sat3Support_dead N c c'' ⟨1, by omega⟩ (le_refl 1) i)
      (by
        intro i
        rw [hread ⟨2, by omega⟩ i.val (by have := i.isLt; omega)]
        exact sat3Support_dead N c c'' ⟨2, by omega⟩ (by omega : (1:ℕ) ≤ 2) i)
    have hxor := hiff.mp hcc
    rw [hread ⟨0, by omega⟩ (sat3V N) (by omega)] at hxor
    rw [sat3Support_sign0 N c c'' hc''v] at hxor
    rw [ha0] at hxor
    exact Bool.noConfusion hxor
  · intro b hb
    by_contra hne
    apply hb
    rw [Function.update_of_ne hne, Function.update_of_ne hne]

/-! ### Every layout bit is live -/

/-- **NO DEAD BITS (proved)**: every one of the `m·D` layout coordinates carries a 1/0 forcing pair. -/
theorem sat3_layout_pair (N : ℕ) (hv : 1 ≤ sat3V N) (hm2 : 2 ≤ sat3M N)
    (c : Fin (sat3M N)) (t : Fin 3) (fI : ℕ) (hf : fI < sat3V N + 1) :
    ∃ x₁ x₀ : Fin N → Bool, sat3Family N x₁ = true ∧ sat3Family N x₀ = false ∧
      ∀ b : Fin N, x₁ b ≠ x₀ b → b = sat3Bit N c t fI hf := by
  by_cases hfv : fI = sat3V N
  · subst hfv
    exact sat3_sign_pair N hv hm2 c t
  · have hlt : fI < sat3V N := by omega
    exact sat3_sel_pair N hv c t ⟨fI, hlt⟩

/-- **THE `≈ N` CIRCUIT BOUND (proved)**: `m·D ≤ cbudget (sat3Family N)` — every layout coordinate demands its
own `var` gate; the dependency method's ceiling in this model, met exactly. -/
theorem sat3_cbudget_all_bits (N : ℕ) (hv : 1 ≤ sat3V N) (hm2 : 2 ≤ sat3M N) :
    sat3M N * sat3D N ≤ cbudget (sat3Family N) := by
  obtain ⟨c, hcomp, hlen⟩ := Nat.sInf_mem (cbudget_set_nonempty (sat3Family N))
  have hlen' : c.length = cbudget (sat3Family N) := hlen
  have hmem : ∀ p : Fin (sat3M N) × Fin 3 × Fin (sat3V N + 1),
      CGate.var (sat3Bit N p.1 p.2.1 p.2.2.val p.2.2.isLt) ∈ c := by
    intro p
    obtain ⟨x₁, x₀, h1, h0, hforce⟩ :=
      sat3_layout_pair N hv hm2 p.1 p.2.1 p.2.2.val p.2.2.isLt
    exact depends_var_mem c (sat3Family N) hcomp _ x₁ x₀ hforce (by
      rw [h1, h0]
      decide)
  have hinj : Function.Injective
      (fun p : Fin (sat3M N) × Fin 3 × Fin (sat3V N + 1) =>
        sat3Bit N p.1 p.2.1 p.2.2.val p.2.2.isLt) := by
    intro p q h
    obtain ⟨hc, ht, hf⟩ := sat3Bit_inj N p.2.2.isLt q.2.2.isLt h
    exact Prod.ext hc (Prod.ext ht (Fin.ext hf))
  have hsub : Finset.univ.image (fun p : Fin (sat3M N) × Fin 3 × Fin (sat3V N + 1) =>
      sat3Bit N p.1 p.2.1 p.2.2.val p.2.2.isLt) ⊆ circuitVars c := by
    intro i hi
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hi
    exact mem_circuitVars_of c _ (hmem p)
  have hcard : sat3M N * (3 * (sat3V N + 1)) ≤ (circuitVars c).card := by
    have himg : (Finset.univ.image (fun p : Fin (sat3M N) × Fin 3 × Fin (sat3V N + 1) =>
        sat3Bit N p.1 p.2.1 p.2.2.val p.2.2.isLt)).card
        = sat3M N * (3 * (sat3V N + 1)) := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod,
        Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
    rw [← himg]
    exact Finset.card_le_card hsub
  have hD : sat3M N * sat3D N = sat3M N * (3 * (sat3V N + 1)) := rfl
  have hfinal := le_trans hcard (circuitVars_card_le c)
  omega

/-- The record in schedule form: `3·m·v + 3·m` — subsuming `m·v` and `m·v + (m−2)`. -/
theorem sat3_cbudget_all_bits' (N : ℕ) (hv : 1 ≤ sat3V N) (hm2 : 2 ≤ sat3M N) :
    3 * (sat3M N * sat3V N) + 3 * sat3M N ≤ cbudget (sat3Family N) := by
  have h := sat3_cbudget_all_bits N hv hm2
  have he : sat3M N * sat3D N = 3 * (sat3M N * sat3V N) + 3 * sat3M N := by
    show sat3M N * (3 * (sat3V N + 1)) = _
    ring
  omega

/-- **Within one block of the full input count (proved)**: `N ≤ cbudget (sat3Family N) + D` — only the `< D`
layout-padding coordinates are unaccounted. -/
theorem sat3_cbudget_near_N (N : ℕ) (hv : 1 ≤ sat3V N) (hm2 : 2 ≤ sat3M N) :
    N ≤ cbudget (sat3Family N) + sat3D N := by
  have h := sat3_cbudget_all_bits N hv hm2
  have hdm := Nat.div_add_mod N (sat3D N)
  have hmod : N % sat3D N < sat3D N := Nat.mod_lt N (sat3D_pos N)
  have hM : sat3M N * sat3D N = sat3D N * (N / sat3D N) := by
    show N / sat3D N * sat3D N = sat3D N * (N / sat3D N)
    exact Nat.mul_comm _ _
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3Bit_inj
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_sel_pair
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_sign_pair
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_layout_pair
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cbudget_all_bits
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cbudget_all_bits'
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cbudget_near_N
