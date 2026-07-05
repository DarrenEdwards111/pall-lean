import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameFinalBalanceCount

/-!
# N-Frame: evasiveness — the `hvars` rung discharged

The single stated hypothesis of `sat3_coneExcess_omega` was `hvars`: the root cone of a circuit
computing sat3 reads at least half the live selector grid.  This file proves the stronger true
statement and removes the hypothesis:

  `influential_mem_varsOf` — **PROVED, the general principle**: a circuit's output is a function
        of its root-cone variable support, so any influential bit lies in `varsOf` of the root.
  `sat3_selector_influential` — **PROVED, the witness pair**: every slot-0 selector bit
        `sel₀(c,w)` is influential for `sat3Family` — the multi-probe eval at `T = ∅` versus
        `T = {w}` under a covering pin context gives two points differing at exactly that bit
        with values `false` and `true`.
  `sat3_varsOf_lower` — **PROVED, the grid bound**: `m·v ≤ |varsOf root|` for every circuit
        computing sat3.
  `sat3_coneExcess_omega_unconditional` — **PROVED, the capstone**: for every minimal circuit of
        `sat3Family N` (with the trivial size conditions `1 ≤ v`, `3 ≤ m`),
        `m < 32·(coneExcess + 2)` — i.e. `coneExcess ≥ m/32 − 2 = Ω(m) = Ω(√N)`,
        **unconditionally**.

## Honest scope

The Track C chain is now hypothesis-free from the circuit model to the cone-excess bound: minimal
circuits computing the encoded 3-SAT family pay `Ω(√N)` cone excess.  This is a real, restricted
lower bound in the wire/cone-excess model.  What it is NOT: a gate-count (`cbudget`) lower bound
beyond what cone excess implies (that cash-out is the next rung), and it is nowhere near
`NEXP ⊄ ACC⁰` or `P ≠ NP` — the model is the repository's own boundary-transducer circuit model,
and the bound is polynomially small (`√N`), not super-polynomial.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **THE GENERAL PRINCIPLE (proved)**: an influential bit of a computed function lies in the
root cone's variable support. -/
theorem influential_mem_varsOf {n : ℕ} (f : (Fin n → Bool) → Bool)
    (cc : List (CGate n)) (hcomp : computes cc f) (i : Fin n)
    (x y : Fin n → Bool) (hagree : ∀ i' : Fin n, i' ≠ i → x i' = y i')
    (hne : f x ≠ f y) : i ∈ varsOf cc (cc.length - 1) := by
  by_contra hmem
  apply hne
  rw [← hcomp x, ← hcomp y]
  show (runFrom x [] cc).getD (cc.length - 1) false
    = (runFrom y [] cc).getD (cc.length - 1) false
  apply varsOf_agree_wire
  intro i' hi'
  apply hagree
  intro hcon
  rw [hcon] at hi'
  exact hmem hi'

set_option maxHeartbeats 800000 in
/-- **THE WITNESS PAIR (proved)**: every slot-0 selector bit is influential for the SAT family —
the multi-probe eval at `T = ∅` versus `T = {w}` under a covering pin context. -/
theorem sat3_selector_influential (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (c : Fin (sat3M N)) (w : Fin (sat3V N)) :
    ∃ x y : Fin N → Bool,
      (∀ i : Fin N,
        i ≠ sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) → x i = y i)
      ∧ sat3Family N x ≠ sat3Family N y := by
  classical
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  set p0 : Fin (sat3M N - 2) := ⟨0, by omega⟩ with hp0
  obtain ⟨α, hαinj, hαmap, -⟩ := exists_injection_mapping_strict hkv
    ({p0} : Finset (Fin (sat3M N - 2))) ({w} : Finset (Fin (sat3V N)))
    (by rw [Finset.card_singleton, Finset.card_singleton])
  have hα0 : α p0 = w :=
    Finset.mem_singleton.mp (hαmap p0 (Finset.mem_singleton_self p0))
  set bvec : Fin (sat3M N - 2) → Bool := fun _ => true with hbvec
  refine ⟨sat3Patch N c (sat3ContextG N c hk α bvec)
      (fun bit => decide (∃ w' ∈ (∅ : Finset (Fin (sat3V N))),
        bit.val % sat3D N = w'.val)),
    sat3Patch N c (sat3ContextG N c hk α bvec)
      (fun bit => decide (∃ w' ∈ ({w} : Finset (Fin (sat3V N))),
        bit.val % sat3D N = w'.val)), ?_, ?_⟩
  · -- the two points differ only at the selector bit
    intro i hi
    show (if i.val / sat3D N = c.val
        then decide (∃ w' ∈ (∅ : Finset (Fin (sat3V N))), i.val % sat3D N = w'.val)
        else sat3ContextG N c hk α bvec i)
      = (if i.val / sat3D N = c.val
        then decide (∃ w' ∈ ({w} : Finset (Fin (sat3V N))), i.val % sat3D N = w'.val)
        else sat3ContextG N c hk α bvec i)
    by_cases hdiv : i.val / sat3D N = c.val
    · rw [if_pos hdiv, if_pos hdiv]
      have h0 : decide (∃ w' ∈ (∅ : Finset (Fin (sat3V N))),
          i.val % sat3D N = w'.val) = false := by
        apply decide_eq_false
        rintro ⟨w', hw', -⟩
        exact Finset.notMem_empty _ hw'
      have h1 : decide (∃ w' ∈ ({w} : Finset (Fin (sat3V N))),
          i.val % sat3D N = w'.val) = false := by
        apply decide_eq_false
        rintro ⟨w', hw', hrem⟩
        have hww : w' = w := Finset.mem_singleton.mp hw'
        rw [hww] at hrem
        apply hi
        apply Fin.ext
        show i.val = c.val * sat3D N + 0 * (sat3V N + 1) + w.val
        have hdm := Nat.div_add_mod i.val (sat3D N)
        rw [hdiv, hrem] at hdm
        have hcm : sat3D N * c.val = c.val * sat3D N := Nat.mul_comm _ _
        omega
      rw [h0, h1]
    · rw [if_neg hdiv, if_neg hdiv]
  · -- the values differ: false at `T = ∅`, true at `T = {w}`
    rw [sat3ContextG_multi_probe_eval N hv hk hkv c α hαinj bvec
        (∅ : Finset (Fin (sat3V N)))
        (fun w' hw' => absurd hw' (Finset.notMem_empty w')),
      sat3ContextG_multi_probe_eval N hv hk hkv c α hαinj bvec
        ({w} : Finset (Fin (sat3V N)))
        (fun w' hw' => ⟨p0, by
          rw [hα0]
          exact (Finset.mem_singleton.mp hw').symm⟩)]
    have hd0 : decide (∃ j : Fin (sat3M N - 2),
        α j ∈ (∅ : Finset (Fin (sat3V N))) ∧ bvec j = true) = false := by
      apply decide_eq_false
      rintro ⟨p, hp, -⟩
      exact Finset.notMem_empty _ hp
    have hd1 : decide (∃ j : Fin (sat3M N - 2),
        α j ∈ ({w} : Finset (Fin (sat3V N))) ∧ bvec j = true) = true := by
      apply decide_eq_true
      refine ⟨p0, ?_, rfl⟩
      rw [hα0]
      exact Finset.mem_singleton_self w
    rw [hd0, hd1]
    exact Bool.false_ne_true

/-- **THE GRID BOUND (proved)**: every circuit computing sat3 reads the whole slot-0 selector
grid: `m·v ≤ |varsOf root|`. -/
theorem sat3_varsOf_lower (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cc : List (CGate N)) (hcomp : computes cc (sat3Family N)) :
    sat3M N * sat3V N ≤ (varsOf cc (cc.length - 1)).card := by
  classical
  have hmem : ∀ (c : Fin (sat3M N)) (w : Fin (sat3V N)),
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega)
        ∈ varsOf cc (cc.length - 1) := by
    intro c w
    obtain ⟨x, y, hagree, hne⟩ := sat3_selector_influential N hv hm3 hk c w
    exact influential_mem_varsOf (sat3Family N) cc hcomp _ x y hagree hne
  have hle : (Finset.univ : Finset (Fin (sat3M N) × Fin (sat3V N))).card
      ≤ (varsOf cc (cc.length - 1)).card := by
    apply Finset.card_le_card_of_injOn
      (fun cw : Fin (sat3M N) × Fin (sat3V N) =>
        sat3Bit N cw.1 ⟨0, by omega⟩ cw.2.val (by have := cw.2.isLt; omega))
    · intro cw _
      apply Finset.mem_coe.mpr
      exact hmem cw.1 cw.2
    · intro cw _ cw' _ heq
      have hveq := congrArg Fin.val heq
      have h1 : (sat3Bit N cw.1 ⟨0, by omega⟩ cw.2.val
          (by have := cw.2.isLt; omega)).val / sat3D N = cw.1.val :=
        sat3Bit_clause N cw.1 ⟨0, by omega⟩ cw.2.val (by have := cw.2.isLt; omega)
      have h2 : (sat3Bit N cw'.1 ⟨0, by omega⟩ cw'.2.val
          (by have := cw'.2.isLt; omega)).val / sat3D N = cw'.1.val :=
        sat3Bit_clause N cw'.1 ⟨0, by omega⟩ cw'.2.val (by have := cw'.2.isLt; omega)
      have h3 : (sat3Bit N cw.1 ⟨0, by omega⟩ cw.2.val
          (by have := cw.2.isLt; omega)).val % sat3D N
          = (⟨0, by omega⟩ : Fin 3).val * (sat3V N + 1) + cw.2.val :=
        sat3Bit_rem N cw.1 ⟨0, by omega⟩ cw.2.val (by have := cw.2.isLt; omega)
      have h4 : (sat3Bit N cw'.1 ⟨0, by omega⟩ cw'.2.val
          (by have := cw'.2.isLt; omega)).val % sat3D N
          = (⟨0, by omega⟩ : Fin 3).val * (sat3V N + 1) + cw'.2.val :=
        sat3Bit_rem N cw'.1 ⟨0, by omega⟩ cw'.2.val (by have := cw'.2.isLt; omega)
      have h3' : (sat3Bit N cw.1 ⟨0, by omega⟩ cw.2.val
          (by have := cw.2.isLt; omega)).val % sat3D N = cw.2.val := by
        rw [h3]
        show (0 : ℕ) * (sat3V N + 1) + cw.2.val = cw.2.val
        omega
      have h4' : (sat3Bit N cw'.1 ⟨0, by omega⟩ cw'.2.val
          (by have := cw'.2.isLt; omega)).val % sat3D N = cw'.2.val := by
        rw [h4]
        show (0 : ℕ) * (sat3V N + 1) + cw'.2.val = cw'.2.val
        omega
      apply Prod.ext
      · apply Fin.ext
        rw [← h1, ← h2, hveq]
      · apply Fin.ext
        rw [hveq] at h3'
        rw [h3'] at h4'
        exact h4'
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hle
  exact hle

/-- **THE UNCONDITIONAL Ω(m) CONE-EXCESS BOUND (proved)**: every minimal circuit of the encoded
3-SAT family pays `coneExcess ≥ m/32 − 2 = Ω(m) = Ω(√N)` — no evasiveness hypothesis left. -/
theorem sat3_coneExcess_omega_unconditional (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N)
    (cc : List (CGate N)) (hcomp : computes cc (sat3Family N))
    (hmin : cc.length = cbudget (sat3Family N)) :
    sat3M N < 32 * (coneExcess cc (cc.length - 1) + 2) := by
  have hk : (sat3M N - 2) + 1 ≤ sat3M N := by omega
  apply sat3_coneExcess_omega N hv hm3 hk cc hcomp hmin
  have := sat3_varsOf_lower N hv hm3 hk cc hcomp
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.influential_mem_varsOf
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_selector_influential
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_varsOf_lower
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_coneExcess_omega_unconditional
