import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATTwoCut

/-!
# The parallel-case core: freezing one wire, refining through the other

Multi-wire brick 7.  A structural scoping fact drives the case-(iii) analysis: a
coordinate below BOTH wires forces the wires to be NESTED (upward paths diverge
only at reconvergences).  In the parallel case every profile is single-wire, and
the kills refine through one wire while the other is provably frozen:

* **`wire_frozen` (proved)** — nine-slot freezing: if every changed slot's gates
  avoid `v`, the completions give equal `v`-values (chained `wire_u_indep`
  through the nine hybrid completions);
* **`refine_via` (proved)** — THE ONE-OF-TWO REFINEMENT: changed slots below `u`
  and avoiding `v`, equal `u`-values ⟹ equal outputs (the `v`-value is frozen,
  `refine_nineUpd2` finishes);
* **`killA2_g0/g1/g2` (proved)** — a gadget whose three sign gates avoid BOTH
  wires kills the circuit (pair-vacuous count spec + split).

The per-wire B1/B2/B3 kills and the parallel pigeonhole build on `refine_via`.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.SATFamilyDenseFloor

/-- **Nine-slot wire freezing (proved)**: changed slots avoiding `v` cannot move
`v`'s value. -/
theorem wire_frozen (N : ℕ) (h15 : 15 < N) (h21 : 21 < N) (h27 : 27 < N)
    (h34 : 34 < N) (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N) (h64 : 64 < N)
    (h72 : 72 < N)
    (c : List (CGate N)) (hs : 0 < c.length) {v : ℕ} (hv_lt : v < c.length)
    (hv_cone : InCone c v)
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ : Bool)
    (hf1 : s₁ = t₁ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨15, h15⟩ : Fin N) → ¬ Reach c v q)
    (hf2 : s₂ = t₂ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨21, h21⟩ : Fin N) → ¬ Reach c v q)
    (hf3 : s₃ = t₃ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨27, h27⟩ : Fin N) → ¬ Reach c v q)
    (hf4 : s₄ = t₄ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨34, h34⟩ : Fin N) → ¬ Reach c v q)
    (hf5 : s₅ = t₅ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨41, h41⟩ : Fin N) → ¬ Reach c v q)
    (hf6 : s₆ = t₆ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨48, h48⟩ : Fin N) → ¬ Reach c v q)
    (hf7 : s₇ = t₇ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨56, h56⟩ : Fin N) → ¬ Reach c v q)
    (hf8 : s₈ = t₈ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨64, h64⟩ : Fin N) → ¬ Reach c v q)
    (hf9 : s₉ = t₉ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨72, h72⟩ : Fin N) → ¬ Reach c v q) :
    wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉) v
      = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉) v := by
  have step1 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉) v
      = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉) v := by
    rcases hf1 with he | hall
    · rw [he]
    · conv_lhs => rw [← nineUpd_upd1 h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁]
      exact wire_u_indep c v hs hv_lt hv_cone _ _ s₁ hall
  have step2 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      t₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉) v
      = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ t₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉) v := by
    rcases hf2 with he | hall
    · rw [he]
    · conv_lhs => rw [← nineUpd_upd2 h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ t₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₂]
      exact wire_u_indep c v hs hv_lt hv_cone _ _ s₂ hall
  have step3 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      t₁ t₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉) v
      = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ t₂ t₃ s₄ s₅ s₆ s₇ s₈ s₉) v := by
    rcases hf3 with he | hall
    · rw [he]
    · conv_lhs => rw [← nineUpd_upd3 h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ t₂ t₃ s₄ s₅ s₆ s₇ s₈ s₉ s₃]
      exact wire_u_indep c v hs hv_lt hv_cone _ _ s₃ hall
  have step4 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      t₁ t₂ t₃ s₄ s₅ s₆ s₇ s₈ s₉) v
      = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ t₂ t₃ t₄ s₅ s₆ s₇ s₈ s₉) v := by
    rcases hf4 with he | hall
    · rw [he]
    · conv_lhs => rw [← nineUpd_upd4 h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ t₂ t₃ t₄ s₅ s₆ s₇ s₈ s₉ s₄]
      exact wire_u_indep c v hs hv_lt hv_cone _ _ s₄ hall
  have step5 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      t₁ t₂ t₃ t₄ s₅ s₆ s₇ s₈ s₉) v
      = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ t₂ t₃ t₄ t₅ s₆ s₇ s₈ s₉) v := by
    rcases hf5 with he | hall
    · rw [he]
    · conv_lhs => rw [← nineUpd_upd5 h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ t₂ t₃ t₄ t₅ s₆ s₇ s₈ s₉ s₅]
      exact wire_u_indep c v hs hv_lt hv_cone _ _ s₅ hall
  have step6 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      t₁ t₂ t₃ t₄ t₅ s₆ s₇ s₈ s₉) v
      = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ t₂ t₃ t₄ t₅ t₆ s₇ s₈ s₉) v := by
    rcases hf6 with he | hall
    · rw [he]
    · conv_lhs => rw [← nineUpd_upd6 h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ t₂ t₃ t₄ t₅ t₆ s₇ s₈ s₉ s₆]
      exact wire_u_indep c v hs hv_lt hv_cone _ _ s₆ hall
  have step7 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      t₁ t₂ t₃ t₄ t₅ t₆ s₇ s₈ s₉) v
      = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ t₂ t₃ t₄ t₅ t₆ t₇ s₈ s₉) v := by
    rcases hf7 with he | hall
    · rw [he]
    · conv_lhs => rw [← nineUpd_upd7 h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ t₂ t₃ t₄ t₅ t₆ t₇ s₈ s₉ s₇]
      exact wire_u_indep c v hs hv_lt hv_cone _ _ s₇ hall
  have step8 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      t₁ t₂ t₃ t₄ t₅ t₆ t₇ s₈ s₉) v
      = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ s₉) v := by
    rcases hf8 with he | hall
    · rw [he]
    · conv_lhs => rw [← nineUpd_upd8 h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ s₉ s₈]
      exact wire_u_indep c v hs hv_lt hv_cone _ _ s₈ hall
  have step9 : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ s₉) v
      = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉) v := by
    rcases hf9 with he | hall
    · rw [he]
    · conv_lhs => rw [← nineUpd_upd9 h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ s₉]
      exact wire_u_indep c v hs hv_lt hv_cone _ _ s₉ hall
  exact step1.trans (step2.trans (step3.trans (step4.trans (step5.trans
    (step6.trans (step7.trans (step8.trans step9)))))))

/-- **THE ONE-OF-TWO REFINEMENT (proved)**: changed slots below `u` and avoiding
`v`, equal `u`-values ⟹ equal outputs. -/
theorem refine_via (N : ℕ) (h15 : 15 < N) (h21 : 21 < N) (h27 : 27 < N)
    (h34 : 34 < N) (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N) (h64 : 64 < N)
    (h72 : 72 < N)
    (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    {u v : ℕ} (hR : reconvR c = {u, v})
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ : Bool)
    (hb1 : s₁ = t₁ ∨ ((∀ q ∈ cone c,
        c.getD q (.cst false) = CGate.var (⟨15, h15⟩ : Fin N) → Reach c u q)
      ∧ (∀ q ∈ cone c,
        c.getD q (.cst false) = CGate.var (⟨15, h15⟩ : Fin N) → ¬ Reach c v q)))
    (hb2 : s₂ = t₂ ∨ ((∀ q ∈ cone c,
        c.getD q (.cst false) = CGate.var (⟨21, h21⟩ : Fin N) → Reach c u q)
      ∧ (∀ q ∈ cone c,
        c.getD q (.cst false) = CGate.var (⟨21, h21⟩ : Fin N) → ¬ Reach c v q)))
    (hb3 : s₃ = t₃ ∨ ((∀ q ∈ cone c,
        c.getD q (.cst false) = CGate.var (⟨27, h27⟩ : Fin N) → Reach c u q)
      ∧ (∀ q ∈ cone c,
        c.getD q (.cst false) = CGate.var (⟨27, h27⟩ : Fin N) → ¬ Reach c v q)))
    (hb4 : s₄ = t₄ ∨ ((∀ q ∈ cone c,
        c.getD q (.cst false) = CGate.var (⟨34, h34⟩ : Fin N) → Reach c u q)
      ∧ (∀ q ∈ cone c,
        c.getD q (.cst false) = CGate.var (⟨34, h34⟩ : Fin N) → ¬ Reach c v q)))
    (hb5 : s₅ = t₅ ∨ ((∀ q ∈ cone c,
        c.getD q (.cst false) = CGate.var (⟨41, h41⟩ : Fin N) → Reach c u q)
      ∧ (∀ q ∈ cone c,
        c.getD q (.cst false) = CGate.var (⟨41, h41⟩ : Fin N) → ¬ Reach c v q)))
    (hb6 : s₆ = t₆ ∨ ((∀ q ∈ cone c,
        c.getD q (.cst false) = CGate.var (⟨48, h48⟩ : Fin N) → Reach c u q)
      ∧ (∀ q ∈ cone c,
        c.getD q (.cst false) = CGate.var (⟨48, h48⟩ : Fin N) → ¬ Reach c v q)))
    (hb7 : s₇ = t₇ ∨ ((∀ q ∈ cone c,
        c.getD q (.cst false) = CGate.var (⟨56, h56⟩ : Fin N) → Reach c u q)
      ∧ (∀ q ∈ cone c,
        c.getD q (.cst false) = CGate.var (⟨56, h56⟩ : Fin N) → ¬ Reach c v q)))
    (hb8 : s₈ = t₈ ∨ ((∀ q ∈ cone c,
        c.getD q (.cst false) = CGate.var (⟨64, h64⟩ : Fin N) → Reach c u q)
      ∧ (∀ q ∈ cone c,
        c.getD q (.cst false) = CGate.var (⟨64, h64⟩ : Fin N) → ¬ Reach c v q)))
    (hb9 : s₉ = t₉ ∨ ((∀ q ∈ cone c,
        c.getD q (.cst false) = CGate.var (⟨72, h72⟩ : Fin N) → Reach c u q)
      ∧ (∀ q ∈ cone c,
        c.getD q (.cst false) = CGate.var (⟨72, h72⟩ : Fin N) → ¬ Reach c v q)))
    (hwu : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉) u
      = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉) u) :
    SATFamily N (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉)
      = SATFamily N (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉) := by
  have hvmem : v ∈ reconvR c := by
    rw [hR]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
  obtain ⟨hvne, hvc⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp hvmem).1
  have hwv := wire_frozen N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hs
    ((mem_cone.mp hvc).1) ((mem_cone.mp hvc).2)
    s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
    (hb1.imp_right And.right) (hb2.imp_right And.right) (hb3.imp_right And.right)
    (hb4.imp_right And.right) (hb5.imp_right And.right) (hb6.imp_right And.right)
    (hb7.imp_right And.right) (hb8.imp_right And.right) (hb9.imp_right And.right)
  exact refine_nineUpd2 N h15 h21 h27 h34 h41 h48 h56 h64 h72 c hcomp hs hR
    s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
    (hb1.imp_right (fun h q hq hg => Or.inl (h.1 q hq hg)))
    (hb2.imp_right (fun h q hq hg => Or.inl (h.1 q hq hg)))
    (hb3.imp_right (fun h q hq hg => Or.inl (h.1 q hq hg)))
    (hb4.imp_right (fun h q hq hg => Or.inl (h.1 q hq hg)))
    (hb5.imp_right (fun h q hq hg => Or.inl (h.1 q hq hg)))
    (hb6.imp_right (fun h q hq hg => Or.inl (h.1 q hq hg)))
    (hb7.imp_right (fun h q hq hg => Or.inl (h.1 q hq hg)))
    (hb8.imp_right (fun h q hq hg => Or.inl (h.1 q hq hg)))
    (hb9.imp_right (fun h q hq hg => Or.inl (h.1 q hq hg)))
    hwu hwv

/-! ### The pair-vacuous A-kills -/

section KillA2

variable (N : ℕ) (hN : 73 ≤ N) (h15 : 15 < N) (h21 : 21 < N) (h27 : 27 < N)
  (h34 : 34 < N) (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N) (h64 : 64 < N)
  (h72 : 72 < N)
  (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
  (hWd : (coneVars c).card ≤ (depSet (SATFamily N)).card)

include hN h15 h21 h27 h34 h41 h48 h56 h64 h72 hcomp hs hWd

/-- **Kill A at two wires, gadget 0 (proved)**. -/
theorem killA2_g0 {u₁ u₂ : ℕ} (hR : reconvR c = {u₁, u₂}) {q15 q21 q27 : ℕ}
    (hq15c : q15 ∈ cone c) (hq15g : c.getD q15 (.cst false) = CGate.var ⟨15, h15⟩)
    (hnb15a : ¬ Reach c u₁ q15) (hnb15b : ¬ Reach c u₂ q15)
    (hq21c : q21 ∈ cone c) (hq21g : c.getD q21 (.cst false) = CGate.var ⟨21, h21⟩)
    (hnb21a : ¬ Reach c u₁ q21) (hnb21b : ¬ Reach c u₂ q21)
    (hq27c : q27 ∈ cone c) (hq27g : c.getD q27 (.cst false) = CGate.var ⟨27, h27⟩)
    (hnb27a : ¬ Reach c u₁ q27) (hnb27b : ¬ Reach c u₂ q27) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd15 := sign15_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd21 := sign21_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd27 := sign27_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hroot : c.length - 1 ∈ cone c := mem_cone.mpr ⟨by omega, InCone.root⟩
  have hRv : ∀ q₀ : ℕ, ¬ Reach c u₁ q₀ → ¬ Reach c u₂ q₀ →
      ∀ u' ∈ reconvR c, ¬ Reach c u' q₀ := by
    intro q₀ hn₁ hn₂ u' hu'
    rw [hR] at hu'
    rcases Finset.mem_insert.mp hu' with h | h
    · rw [h]; exact hn₁
    · rw [Finset.mem_singleton.mp h]; exact hn₂
  have hcnt15 := (extractG_cnt_spec c hs ⟨15, h15⟩ q15 hq15c hq15g
      (fun q hq hg => huniq ⟨15, h15⟩ hd15 q hq q15 hq15c hg hq15g)
      (hRv q15 hnb15a hnb15b) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq15c).2)
  have hcnt21 := (extractG_cnt_spec c hs ⟨21, h21⟩ q21 hq21c hq21g
      (fun q hq hg => huniq ⟨21, h21⟩ hd21 q hq q21 hq21c hg hq21g)
      (hRv q21 hnb21a hnb21b) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq21c).2)
  have hcnt27 := (extractG_cnt_spec c hs ⟨27, h27⟩ q27 hq27c hq27g
      (fun q hq hg => huniq ⟨27, h27⟩ hd27 q hq q27 hq27c hg hq27g)
      (hRv q27 hnb27a hnb27b) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq27c).2)
  have hsp := gtree_split_cnt (extractG c c.length (c.length - 1))
    ⟨15, h15⟩ ⟨21, h21⟩ ⟨27, h27⟩
    (fne h15 h21 (by omega)) (fne h15 h27 (by omega)) (fne h21 h27 (by omega))
    (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true true true true)
    hcnt15 hcnt21 hcnt27
  have heval : ∀ y, (extractG c c.length (c.length - 1)).eval y = SATFamily N y := by
    intro y
    rw [extractG_eval c c.length (c.length - 1) (by omega) (by omega) y]
    exact hcomp y
  have heq : (fun a b g => (extractG c c.length (c.length - 1)).eval
      (Function.update (Function.update (Function.update
        (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true true true true true true true)
        ⟨15, h15⟩ a) ⟨21, h21⟩ b) ⟨27, h27⟩ g)) = allEq3 := by
    funext a b g
    rw [nineUpd_upd1, nineUpd_upd2, nineUpd_upd3, heval,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        a b g true true true true true true]
    simp only [show allEq3 true true true = true from rfl, Bool.and_true]
  rw [heq] at hsp
  rcases hsp with h | h | h
  · exact allEq3_no_split_a h
  · exact allEq3_no_split_b h
  · exact allEq3_no_split_c h

/-- **Kill A at two wires, gadget 1 (proved)**. -/
theorem killA2_g1 {u₁ u₂ : ℕ} (hR : reconvR c = {u₁, u₂}) {q34 q41 q48 : ℕ}
    (hq34c : q34 ∈ cone c) (hq34g : c.getD q34 (.cst false) = CGate.var ⟨34, h34⟩)
    (hnb34a : ¬ Reach c u₁ q34) (hnb34b : ¬ Reach c u₂ q34)
    (hq41c : q41 ∈ cone c) (hq41g : c.getD q41 (.cst false) = CGate.var ⟨41, h41⟩)
    (hnb41a : ¬ Reach c u₁ q41) (hnb41b : ¬ Reach c u₂ q41)
    (hq48c : q48 ∈ cone c) (hq48g : c.getD q48 (.cst false) = CGate.var ⟨48, h48⟩)
    (hnb48a : ¬ Reach c u₁ q48) (hnb48b : ¬ Reach c u₂ q48) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd34 := sign34_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd41 := sign41_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd48 := sign48_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hroot : c.length - 1 ∈ cone c := mem_cone.mpr ⟨by omega, InCone.root⟩
  have hRv : ∀ q₀ : ℕ, ¬ Reach c u₁ q₀ → ¬ Reach c u₂ q₀ →
      ∀ u' ∈ reconvR c, ¬ Reach c u' q₀ := by
    intro q₀ hn₁ hn₂ u' hu'
    rw [hR] at hu'
    rcases Finset.mem_insert.mp hu' with h | h
    · rw [h]; exact hn₁
    · rw [Finset.mem_singleton.mp h]; exact hn₂
  have hcnt34 := (extractG_cnt_spec c hs ⟨34, h34⟩ q34 hq34c hq34g
      (fun q hq hg => huniq ⟨34, h34⟩ hd34 q hq q34 hq34c hg hq34g)
      (hRv q34 hnb34a hnb34b) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq34c).2)
  have hcnt41 := (extractG_cnt_spec c hs ⟨41, h41⟩ q41 hq41c hq41g
      (fun q hq hg => huniq ⟨41, h41⟩ hd41 q hq q41 hq41c hg hq41g)
      (hRv q41 hnb41a hnb41b) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq41c).2)
  have hcnt48 := (extractG_cnt_spec c hs ⟨48, h48⟩ q48 hq48c hq48g
      (fun q hq hg => huniq ⟨48, h48⟩ hd48 q hq q48 hq48c hg hq48g)
      (hRv q48 hnb48a hnb48b) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq48c).2)
  have hsp := gtree_split_cnt (extractG c c.length (c.length - 1))
    ⟨34, h34⟩ ⟨41, h41⟩ ⟨48, h48⟩
    (fne h34 h41 (by omega)) (fne h34 h48 (by omega)) (fne h41 h48 (by omega))
    (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true true true true)
    hcnt34 hcnt41 hcnt48
  have heval : ∀ y, (extractG c c.length (c.length - 1)).eval y = SATFamily N y := by
    intro y
    rw [extractG_eval c c.length (c.length - 1) (by omega) (by omega) y]
    exact hcomp y
  have heq : (fun a b g => (extractG c c.length (c.length - 1)).eval
      (Function.update (Function.update (Function.update
        (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true true true true true true true)
        ⟨34, h34⟩ a) ⟨41, h41⟩ b) ⟨48, h48⟩ g)) = allEq3 := by
    funext a b g
    rw [nineUpd_upd4, nineUpd_upd5, nineUpd_upd6, heval,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true a b g true true true]
    simp only [show allEq3 true true true = true from rfl, Bool.and_true, Bool.true_and]
  rw [heq] at hsp
  rcases hsp with h | h | h
  · exact allEq3_no_split_a h
  · exact allEq3_no_split_b h
  · exact allEq3_no_split_c h

/-- **Kill A at two wires, gadget 2 (proved)**. -/
theorem killA2_g2 {u₁ u₂ : ℕ} (hR : reconvR c = {u₁, u₂}) {q56 q64 q72 : ℕ}
    (hq56c : q56 ∈ cone c) (hq56g : c.getD q56 (.cst false) = CGate.var ⟨56, h56⟩)
    (hnb56a : ¬ Reach c u₁ q56) (hnb56b : ¬ Reach c u₂ q56)
    (hq64c : q64 ∈ cone c) (hq64g : c.getD q64 (.cst false) = CGate.var ⟨64, h64⟩)
    (hnb64a : ¬ Reach c u₁ q64) (hnb64b : ¬ Reach c u₂ q64)
    (hq72c : q72 ∈ cone c) (hq72g : c.getD q72 (.cst false) = CGate.var ⟨72, h72⟩)
    (hnb72a : ¬ Reach c u₁ q72) (hnb72b : ¬ Reach c u₂ q72) : False := by
  have huniq := unique_var_gate (SATFamily N) c hcomp hs hWd
  have hd56 := sign56_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd64 := sign64_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hd72 := sign72_dep9 N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
  have hroot : c.length - 1 ∈ cone c := mem_cone.mpr ⟨by omega, InCone.root⟩
  have hRv : ∀ q₀ : ℕ, ¬ Reach c u₁ q₀ → ¬ Reach c u₂ q₀ →
      ∀ u' ∈ reconvR c, ¬ Reach c u' q₀ := by
    intro q₀ hn₁ hn₂ u' hu'
    rw [hR] at hu'
    rcases Finset.mem_insert.mp hu' with h | h
    · rw [h]; exact hn₁
    · rw [Finset.mem_singleton.mp h]; exact hn₂
  have hcnt56 := (extractG_cnt_spec c hs ⟨56, h56⟩ q56 hq56c hq56g
      (fun q hq hg => huniq ⟨56, h56⟩ hd56 q hq q56 hq56c hg hq56g)
      (hRv q56 hnb56a hnb56b) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq56c).2)
  have hcnt64 := (extractG_cnt_spec c hs ⟨64, h64⟩ q64 hq64c hq64g
      (fun q hq hg => huniq ⟨64, h64⟩ hd64 q hq q64 hq64c hg hq64g)
      (hRv q64 hnb64a hnb64b) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq64c).2)
  have hcnt72 := (extractG_cnt_spec c hs ⟨72, h72⟩ q72 hq72c hq72g
      (fun q hq hg => huniq ⟨72, h72⟩ hd72 q hq q72 hq72c hg hq72g)
      (hRv q72 hnb72a hnb72b) c.length (c.length - 1) (by omega) hroot).1
      (inCone_reach_root (mem_cone.mp hq72c).2)
  have hsp := gtree_split_cnt (extractG c c.length (c.length - 1))
    ⟨56, h56⟩ ⟨64, h64⟩ ⟨72, h72⟩
    (fne h56 h64 (by omega)) (fne h56 h72 (by omega)) (fne h64 h72 (by omega))
    (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
      true true true true true true true true true)
    hcnt56 hcnt64 hcnt72
  have heval : ∀ y, (extractG c c.length (c.length - 1)).eval y = SATFamily N y := by
    intro y
    rw [extractG_eval c c.length (c.length - 1) (by omega) (by omega) y]
    exact hcomp y
  have heq : (fun a b g => (extractG c c.length (c.length - 1)).eval
      (Function.update (Function.update (Function.update
        (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
          true true true true true true true true true)
        ⟨56, h56⟩ a) ⟨64, h64⟩ b) ⟨72, h72⟩ g)) = allEq3 := by
    funext a b g
    rw [nineUpd_upd7, nineUpd_upd8, nineUpd_upd9, heval,
      SATFamily_nineUpd N hN h15 h21 h27 h34 h41 h48 h56 h64 h72
        true true true true true true a b g]
    simp only [show allEq3 true true true = true from rfl, Bool.true_and]
  rw [heq] at hsp
  rcases hsp with h | h | h
  · exact allEq3_no_split_a h
  · exact allEq3_no_split_b h
  · exact allEq3_no_split_c h

end KillA2

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.wire_frozen
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.refine_via
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.killA2_g0
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.killA2_g2
