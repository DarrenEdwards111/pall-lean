import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATKillOne3B

/-!
# The two-cut lemma: the circuit above TWO reconvergence wires

Multi-wire brick 6 — the case-(iii) foundation.  With `reconvR c = {u₁, u₂}`,
the circuit above the two wires sees the below-region only through the PAIR of
bits:

* **`read_structure2` (proved)** — a cone wire below neither `u₁` nor `u₂` reads
  only `u₁`, `u₂`, or other below-neither wires (a below read's second reader
  would be a third reconvergence);
* **`cut_agree2` (proved)** — THE TWO-CUT LEMMA: equal values at BOTH wires plus
  agreement at every coordinate owning a below-neither var gate force equal
  values on every below-neither wire — in particular at the root;
* **`refine_nineUpd2` (proved)** — the nine-slot master refinement at two wires:
  changed slots below-at-least-one + equal wire-pair ⟹ equal outputs.

Note `wire_u_indep` needs no reconvergence hypothesis at all, so per-wire
mediator-independence carries over unchanged.  The case-(iii) kill analysis
builds on these.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.SATFamilyDenseFloor

/-- **The two-wire read structure (proved)**: below neither wire, reads hit only
the wires themselves or other below-neither wires. -/
theorem read_structure2 {n : ℕ} (c : List (CGate n)) (u₁ u₂ : ℕ) (hs : 0 < c.length)
    (hR : reconvR c = {u₁, u₂}) (hu₁ : InCone c u₁) (hu₂ : InCone c u₂)
    {w j : ℕ} (hw : w ∈ cone c) (hnb₁ : ¬ Reach c u₁ w) (hnb₂ : ¬ Reach c u₂ w)
    (hj : j ∈ gateReads (c.getD w (.cst false))) (hjw : j < w) :
    j = u₁ ∨ j = u₂ ∨ (¬ Reach c u₁ j ∧ ¬ Reach c u₂ j) := by
  by_cases hju₁ : j = u₁
  · exact Or.inl hju₁
  by_cases hju₂ : j = u₂
  · exact Or.inr (Or.inl hju₂)
  refine Or.inr (Or.inr ⟨?_, ?_⟩)
  · intro hreach
    obtain ⟨p, hp, hjp, hjlt⟩ :
        ∃ p, Reach c u₁ p ∧ j ∈ gateReads (c.getD p (.cst false)) ∧ j < p := by
      cases hreach with
      | refl => exact absurd rfl hju₁
      | step hp hq hlt => exact ⟨_, hp, hq, hlt⟩
    by_cases hpw : p = w
    · rw [hpw] at hp
      exact hnb₁ hp
    · have hpic : InCone c p := reach_inCone hu₁ hp
      have hpc : p ∈ cone c := mem_cone.mpr ⟨inCone_lt hs hpic, hpic⟩
      have hwlt : w < c.length := (mem_cone.mp hw).1
      have hjc : j ∈ cone c :=
        mem_cone.mpr ⟨by omega, InCone.step (mem_cone.mp hw).2 hj hjw⟩
      have hjroot : j ≠ c.length - 1 := by omega
      have hmem := two_readers_mem_reconv c hw hpc (fun he => hpw he.symm)
        hj hjp hjc hjroot
      rw [hR] at hmem
      rcases Finset.mem_insert.mp hmem with h | h
      · exact hju₁ h
      · exact hju₂ (Finset.mem_singleton.mp h)
  · intro hreach
    obtain ⟨p, hp, hjp, hjlt⟩ :
        ∃ p, Reach c u₂ p ∧ j ∈ gateReads (c.getD p (.cst false)) ∧ j < p := by
      cases hreach with
      | refl => exact absurd rfl hju₂
      | step hp hq hlt => exact ⟨_, hp, hq, hlt⟩
    by_cases hpw : p = w
    · rw [hpw] at hp
      exact hnb₂ hp
    · have hpic : InCone c p := reach_inCone hu₂ hp
      have hpc : p ∈ cone c := mem_cone.mpr ⟨inCone_lt hs hpic, hpic⟩
      have hwlt : w < c.length := (mem_cone.mp hw).1
      have hjc : j ∈ cone c :=
        mem_cone.mpr ⟨by omega, InCone.step (mem_cone.mp hw).2 hj hjw⟩
      have hjroot : j ≠ c.length - 1 := by omega
      have hmem := two_readers_mem_reconv c hw hpc (fun he => hpw he.symm)
        hj hjp hjc hjroot
      rw [hR] at hmem
      rcases Finset.mem_insert.mp hmem with h | h
      · exact hju₁ h
      · exact hju₂ (Finset.mem_singleton.mp h)

/-- **THE TWO-CUT LEMMA (proved)**: equal wire-pair values plus below-neither
agreement force equal values on every below-neither wire. -/
theorem cut_agree2 {n : ℕ} (c : List (CGate n)) (u₁ u₂ : ℕ) (hs : 0 < c.length)
    (hR : reconvR c = {u₁, u₂}) (hu₁ : InCone c u₁) (hu₂ : InCone c u₂)
    (x x' : Fin n → Bool)
    (hwu₁ : wire c x u₁ = wire c x' u₁) (hwu₂ : wire c x u₂ = wire c x' u₂)
    (hagree : ∀ i : Fin n,
      (∃ q, q ∈ cone c ∧ c.getD q (.cst false) = CGate.var i ∧
        ¬ Reach c u₁ q ∧ ¬ Reach c u₂ q) →
      x i = x' i) :
    ∀ w, w ∈ cone c → ¬ Reach c u₁ w → ¬ Reach c u₂ w →
      wire c x w = wire c x' w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwc hnb₁ hnb₂
    have hwlt : w < c.length := (mem_cone.mp hwc).1
    rw [wire_eq c x hwlt, wire_eq c x' hwlt]
    have hread : ∀ m : ℕ, m ∈ gateReads (c.getD w (.cst false)) → m < w →
        wire c x m = wire c x' m := by
      intro m hmr hmw
      have hmc : m ∈ cone c :=
        mem_cone.mpr ⟨by omega, InCone.step (mem_cone.mp hwc).2 hmr hmw⟩
      rcases read_structure2 c u₁ u₂ hs hR hu₁ hu₂ hwc hnb₁ hnb₂ hmr hmw with
        hm1 | hm2 | ⟨hn1, hn2⟩
      · rw [hm1]; exact hwu₁
      · rw [hm2]; exact hwu₂
      · exact ih m hmw hmc hn1 hn2
    have hgetD : ∀ m : ℕ, m ∈ gateReads (c.getD w (.cst false)) →
        (runFrom x [] (c.take w)).getD m false
          = (runFrom x' [] (c.take w)).getD m false := by
      intro m hmr
      by_cases hmw : m < w
      · rw [wire_prefix c x hmw (le_of_lt hwlt), wire_prefix c x' hmw (le_of_lt hwlt)]
        exact hread m hmr hmw
      · have hlen : (runFrom x [] (c.take w)).length = w := by
          rw [runFrom_length, List.length_take]
          simp
          omega
        have hlen' : (runFrom x' [] (c.take w)).length = w := by
          rw [runFrom_length, List.length_take]
          simp
          omega
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    cases hg : c.getD w (.cst false) with
    | var i =>
      show x i = x' i
      refine hagree i ⟨w, hwc, hg, hnb₁, hnb₂⟩
    | cst b => rfl
    | un op j =>
      show op ((runFrom x [] (c.take w)).getD j false)
        = op ((runFrom x' [] (c.take w)).getD j false)
      rw [hgetD j (by rw [hg]; exact Finset.mem_singleton_self j)]
    | bin op j k =>
      show op ((runFrom x [] (c.take w)).getD j false)
          ((runFrom x [] (c.take w)).getD k false)
        = op ((runFrom x' [] (c.take w)).getD j false)
          ((runFrom x' [] (c.take w)).getD k false)
      rw [hgetD j (by rw [hg]; exact Finset.mem_insert_self j {k}),
        hgetD k (by rw [hg]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self k))]

/-! ### The nine-slot master refinement at two wires -/

/-- **The two-wire master refinement (proved)**: changed slots below at least one
wire, equal values at BOTH wires ⟹ equal outputs. -/
theorem refine_nineUpd2 (N : ℕ) (h15 : 15 < N) (h21 : 21 < N) (h27 : 27 < N)
    (h34 : 34 < N) (h41 : 41 < N) (h48 : 48 < N) (h56 : 56 < N) (h64 : 64 < N)
    (h72 : 72 < N)
    (c : List (CGate N)) (hcomp : computes c (SATFamily N)) (hs : 0 < c.length)
    {u₁ u₂ : ℕ} (hR : reconvR c = {u₁, u₂})
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ : Bool)
    (hb1 : s₁ = t₁ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨15, h15⟩ : Fin N) →
      (Reach c u₁ q ∨ Reach c u₂ q))
    (hb2 : s₂ = t₂ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨21, h21⟩ : Fin N) →
      (Reach c u₁ q ∨ Reach c u₂ q))
    (hb3 : s₃ = t₃ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨27, h27⟩ : Fin N) →
      (Reach c u₁ q ∨ Reach c u₂ q))
    (hb4 : s₄ = t₄ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨34, h34⟩ : Fin N) →
      (Reach c u₁ q ∨ Reach c u₂ q))
    (hb5 : s₅ = t₅ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨41, h41⟩ : Fin N) →
      (Reach c u₁ q ∨ Reach c u₂ q))
    (hb6 : s₆ = t₆ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨48, h48⟩ : Fin N) →
      (Reach c u₁ q ∨ Reach c u₂ q))
    (hb7 : s₇ = t₇ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨56, h56⟩ : Fin N) →
      (Reach c u₁ q ∨ Reach c u₂ q))
    (hb8 : s₈ = t₈ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨64, h64⟩ : Fin N) →
      (Reach c u₁ q ∨ Reach c u₂ q))
    (hb9 : s₉ = t₉ ∨ ∀ q ∈ cone c,
      c.getD q (.cst false) = CGate.var (⟨72, h72⟩ : Fin N) →
      (Reach c u₁ q ∨ Reach c u₂ q))
    (hwu₁ : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉) u₁
      = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉) u₁)
    (hwu₂ : wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉) u₂
      = wire c (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉) u₂) :
    SATFamily N (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉)
      = SATFamily N (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72
        t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉) := by
  have hu₁mem : u₁ ∈ reconvR c := by
    rw [hR]
    exact Finset.mem_insert_self u₁ {u₂}
  have hu₂mem : u₂ ∈ reconvR c := by
    rw [hR]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self u₂)
  obtain ⟨hu₁ne, hu₁c⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp hu₁mem).1
  obtain ⟨hu₂ne, hu₂c⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp hu₂mem).1
  have hu₁lt : u₁ < c.length := (mem_cone.mp hu₁c).1
  have hu₂lt : u₂ < c.length := (mem_cone.mp hu₂c).1
  have hroot_nb₁ : ¬ Reach c u₁ (c.length - 1) := by
    intro hr
    have h1 := reach_le hr
    exact hu₁ne (by omega)
  have hroot_nb₂ : ¬ Reach c u₂ (c.length - 1) := by
    intro hr
    have h1 := reach_le hr
    exact hu₂ne (by omega)
  have hagree : ∀ i : Fin N,
      (∃ q, q ∈ cone c ∧ c.getD q (.cst false) = CGate.var i ∧
        ¬ Reach c u₁ q ∧ ¬ Reach c u₂ q) →
      nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ i
        = nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ i := by
    intro i hex
    obtain ⟨q, hqc, hqg, hqnb₁, hqnb₂⟩ := hex
    by_cases e1 : i = ⟨15, h15⟩
    · subst e1
      rw [nineUpd_at15, nineUpd_at15]
      rcases hb1 with he | hall
      · exact he
      · rcases hall q hqc hqg with h | h
        · exact absurd h hqnb₁
        · exact absurd h hqnb₂
    by_cases e2 : i = ⟨21, h21⟩
    · subst e2
      rw [nineUpd_at21, nineUpd_at21]
      rcases hb2 with he | hall
      · exact he
      · rcases hall q hqc hqg with h | h
        · exact absurd h hqnb₁
        · exact absurd h hqnb₂
    by_cases e3 : i = ⟨27, h27⟩
    · subst e3
      rw [nineUpd_at27, nineUpd_at27]
      rcases hb3 with he | hall
      · exact he
      · rcases hall q hqc hqg with h | h
        · exact absurd h hqnb₁
        · exact absurd h hqnb₂
    by_cases e4 : i = ⟨34, h34⟩
    · subst e4
      rw [nineUpd_at34, nineUpd_at34]
      rcases hb4 with he | hall
      · exact he
      · rcases hall q hqc hqg with h | h
        · exact absurd h hqnb₁
        · exact absurd h hqnb₂
    by_cases e5 : i = ⟨41, h41⟩
    · subst e5
      rw [nineUpd_at41, nineUpd_at41]
      rcases hb5 with he | hall
      · exact he
      · rcases hall q hqc hqg with h | h
        · exact absurd h hqnb₁
        · exact absurd h hqnb₂
    by_cases e6 : i = ⟨48, h48⟩
    · subst e6
      rw [nineUpd_at48, nineUpd_at48]
      rcases hb6 with he | hall
      · exact he
      · rcases hall q hqc hqg with h | h
        · exact absurd h hqnb₁
        · exact absurd h hqnb₂
    by_cases e7 : i = ⟨56, h56⟩
    · subst e7
      rw [nineUpd_at56, nineUpd_at56]
      rcases hb7 with he | hall
      · exact he
      · rcases hall q hqc hqg with h | h
        · exact absurd h hqnb₁
        · exact absurd h hqnb₂
    by_cases e8 : i = ⟨64, h64⟩
    · subst e8
      rw [nineUpd_at64, nineUpd_at64]
      rcases hb8 with he | hall
      · exact he
      · rcases hall q hqc hqg with h | h
        · exact absurd h hqnb₁
        · exact absurd h hqnb₂
    by_cases e9 : i = ⟨72, h72⟩
    · subst e9
      rw [nineUpd_at72, nineUpd_at72]
      rcases hb9 with he | hall
      · exact he
      · rcases hall q hqc hqg with h | h
        · exact absurd h hqnb₁
        · exact absurd h hqnb₂
    rw [nineUpd_at_other h15 h21 h27 h34 h41 h48 h56 h64 h72 _ _ _ _ _ _ _ _ _
        i e1 e2 e3 e4 e5 e6 e7 e8 e9,
      nineUpd_at_other h15 h21 h27 h34 h41 h48 h56 h64 h72 _ _ _ _ _ _ _ _ _
        i e1 e2 e3 e4 e5 e6 e7 e8 e9]
  have hcut := cut_agree2 c u₁ u₂ hs hR ((mem_cone.mp hu₁c).2) ((mem_cone.mp hu₂c).2)
    (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉)
    (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉)
    hwu₁ hwu₂ hagree (c.length - 1)
    (mem_cone.mpr ⟨by omega, InCone.root⟩) hroot_nb₁ hroot_nb₂
  rw [← hcomp (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉),
    ← hcomp (nineUpd N h15 h21 h27 h34 h41 h48 h56 h64 h72 t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉),
    output_eq_wire, output_eq_wire]
  exact hcut

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.read_structure2
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cut_agree2
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.refine_nineUpd2
