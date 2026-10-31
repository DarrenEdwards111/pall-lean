import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMultiSwap

/-!
# Brick E of the ∀m `SlackComposes` campaign: the mediated dichotomy

The first-branch-point argument: below the first reconvergence the reader chain
is deterministic, so a single-gated variable either has unwinding count exactly
one or every clean path misses its gate:

* `cleanIn_inCone` — clean reachability is cone reachability;
* **`cleanIn_no_reconv_reach` (proved)** — a cleanly reachable non-reconvergence
  wire is not reachable from any reconvergence wire (the deterministic chain
  climb: the clean derivation and the reconvergence path would have to share
  readers, and clean readers avoid `R`);
* **`extractG_cnt_spec` (proved)** — for a variable with a unique var gate that
  no reconvergence reaches, the unwinding count from any cone position is
  exactly [position reaches the gate] (degenerate double reads are absorbed by
  slot multiplicity: the doubly-read child is itself a reconvergence);
* `multiSwap_blind'` — blindness from the mediated form of the hypothesis;
* **`gadget_dichotomy` (proved)** — every gadget of `AEm m` has a variable that
  is either *mediated* (every clean path misses its gates outside `R`) or
  *duplicated* (two distinct cone var gates).

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

theorem cleanIn_inCone {n : ℕ} {c : List (CGate n)} {R : Finset ℕ} {q : ℕ}
    (h : CleanIn c R q) : InCone c q := by
  induction h with
  | root => exact InCone.root
  | step hw hnR ht hlt ih => exact InCone.step ih ht hlt

/-- **No reconvergence wire reaches a cleanly reachable non-reconvergence wire
(proved)** — the deterministic chain climb. -/
theorem cleanIn_no_reconv_reach {n : ℕ} (c : List (CGate n)) (hs : 0 < c.length)
    {q₀ : ℕ} (hcl : CleanIn c (reconvR c) q₀) (hq₀R : q₀ ∉ reconvR c) :
    ∀ u ∈ reconvR c, ¬ Reach c u q₀ := by
  intro u huR hru
  have hu_cone : u ∈ cone c :=
    (Finset.mem_erase.mp (Finset.mem_filter.mp huR).1).2
  have hult : u < c.length := (mem_cone.mp hu_cone).1
  have climb : ∀ (mm q : ℕ), c.length - q ≤ mm → CleanIn c (reconvR c) q →
      q ∉ reconvR c → Reach c u q → False := by
    intro mm
    induction mm with
    | zero =>
      intro q hq hcl' hqR hr
      have h1 := reach_le hr
      omega
    | succ mm ih =>
      intro q hq hcl' hqR hr
      by_cases hqu : q = u
      · rw [hqu] at hqR
        exact hqR huR
      · obtain ⟨p, hup, hqp, hqlt⟩ := reach_last hr hqu
        cases hcl' with
        | root =>
          have := reach_le hup
          omega
        | step hclw hwR hqr hqlt' =>
          rename_i w'
          have hw'lt : w' < c.length := inCone_lt hs (cleanIn_inCone hclw)
          have hple := reach_le hup
          have hpc : p ∈ cone c := mem_cone.mpr ⟨by omega,
            reach_inCone (mem_cone.mp hu_cone).2 hup⟩
          have hw'c : w' ∈ cone c := mem_cone.mpr ⟨hw'lt, cleanIn_inCone hclw⟩
          have hqe : q ∈ (cone c).erase (c.length - 1) := by
            refine Finset.mem_erase.mpr ⟨by omega, ?_⟩
            exact mem_cone.mpr ⟨by omega, InCone.step (cleanIn_inCone hclw) hqr hqlt'⟩
          have hpw : w' = p :=
            readers_unique_of_not_reconv c hs hqe hqR hw'c hpc hqr hqp
          exact ih p (by omega) (hpw ▸ hclw) (hpw ▸ hwR) hup
  exact climb c.length q₀ (by omega) hcl hq₀R hru

/-- Reach-based not-both, away from all reconvergences above the target. -/
theorem clean_reach_not_both {n : ℕ} (c : List (CGate n)) (hs : 0 < c.length)
    {w j k : ℕ} (hwc : w ∈ cone c)
    (hj : j ∈ gateReads (c.getD w (.cst false))) (hjw : j < w)
    (hk : k ∈ gateReads (c.getD w (.cst false))) (hkw : k < w)
    (hjk : j ≠ k) {q₀ : ℕ}
    (hRq₀ : ∀ u ∈ reconvR c, ¬ Reach c u q₀) :
    ∀ (mm q : ℕ), c.length - q ≤ mm → Reach c j q → Reach c k q →
      Reach c q q₀ → False := by
  have hwlt : w < c.length := (mem_cone.mp hwc).1
  have hwic : InCone c w := (mem_cone.mp hwc).2
  have hjc : j ∈ cone c := mem_cone.mpr ⟨by omega, InCone.step hwic hj hjw⟩
  have hkc : k ∈ cone c := mem_cone.mpr ⟨by omega, InCone.step hwic hk hkw⟩
  intro mm
  induction mm with
  | zero =>
    intro q hq hrj _ _
    have := reach_le hrj
    have := (mem_cone.mp hjc).1
    omega
  | succ mm ih =>
    intro q hq hrj hrk hrq₀
    have hqR : q ∉ reconvR c := fun hqmem => hRq₀ q hqmem hrq₀
    by_cases hqj : q = j
    · subst hqj
      obtain ⟨p, hpk, hqp, hqlt⟩ := reach_last hrk hjk
      have hpic : InCone c p := reach_inCone (mem_cone.mp hkc).2 hpk
      have hpc : p ∈ cone c := mem_cone.mpr ⟨inCone_lt hs hpic, hpic⟩
      have hqe : q ∈ (cone c).erase (c.length - 1) :=
        Finset.mem_erase.mpr ⟨by omega, hjc⟩
      have hpw : p = w :=
        readers_unique_of_not_reconv c hs hqe hqR hpc hwc hqp hj
      rw [hpw] at hpk
      have := reach_le hpk
      omega
    · by_cases hqk : q = k
      · subst hqk
        obtain ⟨p, hpj, hqp, hqlt⟩ := reach_last hrj (Ne.symm hjk)
        have hpic : InCone c p := reach_inCone (mem_cone.mp hjc).2 hpj
        have hpc : p ∈ cone c := mem_cone.mpr ⟨inCone_lt hs hpic, hpic⟩
        have hqe : q ∈ (cone c).erase (c.length - 1) :=
          Finset.mem_erase.mpr ⟨by omega, hkc⟩
        have hpw : p = w :=
          readers_unique_of_not_reconv c hs hqe hqR hpc hwc hqp hk
        rw [hpw] at hpj
        have := reach_le hpj
        omega
      · obtain ⟨p₁, hp₁, hqr₁, hql₁⟩ := reach_last hrj hqj
        obtain ⟨p₂, hp₂, hqr₂, hql₂⟩ := reach_last hrk hqk
        have hp₁ic : InCone c p₁ := reach_inCone (mem_cone.mp hjc).2 hp₁
        have hp₂ic : InCone c p₂ := reach_inCone (mem_cone.mp hkc).2 hp₂
        have hp₁c : p₁ ∈ cone c := mem_cone.mpr ⟨inCone_lt hs hp₁ic, hp₁ic⟩
        have hp₂c : p₂ ∈ cone c := mem_cone.mpr ⟨inCone_lt hs hp₂ic, hp₂ic⟩
        have hp₁le := reach_le hp₁
        have hjlt := (mem_cone.mp hjc).1
        have hqc : q ∈ cone c :=
          mem_cone.mpr ⟨by omega, InCone.step hp₁ic hqr₁ hql₁⟩
        have hqe : q ∈ (cone c).erase (c.length - 1) :=
          Finset.mem_erase.mpr ⟨by omega, hqc⟩
        have h12' : p₁ = p₂ :=
          readers_unique_of_not_reconv c hs hqe hqR hp₁c hp₂c hqr₁ hqr₂
        rw [← h12'] at hp₂
        exact ih p₁ (by omega) hp₁ hp₂
          (reach_trans (Reach.step (Reach.refl p₁) hqr₁ hql₁) hrq₀)

/-- **The count spec away from reconvergences (proved)**: for a variable with a
unique var gate that no reconvergence reaches, the unwinding count from any cone
position is exactly [position reaches the gate]. -/
theorem extractG_cnt_spec {n : ℕ} (c : List (CGate n)) (hs : 0 < c.length)
    (i : Fin n) (q₀ : ℕ) (hq₀c : q₀ ∈ cone c)
    (hgq₀ : c.getD q₀ (.cst false) = CGate.var i)
    (huniq : ∀ q ∈ cone c, c.getD q (.cst false) = CGate.var i → q = q₀)
    (hRq₀ : ∀ u ∈ reconvR c, ¬ Reach c u q₀) :
    ∀ (fuel w : ℕ), w < fuel → w ∈ cone c →
      (Reach c w q₀ → (extractG c fuel w).cnt i = 1)
      ∧ (¬ Reach c w q₀ → (extractG c fuel w).cnt i = 0) := by
  intro fuel
  induction fuel with
  | zero => intro w hw _; exact absurd hw (Nat.not_lt_zero w)
  | succ fuel ih =>
    intro w hw hwc
    have hwlt : w < c.length := (mem_cone.mp hwc).1
    have hwic : InCone c w := (mem_cone.mp hwc).2
    cases hg : c.getD w (.cst false) with
    | var i' =>
      simp only [extractG]
      rw [hg]
      by_cases hii : i' = i
      · subst hii
        have hwq₀ : w = q₀ := huniq w hwc hg
        constructor
        · intro _
          show (if i' = i' then 1 else 0) = 1
          rw [if_pos rfl]
        · intro hnr
          exact absurd (by rw [hwq₀]; exact Reach.refl q₀) hnr
      · constructor
        · intro hr
          exfalso
          have hq₀w := reach_var_stuck hg hr
          rw [hq₀w, hg] at hgq₀
          exact hii (CGate.var.inj hgq₀)
        · intro _
          show (if i' = i then 1 else 0) = 0
          rw [if_neg hii]
    | cst b =>
      simp only [extractG]
      rw [hg]
      constructor
      · intro hr
        exfalso
        rcases reach_cases hr with he | ⟨t, ht, -, -⟩
        · rw [he, hg] at hgq₀
          simp at hgq₀
        · rw [hg] at ht
          exact absurd ht (by simp [gateReads])
      · intro _
        rfl
    | un op j =>
      by_cases hj : j < w
      · have hE : extractG c (fuel + 1) w = GTree.un op (extractG c fuel j) := by
          simp only [extractG]
          rw [hg]
          show (if j < w then GTree.un op (extractG c fuel j)
            else GTree.cst (op false)) = GTree.un op (extractG c fuel j)
          rw [if_pos hj]
        rw [hE]
        have hjm : j ∈ gateReads (c.getD w (.cst false)) := by
          rw [hg]
          exact Finset.mem_singleton_self j
        have hjc : j ∈ cone c := mem_cone.mpr ⟨by omega, InCone.step hwic hjm hj⟩
        obtain ⟨ihp, ihn⟩ := ih j (by omega) hjc
        constructor
        · intro hr
          rcases reach_cases hr with he | ⟨t, ht, htw, hres⟩
          · exfalso
            rw [he, hg] at hgq₀
            simp at hgq₀
          · rw [hg] at ht
            have htj : t = j := Finset.mem_singleton.mp ht
            subst htj
            show (extractG c fuel t).cnt i = 1
            exact ihp hres
        · intro hnr
          have hnj : ¬ Reach c j q₀ := fun hres =>
            hnr (reach_trans (Reach.step (Reach.refl w) hjm hj) hres)
          show (extractG c fuel j).cnt i = 0
          exact ihn hnj
      · have hE : extractG c (fuel + 1) w = GTree.cst (op false) := by
          simp only [extractG]
          rw [hg]
          show (if j < w then GTree.un op (extractG c fuel j)
            else GTree.cst (op false)) = GTree.cst (op false)
          rw [if_neg hj]
        rw [hE]
        constructor
        · intro hr
          exfalso
          rcases reach_cases hr with he | ⟨t, ht, htw, -⟩
          · rw [he, hg] at hgq₀
            simp at hgq₀
          · rw [hg] at ht
            have := Finset.mem_singleton.mp ht
            omega
        · intro _
          rfl
    | bin op j k =>
      have hjm : j ∈ gateReads (c.getD w (.cst false)) := by
        rw [hg]
        exact Finset.mem_insert_self j {k}
      have hkm : k ∈ gateReads (c.getD w (.cst false)) := by
        rw [hg]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self k)
      by_cases hj : j < w
      · have hjc : j ∈ cone c := mem_cone.mpr ⟨by omega, InCone.step hwic hjm hj⟩
        obtain ⟨ihjp, ihjn⟩ := ih j (by omega) hjc
        by_cases hk : k < w
        · have hkc : k ∈ cone c := mem_cone.mpr ⟨by omega, InCone.step hwic hkm hk⟩
          obtain ⟨ihkp, ihkn⟩ := ih k (by omega) hkc
          have hE : extractG c (fuel + 1) w
              = GTree.node op (extractG c fuel j) (extractG c fuel k) := by
            simp only [extractG]
            rw [hg]
            show (if j < w then
              if k < w then GTree.node op (extractG c fuel j) (extractG c fuel k)
              else GTree.un (fun v => op v false) (extractG c fuel j)
            else
              if k < w then GTree.un (fun v => op false v) (extractG c fuel k)
              else GTree.cst (op false false)) = GTree.node op (extractG c fuel j) (extractG c fuel k)
            rw [if_pos hj, if_pos hk]
          rw [hE]
          by_cases hjk : j = k
          · subst hjk
            have hjR : j ∈ reconvR c := by
              have hval : slotCnt (c.getD w (.cst false)) j = 2 := by
                rw [hg]
                show (if j = j then 1 else 0) + (if j = j then 1 else 0) = 2
                rw [if_pos rfl]
              have hle : slotCnt (c.getD w (.cst false)) j ≤ slotReads c j := by
                rw [slotReads]
                exact Finset.single_le_sum
                  (f := fun w' => slotCnt (c.getD w' (.cst false)) j)
                  (fun w' _ => Nat.zero_le _) hwc
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_erase.mpr ⟨by omega, hjc⟩, by omega⟩
            have hnj : ¬ Reach c j q₀ := hRq₀ j hjR
            constructor
            · intro hr
              exfalso
              rcases reach_cases hr with he | ⟨t, ht, htw, hres⟩
              · rw [he, hg] at hgq₀
                simp at hgq₀
              · rw [hg] at ht
                have ht' : t = j := by
                  rcases Finset.mem_insert.mp ht with h | h
                  · exact h
                  · exact Finset.mem_singleton.mp h
                subst ht'
                exact hnj hres
            · intro _
              show (extractG c fuel j).cnt i + (extractG c fuel j).cnt i = 0
              rw [ihjn hnj]
          · constructor
            · intro hr
              rcases reach_cases hr with he | ⟨t, ht, htw, hres⟩
              · exfalso
                rw [he, hg] at hgq₀
                simp at hgq₀
              · rw [hg] at ht
                have ht' : t = j ∨ t = k := by
                  rcases Finset.mem_insert.mp ht with h | h
                  · exact Or.inl h
                  · exact Or.inr (Finset.mem_singleton.mp h)
                show (extractG c fuel j).cnt i + (extractG c fuel k).cnt i = 1
                rcases ht' with heq | heq
                · subst heq
                  have hnk : ¬ Reach c k q₀ := fun hrk =>
                    clean_reach_not_both c hs hwc hjm hj hkm hk hjk hRq₀
                      c.length q₀ (by omega) hres hrk (Reach.refl q₀)
                  rw [ihjp hres, ihkn hnk]
                · subst heq
                  have hnj : ¬ Reach c j q₀ := fun hrj =>
                    clean_reach_not_both c hs hwc hjm hj hkm hk hjk hRq₀
                      c.length q₀ (by omega) hrj hres (Reach.refl q₀)
                  rw [ihjn hnj, ihkp hres]
            · intro hnr
              have hnj : ¬ Reach c j q₀ := fun hres =>
                hnr (reach_trans (Reach.step (Reach.refl w) hjm hj) hres)
              have hnk : ¬ Reach c k q₀ := fun hres =>
                hnr (reach_trans (Reach.step (Reach.refl w) hkm hk) hres)
              show (extractG c fuel j).cnt i + (extractG c fuel k).cnt i = 0
              rw [ihjn hnj, ihkn hnk]
        · have hE : extractG c (fuel + 1) w
              = GTree.un (fun v => op v false) (extractG c fuel j) := by
            simp only [extractG]
            rw [hg]
            show (if j < w then
              if k < w then GTree.node op (extractG c fuel j) (extractG c fuel k)
              else GTree.un (fun v => op v false) (extractG c fuel j)
            else
              if k < w then GTree.un (fun v => op false v) (extractG c fuel k)
              else GTree.cst (op false false)) = GTree.un (fun v => op v false) (extractG c fuel j)
            rw [if_pos hj, if_neg hk]
          rw [hE]
          constructor
          · intro hr
            rcases reach_cases hr with he | ⟨t, ht, htw, hres⟩
            · exfalso
              rw [he, hg] at hgq₀
              simp at hgq₀
            · rw [hg] at ht
              have ht' : t = j ∨ t = k := by
                rcases Finset.mem_insert.mp ht with h | h
                · exact Or.inl h
                · exact Or.inr (Finset.mem_singleton.mp h)
              rcases ht' with heq | heq
              · subst heq
                show (extractG c fuel t).cnt i = 1
                exact ihjp hres
              · subst heq
                omega
          · intro hnr
            have hnj : ¬ Reach c j q₀ := fun hres =>
              hnr (reach_trans (Reach.step (Reach.refl w) hjm hj) hres)
            show (extractG c fuel j).cnt i = 0
            exact ihjn hnj
      · by_cases hk : k < w
        · have hkc : k ∈ cone c := mem_cone.mpr ⟨by omega, InCone.step hwic hkm hk⟩
          obtain ⟨ihkp, ihkn⟩ := ih k (by omega) hkc
          have hE : extractG c (fuel + 1) w
              = GTree.un (fun v => op false v) (extractG c fuel k) := by
            simp only [extractG]
            rw [hg]
            show (if j < w then
              if k < w then GTree.node op (extractG c fuel j) (extractG c fuel k)
              else GTree.un (fun v => op v false) (extractG c fuel j)
            else
              if k < w then GTree.un (fun v => op false v) (extractG c fuel k)
              else GTree.cst (op false false)) = GTree.un (fun v => op false v) (extractG c fuel k)
            rw [if_neg hj, if_pos hk]
          rw [hE]
          constructor
          · intro hr
            rcases reach_cases hr with he | ⟨t, ht, htw, hres⟩
            · exfalso
              rw [he, hg] at hgq₀
              simp at hgq₀
            · rw [hg] at ht
              have ht' : t = j ∨ t = k := by
                rcases Finset.mem_insert.mp ht with h | h
                · exact Or.inl h
                · exact Or.inr (Finset.mem_singleton.mp h)
              rcases ht' with heq | heq
              · subst heq
                omega
              · subst heq
                show (extractG c fuel t).cnt i = 1
                exact ihkp hres
          · intro hnr
            have hnk : ¬ Reach c k q₀ := fun hres =>
              hnr (reach_trans (Reach.step (Reach.refl w) hkm hk) hres)
            show (extractG c fuel k).cnt i = 0
            exact ihkn hnk
        · have hE : extractG c (fuel + 1) w = GTree.cst (op false false) := by
            simp only [extractG]
            rw [hg]
            show (if j < w then
              if k < w then GTree.node op (extractG c fuel j) (extractG c fuel k)
              else GTree.un (fun v => op v false) (extractG c fuel j)
            else
              if k < w then GTree.un (fun v => op false v) (extractG c fuel k)
              else GTree.cst (op false false)) = GTree.cst (op false false)
            rw [if_neg hj, if_neg hk]
          rw [hE]
          constructor
          · intro hr
            exfalso
            rcases reach_cases hr with he | ⟨t, ht, htw, -⟩
            · rw [he, hg] at hgq₀
              simp at hgq₀
            · rw [hg] at ht
              have ht' : t = j ∨ t = k := by
                rcases Finset.mem_insert.mp ht with h | h
                · exact Or.inl h
                · exact Or.inr (Finset.mem_singleton.mp h)
              rcases ht' with heq | heq <;> omega
          · intro _
            rfl

/-- Blindness from the mediated hypothesis (the `R`-membership case is handled
by the swap itself). -/
theorem multiSwap_blind' {n : ℕ} (c : List (CGate n)) (hs : 0 < c.length)
    (w : ℕ → Bool) (i : Fin n)
    (hnc : ∀ q, CleanIn c (reconvR c) q → q ∉ reconvR c →
      c.getD q (.cst false) ≠ CGate.var i)
    (x : Fin n → Bool) (b : Bool) :
    output (multiSwap c w (reconvR c).toList) (Function.update x i b)
      = output (multiSwap c w (reconvR c).toList) x := by
  have hl : ∀ s ∈ (reconvR c).toList, s < c.length := fun s hsm =>
    (mem_reconvR (Finset.mem_toList.mp hsm)).1
  have hlen : (multiSwap c w (reconvR c).toList).length = c.length :=
    multiSwap_length c w _ hl
  have hnv : ∀ w', InCone (multiSwap c w (reconvR c).toList) w' →
      (multiSwap c w (reconvR c).toList).getD w' (.cst false) ≠ CGate.var i := by
    intro w' hw' hg
    by_cases hwR : w' ∈ reconvR c
    · rw [multiSwap_getD_mem c w _ hl (Finset.nodup_toList _)
        (Finset.mem_toList.mpr hwR)] at hg
      simp at hg
    · rw [multiSwap_getD_notmem c w _ hl
        (fun hmem => hwR (Finset.mem_toList.mp hmem))] at hg
      exact hnc w' (multiSwap_cone_clean c hs w w' hw') hwR hg
  rw [output_eq_wire, output_eq_wire]
  exact cone_wire_agree (multiSwap c w (reconvR c).toList) i x b (by omega) hnv
    _ InCone.root

/-- **THE MEDIATED DICHOTOMY (proved)**: every gadget has a variable that is
mediated (every clean path misses its gates outside `R`) or duplicated. -/
theorem gadget_dichotomy (m : ℕ) (c : List (CGate (3 * m)))
    (hcomp : computes c (AEm m)) (hs : 0 < c.length) (g : ℕ) (hg : g < m)
    (ha : 3 * g < 3 * m) (hb : 3 * g + 1 < 3 * m) (hc : 3 * g + 2 < 3 * m) :
    (∃ i : Fin (3 * m),
      (i = ⟨3 * g, ha⟩ ∨ i = ⟨3 * g + 1, hb⟩ ∨ i = ⟨3 * g + 2, hc⟩) ∧
      ∀ q, CleanIn c (reconvR c) q → q ∉ reconvR c →
        c.getD q (.cst false) ≠ CGate.var i)
    ∨ (∃ i : Fin (3 * m),
      (i = ⟨3 * g, ha⟩ ∨ i = ⟨3 * g + 1, hb⟩ ∨ i = ⟨3 * g + 2, hc⟩) ∧
      ∃ q₁ q₂ : ℕ, q₁ ≠ q₂ ∧ q₁ ∈ cone c ∧ q₂ ∈ cone c ∧
        c.getD q₁ (.cst false) = CGate.var i ∧
        c.getD q₂ (.cst false) = CGate.var i) := by
  classical
  -- the per-variable dichotomy
  have per_var : ∀ i : Fin (3 * m),
      (extractG c c.length (c.length - 1)).cnt i ≠ 1 →
      (∀ q, CleanIn c (reconvR c) q → q ∉ reconvR c →
        c.getD q (.cst false) ≠ CGate.var i)
      ∨ (∃ q₁ q₂ : ℕ, q₁ ≠ q₂ ∧ q₁ ∈ cone c ∧ q₂ ∈ cone c ∧
        c.getD q₁ (.cst false) = CGate.var i ∧
        c.getD q₂ (.cst false) = CGate.var i) := by
    intro i hcnt
    obtain ⟨q₀, hq₀c, hgq₀⟩ := var_position_exists (AEm m) c hcomp hs i
      (by rw [depSet_AEm]; exact Finset.mem_univ _)
    by_cases hdup : ∃ q₁, q₁ ∈ cone c ∧ q₁ ≠ q₀ ∧
        c.getD q₁ (.cst false) = CGate.var i
    · obtain ⟨q₁, hq₁c, hq₁ne, hgq₁⟩ := hdup
      exact Or.inr ⟨q₁, q₀, hq₁ne, hq₁c, hq₀c, hgq₁, hgq₀⟩
    · push_neg at hdup
      left
      intro q hqcl hqR hgq
      have hqcone : q ∈ cone c :=
        mem_cone.mpr ⟨inCone_lt hs (cleanIn_inCone hqcl), cleanIn_inCone hqcl⟩
      have huniq : ∀ q' ∈ cone c, c.getD q' (.cst false) = CGate.var i → q' = q₀ := by
        intro q' hq' hg'
        by_contra hne
        exact hdup q' hq' hne hg'
      have hqq₀ : q = q₀ := huniq q hqcone hgq
      rw [hqq₀] at hqcl hqR
      have hRq₀ := cleanIn_no_reconv_reach c hs hqcl hqR
      have hroot : c.length - 1 ∈ cone c := mem_cone.mpr ⟨by omega, InCone.root⟩
      have hspec := extractG_cnt_spec c hs i q₀ hq₀c hgq₀ huniq hRq₀
        c.length (c.length - 1) (by omega) hroot
      refine hcnt (hspec.1 ?_)
      exact inCone_reach_root (mem_cone.mp hq₀c).2
  have hS1 : ¬ ((extractG c c.length (c.length - 1)).cnt ⟨3 * g, ha⟩ = 1
      ∧ (extractG c c.length (c.length - 1)).cnt ⟨3 * g + 1, hb⟩ = 1
      ∧ (extractG c c.length (c.length - 1)).cnt ⟨3 * g + 2, hc⟩ = 1) :=
    AEm_gadget_cnt_ne m c hcomp hs g hg ha hb hc
  by_cases h0 : (extractG c c.length (c.length - 1)).cnt ⟨3 * g, ha⟩ = 1
  · by_cases h1 : (extractG c c.length (c.length - 1)).cnt ⟨3 * g + 1, hb⟩ = 1
    · by_cases h2 : (extractG c c.length (c.length - 1)).cnt ⟨3 * g + 2, hc⟩ = 1
      · exact absurd ⟨h0, h1, h2⟩ hS1
      · rcases per_var ⟨3 * g + 2, hc⟩ h2 with hM | hD
        · exact Or.inl ⟨_, Or.inr (Or.inr rfl), hM⟩
        · exact Or.inr ⟨_, Or.inr (Or.inr rfl), hD⟩
    · rcases per_var ⟨3 * g + 1, hb⟩ h1 with hM | hD
      · exact Or.inl ⟨_, Or.inr (Or.inl rfl), hM⟩
      · exact Or.inr ⟨_, Or.inr (Or.inl rfl), hD⟩
  · rcases per_var ⟨3 * g, ha⟩ h0 with hM | hD
    · exact Or.inl ⟨_, Or.inl rfl, hM⟩
    · exact Or.inr ⟨_, Or.inl rfl, hD⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.extractG_cnt_spec
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.gadget_dichotomy
