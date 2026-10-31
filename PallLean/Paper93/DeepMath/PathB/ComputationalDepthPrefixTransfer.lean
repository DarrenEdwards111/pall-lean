import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFirstBranch

/-!
# Brick G2a of the ∀m finish: prefix transfer

Reach, cone and reconvergence relations transfer between a circuit and its
prefixes (the gates agree below the cut), and chains cannot pass through
reconvergences:

* `reach_take_of_reach` / `reach_inCone_take` / `reach_of_take` — reachability
  and cone membership transfer across `c.take (j+1)`;
* **`reconvR_take_subset` (proved)** — prefix reconvergences are circuit
  reconvergences (slot counts are monotone under the prefix);
* **`chain_extend_not_reconv` (proved)** — a chain member strictly below the
  chain's top is not a reconvergence;
* `chain_sole₀` / `chain_sole_var₀` — the soleness lemmas without the
  reconvergence-membership hypothesis (it was never used).

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

theorem reach_take_of_reach {n : ℕ} (c : List (CGate n)) {j : ℕ}
    (hj : j < c.length) {q : ℕ} (h : Reach c j q) :
    Reach (c.take (j + 1)) j q := by
  induction h with
  | refl => exact Reach.refl j
  | step hp hq hlt ih =>
    rename_i p q'
    have hple : p ≤ j := reach_le hp
    exact Reach.step ih (by rw [getD_take_eq_g (by omega)]; exact hq) hlt

theorem reach_inCone_take {n : ℕ} (c : List (CGate n)) {j : ℕ}
    (hj : j < c.length) {q : ℕ} (h : Reach c j q) :
    InCone (c.take (j + 1)) q := by
  induction h with
  | refl =>
    have hlt : (c.take (j + 1)).length - 1 = j := by
      rw [List.length_take]
      omega
    have hroot : InCone (c.take (j + 1)) ((c.take (j + 1)).length - 1) :=
      InCone.root
    rw [hlt] at hroot
    exact hroot
  | step hp hq hlt ih =>
    rename_i p q'
    have hple : p ≤ j := reach_le hp
    exact InCone.step ih (by rw [getD_take_eq_g (by omega)]; exact hq) hlt

theorem reach_of_take {n : ℕ} (c : List (CGate n)) {j : ℕ}
    (hj : j < c.length) {w q : ℕ} (hw : w ≤ j)
    (h : Reach (c.take (j + 1)) w q) : Reach c w q := by
  induction h with
  | refl => exact Reach.refl w
  | step hp hq hlt ih =>
    rename_i p q'
    have hple : p ≤ w := reach_le hp
    rw [getD_take_eq_g (show p < j + 1 by omega)] at hq
    exact Reach.step ih hq hlt

/-- **Prefix reconvergences are circuit reconvergences (proved).** -/
theorem reconvR_take_subset {n : ℕ} (c : List (CGate n)) {j : ℕ}
    (hjc : j ∈ cone c) (hjroot : j ≠ c.length - 1) {u' : ℕ}
    (h : u' ∈ reconvR (c.take (j + 1))) : u' ∈ reconvR c := by
  classical
  have hjlt : j < c.length := (mem_cone.mp hjc).1
  rw [reconvR, Finset.mem_filter, Finset.mem_erase] at h
  obtain ⟨⟨hu'ne, hu'c'⟩, hu'2⟩ := h
  have hu'lt : u' < j + 1 := by
    have := (mem_cone.mp hu'c').1
    rw [List.length_take] at this
    omega
  have hu'j : u' ≤ j := by
    have hroot' : (c.take (j + 1)).length - 1 = j := by
      rw [List.length_take]
      omega
    rw [hroot'] at hu'ne
    omega
  have hu'jlt : u' < j := by
    have hroot' : (c.take (j + 1)).length - 1 = j := by
      rw [List.length_take]
      omega
    rw [hroot'] at hu'ne
    omega
  have hu'reach : Reach c j u' :=
    inCone_take_reach_g hjlt u' (mem_cone.mp hu'c').2
  have hu'cone : u' ∈ cone c := by
    refine mem_cone.mpr ⟨by omega, reach_inCone (mem_cone.mp hjc).2 hu'reach⟩
  have hsub : cone (c.take (j + 1)) ⊆ cone c := by
    intro w hw
    have hwr : Reach c j w :=
      inCone_take_reach_g hjlt w (mem_cone.mp hw).2
    have hwlt : w < c.length := by
      have := reach_le hwr
      omega
    exact mem_cone.mpr ⟨hwlt, reach_inCone (mem_cone.mp hjc).2 hwr⟩
  have hcongr : ∑ w ∈ cone (c.take (j + 1)),
      slotCnt ((c.take (j + 1)).getD w (.cst false)) u'
      = ∑ w ∈ cone (c.take (j + 1)), slotCnt (c.getD w (.cst false)) u' := by
    refine Finset.sum_congr rfl (fun w hw => ?_)
    have hwlt : w < (c.take (j + 1)).length := (mem_cone.mp hw).1
    rw [List.length_take] at hwlt
    rw [getD_take_eq_g (by omega)]
  have hmono : slotReads (c.take (j + 1)) u' ≤ slotReads c u' := by
    rw [slotReads, slotReads, hcongr]
    exact Finset.sum_le_sum_of_subset hsub
  refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, hu'cone⟩, by omega⟩
  omega

/-- **A chain member strictly below the top is not a reconvergence (proved).** -/
theorem chain_extend_not_reconv {n : ℕ} (c : List (CGate n)) (hs : 0 < c.length) :
    ∀ (mm q u' j : ℕ), c.length - q ≤ mm → q ∈ cone c →
      Chain c q u' → Chain c q j → u' < j → u' ∉ reconvR c := by
  intro mm
  induction mm with
  | zero =>
    intro q u' j hq hqc h1 h2 hlt
    have := (mem_cone.mp hqc).1
    omega
  | succ mm ih =>
    intro q u' j hq hqc h1 h2 hlt
    have hqu' := chain_le h1
    by_cases hu'q : u' = q
    · subst hu'q
      rcases chain_cases h2 with he | ⟨w₁, ⟨hqR, hw₁c, hr₁, hlt₁⟩, ht₁⟩
      · exfalso
        omega
      · exact hqR
    · rcases chain_cases h1 with he | ⟨w₁, ⟨hqR, hw₁c, hr₁, hlt₁⟩, ht₁⟩
      · exact absurd he.symm (fun h => hu'q h.symm)
      · rcases chain_cases h2 with he2 | ⟨w₂, ⟨hqR', hw₂c, hr₂, hlt₂⟩, ht₂⟩
        · exfalso
          omega
        · have hqe : q ∈ (cone c).erase (c.length - 1) :=
            Finset.mem_erase.mpr ⟨chain_start_ne_root hw₁c hlt₁, hqc⟩
          have hw : w₁ = w₂ :=
            readers_unique_of_not_reconv c hs hqe hqR hw₁c hw₂c hr₁ hr₂
          rw [← hw] at ht₂
          exact ih w₁ u' j (by omega) hw₁c ht₁ ht₂ hlt

/-- Soleness without the reconvergence-membership hypothesis. -/
theorem chain_sole₀ {n : ℕ} (c : List (CGate n)) (hs : 0 < c.length) :
    ∀ (mm q u : ℕ), c.length - q ≤ mm → q ∈ cone c →
      Chain c q u → q ≠ u → CleanIn c {u} q → False := by
  intro mm
  induction mm with
  | zero =>
    intro q u hq hqc h1 hne hcl
    have := (mem_cone.mp hqc).1
    omega
  | succ mm ih =>
    intro q u hq hqc h1 hne hcl
    rcases chain_cases h1 with he | ⟨w₁, ⟨hqR, hw₁c, hr₁, hlt₁⟩, ht₁⟩
    · exact hne he.symm
    · cases hcl with
      | root =>
        exact chain_start_ne_root hw₁c hlt₁ rfl
      | step hclw hwR hqr hqlt' =>
        rename_i w'
        have hw'c : w' ∈ cone c :=
          mem_cone.mpr ⟨inCone_lt hs (cleanIn_inCone hclw), cleanIn_inCone hclw⟩
        have hqe : q ∈ (cone c).erase (c.length - 1) :=
          Finset.mem_erase.mpr ⟨chain_start_ne_root hw₁c hlt₁, hqc⟩
        have hw : w' = w₁ :=
          readers_unique_of_not_reconv c hs hqe hqR hw'c hw₁c hqr hr₁
        rw [hw] at hclw hwR
        have hw₁u : w₁ ≠ u := by
          intro he
          rw [he] at hwR
          exact hwR (Finset.mem_singleton_self u)
        exact ih w₁ u (by omega) hw₁c ht₁ hw₁u hclw

/-- The kill-consumable soleness at an arbitrary chain top. -/
theorem chain_sole_var₀ {n : ℕ} (c : List (CGate n)) (hs : 0 < c.length)
    {q u : ℕ} (hqc : q ∈ cone c) (hch : Chain c q u)
    {i : Fin n} (huniq : ∀ q' ∈ cone c, c.getD q' (.cst false) = CGate.var i → q' = q) :
    ∀ q', CleanIn c {u} q' → q' ≠ u →
      c.getD q' (.cst false) ≠ CGate.var i := by
  intro q' hcl hne hg
  have hq'c : q' ∈ cone c :=
    mem_cone.mpr ⟨inCone_lt hs (cleanIn_inCone hcl), cleanIn_inCone hcl⟩
  have hq'q : q' = q := huniq q' hq'c hg
  subst hq'q
  by_cases hqu : q' = u
  · exact hne hqu
  · exact chain_sole₀ c hs c.length q' u (by omega) hq'c hch hqu hcl

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.reconvR_take_subset
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.chain_extend_not_reconv
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.chain_sole_var₀
