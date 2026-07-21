import PallLean.Paper93.DeepMath.PathB.ComputationalDepthIntraKill

/-!
# Brick G1 of the ∀m finish: the first-branch chain

Below the first reconvergence, reader chains are deterministic.  This brick
makes the chain a formal object and proves the facts the collapse design
consumes:

* `Chain` — the reader climb through non-reconvergence wires;
* **`chain_unique` (proved)** — the climb is deterministic: two chains from the
  same wire into the reconvergence set end at the same wire (the first branch);
* **`chain_sole` / `chain_sole_var` (proved)** — a wire strictly below its
  first branch has no `{first branch}`-clean path: the chain is its only route;
* **`reach_chain_dichotomy` (proved)** — anything in the cone reaching a
  chained wire is on the chain or reaches its top;
* **`firstBranch_exists_of_cnt` (proved)** — a single-gated variable whose
  unwinding count is not 1 has a first branch (a clean climb to the root would
  force count 1 via `extractG_cnt_spec`).

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-- The deterministic reader climb: intermediate wires avoid the reconvergence
set, each step moves to a cone reader. -/
inductive Chain (c : List (CGate n)) : ℕ → ℕ → Prop
  | refl (q : ℕ) : Chain c q q
  | step {q w w' : ℕ} : Chain c q w → w ∉ reconvR c → w' ∈ cone c →
      w ∈ gateReads (c.getD w' (.cst false)) → w < w' → Chain c q w'

theorem chain_le {c : List (CGate n)} {q w : ℕ} (h : Chain c q w) : q ≤ w := by
  induction h with
  | refl => exact le_refl _
  | step hc hR hcone hr hlt ih => omega

theorem chain_reach {c : List (CGate n)} {q w : ℕ} (h : Chain c q w) :
    Reach c w q := by
  induction h with
  | refl => exact Reach.refl _
  | step hc hR hcone hr hlt ih =>
    exact reach_trans (Reach.step (Reach.refl _) hr hlt) ih

theorem chain_trans {c : List (CGate n)} {q w w'' : ℕ} (h1 : Chain c q w)
    (h2 : Chain c w w'') : Chain c q w'' := by
  induction h2 with
  | refl => exact h1
  | step hc hR hcone hr hlt ih => exact Chain.step ih hR hcone hr hlt

theorem chain_cone {c : List (CGate n)} {q w : ℕ} (h : Chain c q w)
    (hq : q ∈ cone c) : w ∈ cone c := by
  induction h with
  | refl => exact hq
  | step hc hR hcone hr hlt ih => exact hcone

/-- First-step inversion of a chain. -/
theorem chain_cases {c : List (CGate n)} {q u : ℕ} (h : Chain c q u) :
    u = q ∨ ∃ w₁, (q ∉ reconvR c ∧ w₁ ∈ cone c
      ∧ q ∈ gateReads (c.getD w₁ (.cst false)) ∧ q < w₁) ∧ Chain c w₁ u := by
  induction h with
  | refl => exact Or.inl rfl
  | step hc hR hcone hr hlt ih =>
    rcases ih with he | ⟨w₁, hfirst, htail⟩
    · subst he
      exact Or.inr ⟨_, ⟨hR, hcone, hr, hlt⟩, Chain.refl _⟩
    · exact Or.inr ⟨w₁, hfirst, Chain.step htail hR hcone hr hlt⟩

/-- A wire strictly below a cone wire is not the root. -/
theorem chain_start_ne_root {c : List (CGate n)} {q w₁ : ℕ}
    (hw₁ : w₁ ∈ cone c) (hlt : q < w₁) : q ≠ c.length - 1 := by
  have := (mem_cone.mp hw₁).1
  omega

/-- **The climb is deterministic (proved).** -/
theorem chain_unique {n : ℕ} (c : List (CGate n)) (hs : 0 < c.length) :
    ∀ (mm q u₁ u₂ : ℕ), c.length - q ≤ mm →
      q ∈ cone c → Chain c q u₁ → u₁ ∈ reconvR c →
      Chain c q u₂ → u₂ ∈ reconvR c → u₁ = u₂ := by
  intro mm
  induction mm with
  | zero =>
    intro q u₁ u₂ hq hqc h1 hR1 h2 hR2
    have := (mem_cone.mp hqc).1
    omega
  | succ mm ih =>
    intro q u₁ u₂ hq hqc h1 hR1 h2 hR2
    rcases chain_cases h1 with he1 | ⟨w₁, ⟨hqR, hw₁c, hr₁, hlt₁⟩, ht₁⟩
    · subst he1
      rcases chain_cases h2 with he2 | ⟨w₂, ⟨hqR', hw₂c, hr₂, hlt₂⟩, ht₂⟩
      · rw [he2]
      · exact absurd hR1 hqR'
    · rcases chain_cases h2 with he2 | ⟨w₂, ⟨hqR', hw₂c, hr₂, hlt₂⟩, ht₂⟩
      · rw [he2] at hR2
        exact absurd hR2 hqR
      · have hqe : q ∈ (cone c).erase (c.length - 1) :=
          Finset.mem_erase.mpr ⟨chain_start_ne_root hw₁c hlt₁, hqc⟩
        have hw : w₁ = w₂ :=
          readers_unique_of_not_reconv c hs hqe hqR hw₁c hw₂c hr₁ hr₂
        rw [← hw] at ht₂
        exact ih w₁ u₁ u₂ (by omega) hw₁c ht₁ hR1 ht₂ hR2

/-- **The chain is the only route (proved)**: a wire strictly below its first
branch has no `{first branch}`-clean path. -/
theorem chain_sole {n : ℕ} (c : List (CGate n)) (hs : 0 < c.length) :
    ∀ (mm q u : ℕ), c.length - q ≤ mm → q ∈ cone c →
      Chain c q u → u ∈ reconvR c → q ≠ u →
      CleanIn c {u} q → False := by
  intro mm
  induction mm with
  | zero =>
    intro q u hq hqc h1 hR hne hcl
    have := (mem_cone.mp hqc).1
    omega
  | succ mm ih =>
    intro q u hq hqc h1 hR hne hcl
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
        exact ih w₁ u (by omega) hw₁c ht₁ hR hw₁u hclw

/-- The soleness in kill-consumable form: for a single-gated variable, every
`{first branch}`-clean path misses its gate off the first branch. -/
theorem chain_sole_var {n : ℕ} (c : List (CGate n)) (hs : 0 < c.length)
    {q u : ℕ} (hqc : q ∈ cone c) (hch : Chain c q u) (hR : u ∈ reconvR c)
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
  · exact chain_sole c hs c.length q' u (by omega) hq'c hch hR hqu hcl

/-- **Reaching a chained wire (proved)**: anything in the cone reaching `q` is
on `q`'s chain or reaches its top. -/
theorem reach_chain_dichotomy {n : ℕ} (c : List (CGate n)) (hs : 0 < c.length) :
    ∀ (mm q u : ℕ), c.length - q ≤ mm → q ∈ cone c → Chain c q u →
      ∀ w, w ∈ cone c → Reach c w q → Chain c q w ∨ Reach c w u := by
  intro mm
  induction mm with
  | zero =>
    intro q u hq hqc h1 w hwc hr
    have := (mem_cone.mp hqc).1
    omega
  | succ mm ih =>
    intro q u hq hqc h1 w hwc hr
    by_cases hwq : w = q
    · rw [hwq]
      exact Or.inl (Chain.refl q)
    · rcases chain_cases h1 with he | ⟨w₁, ⟨hqR, hw₁c, hr₁, hlt₁⟩, ht₁⟩
      · subst he
        exact Or.inr hr
      · obtain ⟨p, hwp, hqp, hqlt⟩ := reach_last hr (fun he => hwq he.symm)
        have hpic : InCone c p := reach_inCone (mem_cone.mp hwc).2 hwp
        have hpc : p ∈ cone c := mem_cone.mpr ⟨inCone_lt hs hpic, hpic⟩
        have hqe : q ∈ (cone c).erase (c.length - 1) :=
          Finset.mem_erase.mpr ⟨chain_start_ne_root hw₁c hlt₁, hqc⟩
        have hw : p = w₁ :=
          readers_unique_of_not_reconv c hs hqe hqR hpc hw₁c hqp hr₁
        rw [hw] at hwp
        rcases ih w₁ u (by omega) hw₁c ht₁ w hwc hwp with hch | hru
        · exact Or.inl (chain_trans
            (Chain.step (Chain.refl q) hqR hw₁c hr₁ hlt₁) hch)
        · exact Or.inr hru

/-- A chainless wire is unreachable from every reconvergence. -/
theorem no_chain_no_reconv_reach {n : ℕ} (c : List (CGate n)) (hs : 0 < c.length) :
    ∀ (mm q : ℕ), c.length - q ≤ mm → q ∈ cone c →
      (¬ ∃ u, Chain c q u ∧ u ∈ reconvR c) →
      ∀ u' ∈ reconvR c, ¬ Reach c u' q := by
  intro mm
  induction mm with
  | zero =>
    intro q hq hqc hno u' hu'R hr
    have := (mem_cone.mp hqc).1
    omega
  | succ mm ih =>
    intro q hq hqc hno u' hu'R hr
    by_cases hqR : q ∈ reconvR c
    · exact hno ⟨q, Chain.refl q, hqR⟩
    · have hu'c : u' ∈ cone c :=
        (Finset.mem_erase.mp (Finset.mem_filter.mp hu'R).1).2
      by_cases hqroot : q = c.length - 1
      · have h1 := reach_le hr
        have h2 := (mem_cone.mp hu'c).1
        have hu'root : u' = c.length - 1 := by omega
        exact (Finset.mem_erase.mp (Finset.mem_filter.mp hu'R).1).1 hu'root
      · obtain ⟨hqlt, hqcone⟩ := mem_cone.mp hqc
        cases hqcone with
        | root => exact absurd rfl hqroot
        | step hw hjm hjw =>
          rename_i w₁
          have hw₁c : w₁ ∈ cone c := mem_cone.mpr ⟨inCone_lt hs hw, hw⟩
          have hu'q : u' ≠ q := fun he => hqR (he ▸ hu'R)
          obtain ⟨p, hu'p, hqp, hqlt'⟩ := reach_last hr (fun he => hu'q he.symm)
          have hpic : InCone c p := reach_inCone (mem_cone.mp hu'c).2 hu'p
          have hpc : p ∈ cone c := mem_cone.mpr ⟨inCone_lt hs hpic, hpic⟩
          have hqe : q ∈ (cone c).erase (c.length - 1) :=
            Finset.mem_erase.mpr ⟨hqroot, hqc⟩
          have hpw : p = w₁ :=
            readers_unique_of_not_reconv c hs hqe hqR hpc hw₁c hqp hjm
          rw [hpw] at hu'p
          have hno' : ¬ ∃ u, Chain c w₁ u ∧ u ∈ reconvR c := by
            rintro ⟨u, hch, huR⟩
            exact hno ⟨u, chain_trans
              (Chain.step (Chain.refl q) hqR hw₁c hjm hjw) hch, huR⟩
          exact ih w₁ (by omega) hw₁c hno' u' hu'R hu'p

/-- **First branches exist (proved)**: a single-gated variable whose unwinding
count is not 1 has a first branch. -/
theorem firstBranch_exists_of_cnt {n : ℕ} (c : List (CGate n)) (hs : 0 < c.length)
    (i : Fin n) (q₀ : ℕ) (hq₀c : q₀ ∈ cone c)
    (hgq₀ : c.getD q₀ (.cst false) = CGate.var i)
    (huniq : ∀ q ∈ cone c, c.getD q (.cst false) = CGate.var i → q = q₀)
    (hcnt : (extractG c c.length (c.length - 1)).cnt i ≠ 1) :
    ∃ u, Chain c q₀ u ∧ u ∈ reconvR c := by
  by_contra hno
  have hRq₀ := no_chain_no_reconv_reach c hs c.length q₀ (by omega) hq₀c hno
  have hroot : c.length - 1 ∈ cone c := mem_cone.mpr ⟨by omega, InCone.root⟩
  have hspec := extractG_cnt_spec c hs i q₀ hq₀c hgq₀ huniq hRq₀
    c.length (c.length - 1) (by omega) hroot
  exact hcnt (hspec.1 (inCone_reach_root (mem_cone.mp hq₀c).2))

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.chain_unique
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.chain_sole_var
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.reach_chain_dichotomy
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.firstBranch_exists_of_cnt
