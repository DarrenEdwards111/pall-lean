import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATCutLemma

/-!
# The ⊆-generalized cut lemma (nested-case foundation)

Multi-wire brick 11a — the reusable foundation for the nested two-wire case.

Identical to `read_structure` / `cut_agree` but with `reconvR c ⊆ {u}` in place
of `reconvR c = {u}`.  When the outer reconvergence wire `u` reaches the inner
wire `v` (`Reach c u v`), the `u`-prefix `c.take (u + 1)` has
`reconvR (c.take (u+1)) ⊆ {v}` (possibly empty), so the mediator arguments
apply through the weaker subset hypothesis — exactly the "inner cut" the
nested `c`-profile kills use.

* **`read_structure_subset` / `cut_agree_subset` (proved)** — the only change
  from the `= {u}` versions is discharging `j ∈ reconvR c` via the subset map
  rather than singleton rewriting.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-- **Read structure through a subset reconvergence set (proved)**. -/
theorem read_structure_subset {n : ℕ} (c : List (CGate n)) (u : ℕ) (hs : 0 < c.length)
    (hR : reconvR c ⊆ {u}) (hu_cone : InCone c u)
    {w j : ℕ} (hw : w ∈ cone c) (hnb : ¬ Reach c u w)
    (hj : j ∈ gateReads (c.getD w (.cst false))) (hjw : j < w) :
    j = u ∨ ¬ Reach c u j := by
  by_cases hju : j = u
  · exact Or.inl hju
  refine Or.inr (fun hreach => ?_)
  obtain ⟨p, hp, hjp, hjlt⟩ :
      ∃ p, Reach c u p ∧ j ∈ gateReads (c.getD p (.cst false)) ∧ j < p := by
    cases hreach with
    | refl => exact absurd rfl hju
    | step hp hq hlt => exact ⟨_, hp, hq, hlt⟩
  by_cases hpw : p = w
  · rw [hpw] at hp
    exact hnb hp
  · have hpic : InCone c p := reach_inCone hu_cone hp
    have hpc : p ∈ cone c := mem_cone.mpr ⟨inCone_lt hs hpic, hpic⟩
    have hwlt : w < c.length := (mem_cone.mp hw).1
    have hjc : j ∈ cone c :=
      mem_cone.mpr ⟨by omega, InCone.step (mem_cone.mp hw).2 hj hjw⟩
    have hjroot : j ≠ c.length - 1 := by omega
    have hmem := two_readers_mem_reconv c hw hpc (fun he => hpw he.symm)
      hj hjp hjc hjroot
    exact hju (Finset.mem_singleton.mp (hR hmem))

/-- **The ⊆-generalized cut lemma (proved)**. -/
theorem cut_agree_subset {n : ℕ} (c : List (CGate n)) (u : ℕ) (hs : 0 < c.length)
    (hR : reconvR c ⊆ {u}) (hu_cone : InCone c u)
    (x x' : Fin n → Bool) (hu : wire c x u = wire c x' u)
    (hagree : ∀ i : Fin n,
      (∃ q, q ∈ cone c ∧ c.getD q (.cst false) = CGate.var i ∧ ¬ Reach c u q) →
      x i = x' i) :
    ∀ w, w ∈ cone c → ¬ Reach c u w → wire c x w = wire c x' w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwc hnb
    have hwlt : w < c.length := (mem_cone.mp hwc).1
    rw [wire_eq c x hwlt, wire_eq c x' hwlt]
    have hread : ∀ m : ℕ, m ∈ gateReads (c.getD w (.cst false)) → m < w →
        wire c x m = wire c x' m := by
      intro m hmr hmw
      have hmc : m ∈ cone c :=
        mem_cone.mpr ⟨by omega, InCone.step (mem_cone.mp hwc).2 hmr hmw⟩
      rcases read_structure_subset c u hs hR hu_cone hwc hnb hmr hmw with hmu | hnbm
      · rw [hmu]; exact hu
      · exact ih m hmw hmc hnbm
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
      exact hagree i ⟨w, hwc, hg, hnb⟩
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

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
