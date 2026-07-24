import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATParKillsB3b
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShapeTreeExtract

/-!
# Parallel profile restriction: no coordinate is below both wires

Multi-wire brick 9 — the analytic core of the parallel case.

At two reconvergence wires `reconvR c = {u, v}` that are **parallel**
(`¬ Reach c u v` and `¬ Reach c v u`), no cone gate is reachable from both
`u` and `v`.

**Proof (maximality, no path induction).**  Suppose the below-both set
`S = { q ∈ cone | Reach c u q ∧ Reach c v q }` were nonempty and let
`q★ = max S`.  Neither `q★ = u` (that would give `Reach c v u`) nor
`q★ = v` (that would give `Reach c u v`), so the last downward step to `q★`
exists on each side: `q★` is read by a gate `p` on the `u`-path
(`Reach c u p`, `q★ < p`) and by a gate `p'` on the `v`-path.

* If `p = p'` then `p` is itself below both wires and `p > q★`,
  contradicting maximality of `q★`.
* If `p ≠ p'` then `q★` is read by two distinct cone gates, so
  `2 ≤ slotReads c q★`; being a non-root cone wire this puts
  `q★ ∈ reconvR c = {u, v}`, contradicting `q★ ≠ u, v`.

This is the profile-restriction lemma the parallel-case pigeonhole dispatch
needs: every gadget sign is below *exactly one* wire (or neither), so the
avoiding hypotheses of the `killB1v` / `killB2v` / `killB3v` kills are always
met.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-- **Last-step inversion of `Reach` (proved)**: a nontrivial downward path
ends in a final read step. -/
theorem reach_last_step {n : ℕ} {c : List (CGate n)} {w q : ℕ} (h : Reach c w q) :
    q = w ∨ ∃ p, Reach c w p ∧ q ∈ gateReads (c.getD p (.cst false)) ∧ q < p := by
  cases h with
  | refl => exact Or.inl rfl
  | step hp hq hlt => exact Or.inr ⟨_, hp, hq, hlt⟩

/-- **Two distinct readers force slot-multiplicity two (proved).** -/
theorem slotReads_ge_two_of_two_readers {n : ℕ} (c : List (CGate n)) {q p p' : ℕ}
    (hp : p ∈ cone c) (hp' : p' ∈ cone c) (hpp' : p ≠ p')
    (hrp : q ∈ gateReads (c.getD p (.cst false)))
    (hrp' : q ∈ gateReads (c.getD p' (.cst false))) :
    2 ≤ slotReads c q := by
  have hsub : ({p, p'} : Finset ℕ) ⊆ cone c := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · exact hx ▸ hp
    · exact (Finset.mem_singleton.mp hx) ▸ hp'
  have hcp : 1 ≤ slotCnt (c.getD p (.cst false)) q := slotCnt_pos_of_reads _ _ hrp
  have hcp' : 1 ≤ slotCnt (c.getD p' (.cst false)) q := slotCnt_pos_of_reads _ _ hrp'
  calc 2 = 1 + 1 := rfl
    _ ≤ slotCnt (c.getD p (.cst false)) q + slotCnt (c.getD p' (.cst false)) q :=
        Nat.add_le_add hcp hcp'
    _ = ∑ x ∈ ({p, p'} : Finset ℕ), slotCnt (c.getD x (.cst false)) q :=
        (Finset.sum_pair (f := fun x => slotCnt (c.getD x (.cst false)) q) hpp').symm
    _ ≤ ∑ x ∈ cone c, slotCnt (c.getD x (.cst false)) q :=
        Finset.sum_le_sum_of_subset hsub
    _ = slotReads c q := rfl

/-- **THE PROFILE-RESTRICTION LEMMA (proved)**: at two parallel reconvergence
wires, no cone gate is below both. -/
theorem not_below_both {n : ℕ} (c : List (CGate n)) (hs : 0 < c.length)
    {u v : ℕ} (hR : reconvR c = {u, v}) (huv : ¬ Reach c u v) (hvu : ¬ Reach c v u) :
    ∀ q ∈ cone c, ¬ (Reach c u q ∧ Reach c v q) := by
  -- membership facts for `u` and `v`
  have humem : u ∈ reconvR c := by rw [hR]; exact Finset.mem_insert_self u {v}
  have hvmem : v ∈ reconvR c := by
    rw [hR]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
  have huc : u ∈ cone c := (Finset.mem_erase.mp (Finset.mem_filter.mp humem).1).2
  have hvc : v ∈ cone c := (Finset.mem_erase.mp (Finset.mem_filter.mp hvmem).1).2
  have huIn : InCone c u := (mem_cone.mp huc).2
  have hvIn : InCone c v := (mem_cone.mp hvc).2
  by_contra hcon
  push_neg at hcon
  obtain ⟨q0, hq0c, hq0u, hq0v⟩ := hcon
  -- the below-both set and its maximum
  classical
  set S : Finset ℕ := (cone c).filter (fun q => Reach c u q ∧ Reach c v q) with hSdef
  have hq0S : q0 ∈ S := Finset.mem_filter.mpr ⟨hq0c, hq0u, hq0v⟩
  have hSne : S.Nonempty := ⟨q0, hq0S⟩
  set qs : ℕ := S.max' hSne with hqsdef
  have hqsS : qs ∈ S := S.max'_mem hSne
  obtain ⟨hqsc, hqsu, hqsv⟩ := Finset.mem_filter.mp hqsS
  -- `qs ≠ u, v` from parallelism
  have hne_u : qs ≠ u := by
    rintro h; exact hvu (h ▸ hqsv)
  have hne_v : qs ≠ v := by
    rintro h; exact huv (h ▸ hqsu)
  -- last steps on both sides
  rcases reach_last_step hqsu with hEqu | ⟨p, hup, hrp, hltp⟩
  · exact hne_u hEqu
  rcases reach_last_step hqsv with hEqv | ⟨p', hvp', hrp', hltp'⟩
  · exact hne_v hEqv
  have hpc : p ∈ cone c := reach_inCone huIn hup |> fun hin =>
    mem_cone.mpr ⟨lt_of_le_of_lt (reach_le hup) (mem_cone.mp huc).1, hin⟩
  have hp'c : p' ∈ cone c := reach_inCone hvIn hvp' |> fun hin =>
    mem_cone.mpr ⟨lt_of_le_of_lt (reach_le hvp') (mem_cone.mp hvc).1, hin⟩
  by_cases hpp' : p = p'
  · -- shared predecessor `p` is below both and larger than the max
    subst hpp'
    have hpS : p ∈ S := Finset.mem_filter.mpr ⟨hpc, hup, hvp'⟩
    have hple : p ≤ qs := Finset.le_max' S p hpS
    omega
  · -- distinct readers force `qs ∈ reconvR = {u, v}`
    have h2 : 2 ≤ slotReads c qs :=
      slotReads_ge_two_of_two_readers c hpc hp'c hpp' hrp hrp'
    have hqsne_root : qs ≠ c.length - 1 := by
      have : p ≤ c.length - 1 := by
        have := (mem_cone.mp hpc).1; omega
      omega
    have hqsR : qs ∈ reconvR c :=
      Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hqsne_root, hqsc⟩, h2⟩
    rw [hR] at hqsR
    rcases Finset.mem_insert.mp hqsR with h | h
    · exact hne_u h
    · exact hne_v (Finset.mem_singleton.mp h)

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
