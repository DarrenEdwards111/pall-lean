import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBottleneckKill
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthIntraKill

/-!
# Brick G3 of the ∀m finish: the gadget profile classification

Every bit-served gadget owns a first branch with a fully free profile:

* **`partner_chain_of_below` (proved)** — the recursive-descent collapse: if a
  reconvergence `u` reaches a partner's unique var gate and `u` is minimal among
  the gadget's first branches, the partner's own climb must first-branch at `u`
  itself (`no_chain_no_reconv_reach` forces a chain to exist,
  `reach_chain_dichotomy` + minimality pin its top to `u`);
* **`gadget_FF_branch` (proved)** — a gadget with three unique cone var gates
  has a reconvergence `u` and a chosen coordinate chaining into `u` whose two
  partners have NO var gates below `u`: the minimal first branch works, because
  a partner below it would chain into it too, and then the triple profile dies
  by `chain_bottleneck_kill` while the pair profile dies by
  `intra_gadget_kill`.

This is the (F,F)-profile theorem: it feeds `one_side_pair_kill` in the G5
counting, making the first-branch map injective on bit-served gadgets.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-- **The descent collapse (proved)**: a minimal first branch reaching a wire
forces that wire to chain into it. -/
theorem partner_chain_of_below {n : ℕ} (c : List (CGate n)) (hs : 0 < c.length)
    {u q' : ℕ} (huR : u ∈ reconvR c) (hq'c : q' ∈ cone c) (hr : Reach c u q')
    (hmin : ∀ u'', Chain c q' u'' → u'' ∈ reconvR c → u ≤ u'') :
    Chain c q' u := by
  classical
  have hex : ∃ u'', Chain c q' u'' ∧ u'' ∈ reconvR c := by
    by_contra hno
    exact no_chain_no_reconv_reach c hs c.length q' (by omega) hq'c hno u huR hr
  obtain ⟨u'', hcu'', hu''R⟩ := hex
  have huc : u ∈ cone c :=
    (Finset.mem_erase.mp (Finset.mem_filter.mp huR).1).2
  rcases reach_chain_dichotomy c hs c.length q' u'' (by omega) hq'c hcu''
      u huc hr with hch | hru
  · exact hch
  · have h1 := reach_le hru
    have h2 := hmin u'' hcu'' hu''R
    have he : u = u'' := by omega
    rw [he]
    exact hcu''

/-- **THE (F,F)-PROFILE THEOREM (proved)**: a bit-served gadget has a first
branch whose chosen coordinate chains in and whose partners are free below. -/
theorem gadget_FF_branch (m : ℕ) (c : List (CGate (3 * m)))
    (hcomp : computes c (AEm m)) (hs : 0 < c.length)
    (g : ℕ) (hg : g < m)
    (ha : 3 * g < 3 * m) (hb : 3 * g + 1 < 3 * m) (hc2 : 3 * g + 2 < 3 * m)
    (q₀ q₁ q₂ : ℕ) (hq₀c : q₀ ∈ cone c) (hq₁c : q₁ ∈ cone c) (hq₂c : q₂ ∈ cone c)
    (hg₀ : c.getD q₀ (.cst false) = CGate.var ⟨3 * g, ha⟩)
    (hg₁ : c.getD q₁ (.cst false) = CGate.var ⟨3 * g + 1, hb⟩)
    (hg₂ : c.getD q₂ (.cst false) = CGate.var ⟨3 * g + 2, hc2⟩)
    (hu₀ : ∀ q' ∈ cone c, c.getD q' (.cst false) = CGate.var ⟨3 * g, ha⟩ → q' = q₀)
    (hu₁ : ∀ q' ∈ cone c, c.getD q' (.cst false) = CGate.var ⟨3 * g + 1, hb⟩ → q' = q₁)
    (hu₂ : ∀ q' ∈ cone c, c.getD q' (.cst false) = CGate.var ⟨3 * g + 2, hc2⟩ → q' = q₂) :
    ∃ u ∈ reconvR c, ∃ (p : ℕ) (hp : p < 3 * m) (qp : ℕ),
      p / 3 = g ∧ qp ∈ cone c ∧
      (∀ q' ∈ cone c, c.getD q' (.cst false) = CGate.var ⟨p, hp⟩ → q' = qp) ∧
      Chain c qp u ∧
      ∀ (t : ℕ) (ht : t < 3 * m), t / 3 = p / 3 → t ≠ p →
        ∀ q, Reach c u q → c.getD q (.cst false) ≠ CGate.var ⟨t, ht⟩ := by
  classical
  -- at least one coordinate has a first branch
  have hPex : ∃ u, u ∈ reconvR c
      ∧ (Chain c q₀ u ∨ Chain c q₁ u ∨ Chain c q₂ u) := by
    by_cases hcnt0 : (extractG c c.length (c.length - 1)).cnt ⟨3 * g, ha⟩ = 1
    · by_cases hcnt1 : (extractG c c.length (c.length - 1)).cnt ⟨3 * g + 1, hb⟩ = 1
      · by_cases hcnt2 : (extractG c c.length (c.length - 1)).cnt ⟨3 * g + 2, hc2⟩ = 1
        · exact absurd ⟨hcnt0, hcnt1, hcnt2⟩
            (AEm_gadget_cnt_ne m c hcomp hs g hg ha hb hc2)
        · obtain ⟨u, hch, hR⟩ :=
            firstBranch_exists_of_cnt c hs ⟨3 * g + 2, hc2⟩ q₂ hq₂c hg₂ hu₂ hcnt2
          exact ⟨u, hR, Or.inr (Or.inr hch)⟩
      · obtain ⟨u, hch, hR⟩ :=
          firstBranch_exists_of_cnt c hs ⟨3 * g + 1, hb⟩ q₁ hq₁c hg₁ hu₁ hcnt1
        exact ⟨u, hR, Or.inr (Or.inl hch)⟩
    · obtain ⟨u, hch, hR⟩ :=
        firstBranch_exists_of_cnt c hs ⟨3 * g, ha⟩ q₀ hq₀c hg₀ hu₀ hcnt0
      exact ⟨u, hR, Or.inl hch⟩
  -- the MINIMAL first branch of the gadget
  obtain ⟨u, huR, hPdisj, hmin⟩ : ∃ u, u ∈ reconvR c
      ∧ (Chain c q₀ u ∨ Chain c q₁ u ∨ Chain c q₂ u)
      ∧ ∀ u'', (u'' ∈ reconvR c
        ∧ (Chain c q₀ u'' ∨ Chain c q₁ u'' ∨ Chain c q₂ u'')) → u ≤ u'' :=
    ⟨Nat.find hPex, (Nat.find_spec hPex).1, (Nat.find_spec hPex).2,
      fun u'' h => Nat.find_min' hPex h⟩
  have hmin₀ : ∀ u'', Chain c q₀ u'' → u'' ∈ reconvR c → u ≤ u'' :=
    fun u'' hch hR => hmin u'' ⟨hR, Or.inl hch⟩
  have hmin₁ : ∀ u'', Chain c q₁ u'' → u'' ∈ reconvR c → u ≤ u'' :=
    fun u'' hch hR => hmin u'' ⟨hR, Or.inr (Or.inl hch)⟩
  have hmin₂ : ∀ u'', Chain c q₂ u'' → u'' ∈ reconvR c → u ≤ u'' :=
    fun u'' hch hR => hmin u'' ⟨hR, Or.inr (Or.inr hch)⟩
  have huc : u ∈ cone c :=
    (Finset.mem_erase.mp (Finset.mem_filter.mp huR).1).2
  have huroot : u ≠ c.length - 1 :=
    (Finset.mem_erase.mp (Finset.mem_filter.mp huR).1).1
  have hult : u < c.length := (mem_cone.mp huc).1
  -- a partner with a gate below u chains into u
  have hbelow₀ : (¬ ∀ q, Reach c u q →
      c.getD q (.cst false) ≠ CGate.var ⟨3 * g, ha⟩) → Chain c q₀ u := by
    intro hnb
    push_neg at hnb
    obtain ⟨qx, hqxr, hqxg⟩ := hnb
    have h1 := reach_le hqxr
    have hqxc : qx ∈ cone c :=
      mem_cone.mpr ⟨by omega, reach_inCone (mem_cone.mp huc).2 hqxr⟩
    have hqe : qx = q₀ := hu₀ qx hqxc hqxg
    rw [hqe] at hqxr
    exact partner_chain_of_below c hs huR hq₀c hqxr hmin₀
  have hbelow₁ : (¬ ∀ q, Reach c u q →
      c.getD q (.cst false) ≠ CGate.var ⟨3 * g + 1, hb⟩) → Chain c q₁ u := by
    intro hnb
    push_neg at hnb
    obtain ⟨qx, hqxr, hqxg⟩ := hnb
    have h1 := reach_le hqxr
    have hqxc : qx ∈ cone c :=
      mem_cone.mpr ⟨by omega, reach_inCone (mem_cone.mp huc).2 hqxr⟩
    have hqe : qx = q₁ := hu₁ qx hqxc hqxg
    rw [hqe] at hqxr
    exact partner_chain_of_below c hs huR hq₁c hqxr hmin₁
  have hbelow₂ : (¬ ∀ q, Reach c u q →
      c.getD q (.cst false) ≠ CGate.var ⟨3 * g + 2, hc2⟩) → Chain c q₂ u := by
    intro hnb
    push_neg at hnb
    obtain ⟨qx, hqxr, hqxg⟩ := hnb
    have h1 := reach_le hqxr
    have hqxc : qx ∈ cone c :=
      mem_cone.mpr ⟨by omega, reach_inCone (mem_cone.mp huc).2 hqxr⟩
    have hqe : qx = q₂ := hu₂ qx hqxc hqxg
    rw [hqe] at hqxr
    exact partner_chain_of_below c hs huR hq₂c hqxr hmin₂
  -- chosen-coordinate rotation
  rcases hPdisj with hch | hch | hch
  · -- chosen coordinate 3g; partners 3g+1, 3g+2
    by_cases hFa : ∀ q, Reach c u q →
        c.getD q (.cst false) ≠ CGate.var ⟨3 * g + 1, hb⟩
    · by_cases hFb : ∀ q, Reach c u q →
          c.getD q (.cst false) ≠ CGate.var ⟨3 * g + 2, hc2⟩
      · refine ⟨u, huR, 3 * g, ha, q₀, by omega, hq₀c, hu₀, hch, ?_⟩
        intro t ht hdiv hne q hrq hgq
        have hcases : t = 3 * g + 1 ∨ t = 3 * g + 2 := by omega
        rcases hcases with he | he
        · have hfe : (⟨t, ht⟩ : Fin (3 * m)) = ⟨3 * g + 1, hb⟩ := Fin.ext he
          rw [hfe] at hgq
          exact hFa q hrq hgq
        · have hfe : (⟨t, ht⟩ : Fin (3 * m)) = ⟨3 * g + 2, hc2⟩ := Fin.ext he
          rw [hfe] at hgq
          exact hFb q hrq hgq
      · exact (intra_gadget_kill m c hcomp hs u hult
          (3 * g) (3 * g + 2) (3 * g + 1) ha hc2 hb
          (by omega) (by omega) (by omega) (by omega) (by omega)
          (chain_sole_var₀ c hs hq₀c hch hu₀)
          (chain_sole_var₀ c hs hq₂c (hbelow₂ hFb) hu₂) hFa).elim
    · have hch₁' : Chain c q₁ u := hbelow₁ hFa
      by_cases hFb : ∀ q, Reach c u q →
          c.getD q (.cst false) ≠ CGate.var ⟨3 * g + 2, hc2⟩
      · exact (intra_gadget_kill m c hcomp hs u hult
          (3 * g) (3 * g + 1) (3 * g + 2) ha hb hc2
          (by omega) (by omega) (by omega) (by omega) (by omega)
          (chain_sole_var₀ c hs hq₀c hch hu₀)
          (chain_sole_var₀ c hs hq₁c hch₁' hu₁) hFb).elim
      · exact (chain_bottleneck_kill m c hcomp hs g hg ha hb hc2
          u huc huroot q₀ q₁ q₂ hq₀c hq₁c hq₂c hg₀ hg₁ hg₂ hu₀ hu₁ hu₂
          hch hch₁' (hbelow₂ hFb)).elim
  · -- chosen coordinate 3g+1; partners 3g, 3g+2
    by_cases hFa : ∀ q, Reach c u q →
        c.getD q (.cst false) ≠ CGate.var ⟨3 * g, ha⟩
    · by_cases hFb : ∀ q, Reach c u q →
          c.getD q (.cst false) ≠ CGate.var ⟨3 * g + 2, hc2⟩
      · refine ⟨u, huR, 3 * g + 1, hb, q₁, by omega, hq₁c, hu₁, hch, ?_⟩
        intro t ht hdiv hne q hrq hgq
        have hcases : t = 3 * g ∨ t = 3 * g + 2 := by omega
        rcases hcases with he | he
        · have hfe : (⟨t, ht⟩ : Fin (3 * m)) = ⟨3 * g, ha⟩ := Fin.ext he
          rw [hfe] at hgq
          exact hFa q hrq hgq
        · have hfe : (⟨t, ht⟩ : Fin (3 * m)) = ⟨3 * g + 2, hc2⟩ := Fin.ext he
          rw [hfe] at hgq
          exact hFb q hrq hgq
      · exact (intra_gadget_kill m c hcomp hs u hult
          (3 * g + 1) (3 * g + 2) (3 * g) hb hc2 ha
          (by omega) (by omega) (by omega) (by omega) (by omega)
          (chain_sole_var₀ c hs hq₁c hch hu₁)
          (chain_sole_var₀ c hs hq₂c (hbelow₂ hFb) hu₂) hFa).elim
    · have hch₀' : Chain c q₀ u := hbelow₀ hFa
      by_cases hFb : ∀ q, Reach c u q →
          c.getD q (.cst false) ≠ CGate.var ⟨3 * g + 2, hc2⟩
      · exact (intra_gadget_kill m c hcomp hs u hult
          (3 * g + 1) (3 * g) (3 * g + 2) hb ha hc2
          (by omega) (by omega) (by omega) (by omega) (by omega)
          (chain_sole_var₀ c hs hq₁c hch hu₁)
          (chain_sole_var₀ c hs hq₀c hch₀' hu₀) hFb).elim
      · exact (chain_bottleneck_kill m c hcomp hs g hg ha hb hc2
          u huc huroot q₀ q₁ q₂ hq₀c hq₁c hq₂c hg₀ hg₁ hg₂ hu₀ hu₁ hu₂
          hch₀' hch (hbelow₂ hFb)).elim
  · -- chosen coordinate 3g+2; partners 3g, 3g+1
    by_cases hFa : ∀ q, Reach c u q →
        c.getD q (.cst false) ≠ CGate.var ⟨3 * g, ha⟩
    · by_cases hFb : ∀ q, Reach c u q →
          c.getD q (.cst false) ≠ CGate.var ⟨3 * g + 1, hb⟩
      · refine ⟨u, huR, 3 * g + 2, hc2, q₂, by omega, hq₂c, hu₂, hch, ?_⟩
        intro t ht hdiv hne q hrq hgq
        have hcases : t = 3 * g ∨ t = 3 * g + 1 := by omega
        rcases hcases with he | he
        · have hfe : (⟨t, ht⟩ : Fin (3 * m)) = ⟨3 * g, ha⟩ := Fin.ext he
          rw [hfe] at hgq
          exact hFa q hrq hgq
        · have hfe : (⟨t, ht⟩ : Fin (3 * m)) = ⟨3 * g + 1, hb⟩ := Fin.ext he
          rw [hfe] at hgq
          exact hFb q hrq hgq
      · exact (intra_gadget_kill m c hcomp hs u hult
          (3 * g + 2) (3 * g + 1) (3 * g) hc2 hb ha
          (by omega) (by omega) (by omega) (by omega) (by omega)
          (chain_sole_var₀ c hs hq₂c hch hu₂)
          (chain_sole_var₀ c hs hq₁c (hbelow₁ hFb) hu₁) hFa).elim
    · have hch₀' : Chain c q₀ u := hbelow₀ hFa
      by_cases hFb : ∀ q, Reach c u q →
          c.getD q (.cst false) ≠ CGate.var ⟨3 * g + 1, hb⟩
      · exact (intra_gadget_kill m c hcomp hs u hult
          (3 * g + 2) (3 * g) (3 * g + 1) hc2 ha hb
          (by omega) (by omega) (by omega) (by omega) (by omega)
          (chain_sole_var₀ c hs hq₂c hch hu₂)
          (chain_sole_var₀ c hs hq₀c hch₀' hu₀) hFb).elim
      · exact (chain_bottleneck_kill m c hcomp hs g hg ha hb hc2
          u huc huroot q₀ q₁ q₂ hq₀c hq₁c hq₂c hg₀ hg₁ hg₂ hu₀ hu₁ hu₂
          hch₀' (hbelow₁ hFb) hch).elim

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.partner_chain_of_below
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.gadget_FF_branch
