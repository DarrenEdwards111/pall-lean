import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDupCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCaseBKills

/-!
# Brick G5 of the ∀m finish: THE ASSEMBLY — `SlackComposes` is DISCHARGED

The counting: with `B` the served gadgets, `D` the unserved, `t = |reconvR|`,
`W = |coneVars|`, `X = excessX`, `C = |cone|`:

* `B ≤ t` (**`served_le_reconv`**): each served gadget owns an (F,F) first
  branch (`gadget_FF_branch`); two gadgets sharing one die by
  `one_side_pair_kill`, so the branch map is injective into `reconvR`;
* `D + 3m ≤ W` (G4 `dup_plus_vars_le`);
* `2W + X ≤ C + 1` (`cone_ge_slot`), `t ≤ X` (`reconvR_card_le`), `C ≤ length`;
* hence `length ≥ 2(D + 3m) + B − 1 ≥ 6m + (B + D) − 1 = 7m − 1` on the
  OPTIMAL circuit: **`slackComposes_all : ∀ m, 7m − 1 ≤ cbudget (AEm m)`**,
  and the named open statement **`SlackComposes` is proved**
  (`slackComposes : SlackComposes`).

This is the linear direct-sum theorem for the `AEm` family — one slack unit per
gadget, `+1` beyond the floor `6m − 1` at every gadget.  It is a RESTRICTED
result about this family in the `CGate` model.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-- The (F,F) first-branch data of a gadget at a wire. -/
def FFat (m : ℕ) (c : List (CGate (3 * m))) (g u : ℕ) : Prop :=
  ∃ (p : ℕ) (hp : p < 3 * m) (qp : ℕ),
    p / 3 = g ∧ qp ∈ cone c ∧
    (∀ q' ∈ cone c, c.getD q' (.cst false) = CGate.var ⟨p, hp⟩ → q' = qp) ∧
    Chain c qp u ∧
    ∀ (t : ℕ) (ht : t < 3 * m), t / 3 = p / 3 → t ≠ p →
      ∀ q, Reach c u q → c.getD q (.cst false) ≠ CGate.var ⟨t, ht⟩

/-- **B ≤ t (proved)**: served gadgets inject into the reconvergences. -/
theorem served_le_reconv (m : ℕ) (c : List (CGate (3 * m)))
    (hcomp : computes c (AEm m)) (hs : 0 < c.length)
    (Bset : Finset ℕ) (hB : ∀ g ∈ Bset, g < m ∧ GadgetServed c g) :
    Bset.card ≤ (reconvR c).card := by
  classical
  have hFF : ∀ g ∈ Bset, ∃ u, u ∈ reconvR c ∧ FFat m c g u := by
    intro g hg
    obtain ⟨hgm, hserv⟩ := hB g hg
    have ha : 3 * g < 3 * m := by omega
    have hb : 3 * g + 1 < 3 * m := by omega
    have hc2 : 3 * g + 2 < 3 * m := by omega
    obtain ⟨q₀, hq₀c, hg₀, hu₀⟩ :=
      hserv ⟨3 * g, ha⟩ (show 3 * g / 3 = g by omega)
    obtain ⟨q₁, hq₁c, hg₁, hu₁⟩ :=
      hserv ⟨3 * g + 1, hb⟩ (show (3 * g + 1) / 3 = g by omega)
    obtain ⟨q₂, hq₂c, hg₂, hu₂⟩ :=
      hserv ⟨3 * g + 2, hc2⟩ (show (3 * g + 2) / 3 = g by omega)
    obtain ⟨u, huR, htail⟩ := gadget_FF_branch m c hcomp hs g hgm ha hb hc2
      q₀ q₁ q₂ hq₀c hq₁c hq₂c hg₀ hg₁ hg₂ hu₀ hu₁ hu₂
    exact ⟨u, huR, htail⟩
  have hkill : ∀ u ∈ reconvR c, ∀ g₁ ∈ Bset, ∀ g₂ ∈ Bset,
      FFat m c g₁ u → FFat m c g₂ u → g₁ = g₂ := by
    intro u huR g₁ h₁ g₂ h₂ hf₁ hf₂
    by_contra hne
    obtain ⟨p₁, hp₁, qp₁, hd₁, hqc₁, huq₁, hch₁, hfree₁⟩ := hf₁
    obtain ⟨p₂, hp₂, qp₂, hd₂, hqc₂, huq₂, hch₂, hfree₂⟩ := hf₂
    have hgh : p₁ / 3 ≠ p₂ / 3 := fun he => hne (by rw [← hd₁, ← hd₂, he])
    have huc : u ∈ cone c :=
      (Finset.mem_erase.mp (Finset.mem_filter.mp huR).1).2
    have hult : u < c.length := (mem_cone.mp huc).1
    exact one_side_pair_kill m c hcomp hs u hult p₁ p₂ hp₁ hp₂ hgh
      (chain_sole_var₀ c hs hqc₁ hch₁ huq₁)
      (chain_sole_var₀ c hs hqc₂ hch₂ huq₂)
      hfree₂
  refine Finset.card_le_card_of_injOn
    (fun g => if h : ∃ u, u ∈ reconvR c ∧ FFat m c g u then h.choose else 0)
    ?_ ?_
  · intro g hg
    have h := hFF g hg
    simp only [dif_pos h]
    exact h.choose_spec.1
  · intro g₁ h₁ g₂ h₂ he
    have hh₁ := hFF g₁ (Finset.mem_coe.mp h₁)
    have hh₂ := hFF g₂ (Finset.mem_coe.mp h₂)
    simp only [dif_pos hh₁, dif_pos hh₂] at he
    exact hkill hh₁.choose hh₁.choose_spec.1
      g₁ (Finset.mem_coe.mp h₁) g₂ (Finset.mem_coe.mp h₂)
      hh₁.choose_spec.2 (by rw [he]; exact hh₂.choose_spec.2)

/-- **THE ∀m SLACK THEOREM (proved)**: one slack unit per gadget, every `m`. -/
theorem slackComposes_all (m : ℕ) : 7 * m - 1 ≤ cbudget (AEm m) := by
  classical
  obtain ⟨c, hcomp, hclen⟩ := Nat.sInf_mem (cbudget_set_nonempty (AEm m))
  have hclen' : c.length = cbudget (AEm m) := hclen
  rw [← hclen']
  have hs : 0 < c.length := by
    by_contra h0
    push_neg at h0
    have hce : c = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h1 := hcomp (fun _ => true)
    rw [hce] at h1
    have h2 : output ([] : List (CGate (3 * m))) (fun _ => true) = false := rfl
    have hAE : AEm m (fun _ => true) = true := by
      rw [AEm, List.all_eq_true]
      intro j _
      rfl
    rw [h2, hAE] at h1
    exact Bool.noConfusion h1
  set Bset := Finset.filter (fun g => GadgetServed c g) (Finset.range m)
    with hBdef
  set Dset := Finset.filter (fun g => ¬ GadgetServed c g) (Finset.range m)
    with hDdef
  have hBD : Bset.card + Dset.card = m := by
    rw [hBdef, hDdef, Finset.card_filter_add_card_filter_not,
      Finset.card_range]
  have hBmem : ∀ g ∈ Bset, g < m ∧ GadgetServed c g := by
    intro g hg
    rw [hBdef] at hg
    have h := Finset.mem_filter.mp hg
    exact ⟨Finset.mem_range.mp h.1, h.2⟩
  have hDmem : ∀ g ∈ Dset, g < m ∧ ¬ GadgetServed c g := by
    intro g hg
    rw [hDdef] at hg
    have h := Finset.mem_filter.mp hg
    exact ⟨Finset.mem_range.mp h.1, h.2⟩
  have h1 := served_le_reconv m c hcomp hs Bset hBmem
  have h2 := dup_plus_vars_le m c hcomp hs Dset hDmem
  have h3 := cone_ge_slot c hs
  have h4 := reconvR_card_le c
  have h5 : (cone c).card ≤ c.length := by
    have hsub : cone c ⊆ Finset.range c.length := by
      intro w hw
      exact Finset.mem_range.mpr (mem_cone.mp hw).1
    calc (cone c).card ≤ (Finset.range c.length).card :=
          Finset.card_le_card hsub
      _ = c.length := Finset.card_range _
  omega

/-- **THE NAMED OPEN STATEMENT IS DISCHARGED**: `SlackComposes` holds. -/
theorem slackComposes : SlackComposes := fun m _ => slackComposes_all m

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.served_le_reconv
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.slackComposes_all
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.slackComposes
