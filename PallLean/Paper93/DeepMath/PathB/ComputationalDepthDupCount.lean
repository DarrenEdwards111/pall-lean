import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGadgetProfile

/-!
# Brick G4 of the ∀m finish: the duplicate count

Gadgets that are not bit-served pay for themselves in duplicate var gates:

* `BitServed` / `GadgetServed` — a coordinate has a UNIQUE cone var gate; a
  gadget is served when all its coordinates are;
* **`dup_plus_vars_le` (proved)** — `D + 3m ≤ |coneVars|`: the 3m first gates
  (one per variable, via `var_position_exists` on `depSet_AEm = univ`) plus one
  SECOND gate per unserved gadget (its unserved coordinate has two distinct cone
  gates) inject disjointly into the cone var-gate positions.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-- A coordinate is bit-served when it has a unique cone var gate. -/
def BitServed {n : ℕ} (c : List (CGate n)) (i : Fin n) : Prop :=
  ∃ q, q ∈ cone c ∧ c.getD q (.cst false) = CGate.var i ∧
    ∀ q' ∈ cone c, c.getD q' (.cst false) = CGate.var i → q' = q

/-- A gadget is served when all its coordinates are bit-served. -/
def GadgetServed {n : ℕ} (c : List (CGate n)) (g : ℕ) : Prop :=
  ∀ i : Fin n, i.val / 3 = g → BitServed c i

/-- **THE DUPLICATE COUNT (proved)**: unserved gadgets plus the variable count
are dominated by the cone var-gate positions. -/
theorem dup_plus_vars_le (m : ℕ) (c : List (CGate (3 * m)))
    (hcomp : computes c (AEm m)) (hs : 0 < c.length)
    (Dset : Finset ℕ) (hD : ∀ g ∈ Dset, g < m ∧ ¬ GadgetServed c g) :
    Dset.card + 3 * m ≤ (coneVars c).card := by
  classical
  -- one gate per variable
  have hex : ∀ i : Fin (3 * m), ∃ w, w ∈ cone c
      ∧ c.getD w (.cst false) = CGate.var i := fun i =>
    var_position_exists (AEm m) c hcomp hs i
      (by rw [depSet_AEm]; exact Finset.mem_univ i)
  choose αf hαf using hex
  -- one SECOND gate per unserved gadget
  have hβex : ∀ g : ℕ, ∃ w, g ∈ Dset → w ∈ cone c ∧ ∃ i : Fin (3 * m),
      c.getD w (.cst false) = CGate.var i ∧ i.val / 3 = g ∧ w ≠ αf i := by
    intro g
    by_cases hg : g ∈ Dset
    · obtain ⟨hgm, hns⟩ := hD g hg
      simp only [GadgetServed] at hns
      push_neg at hns
      obtain ⟨i, hidiv, hnb⟩ := hns
      have h2 : ∃ w', w' ∈ cone c ∧ c.getD w' (.cst false) = CGate.var i
          ∧ w' ≠ αf i := by
        by_contra hno
        push_neg at hno
        exact hnb ⟨αf i, (hαf i).1, (hαf i).2, hno⟩
      obtain ⟨w', hw'c, hw'g, hw'ne⟩ := h2
      exact ⟨w', fun _ => ⟨hw'c, i, hw'g, hidiv, hw'ne⟩⟩
    · exact ⟨0, fun h => absurd h hg⟩
  choose βf hβf using hβex
  -- the two images sit disjointly inside coneVars
  have hαinj : Set.InjOn αf ↑(Finset.univ : Finset (Fin (3 * m))) := by
    intro i₁ _ i₂ _ he
    have g₁ := (hαf i₁).2
    have g₂ := (hαf i₂).2
    rw [he] at g₁
    rw [g₂] at g₁
    exact (CGate.var.inj g₁).symm
  have hβinj : Set.InjOn βf ↑Dset := by
    intro g₁ h₁ g₂ h₂ he
    obtain ⟨hc₁, i₁, hg₁, hd₁, -⟩ := hβf g₁ (Finset.mem_coe.mp h₁)
    obtain ⟨hc₂, i₂, hg₂, hd₂, -⟩ := hβf g₂ (Finset.mem_coe.mp h₂)
    rw [he] at hg₁
    rw [hg₂] at hg₁
    have hii := CGate.var.inj hg₁
    rw [← hd₁, ← hd₂, hii]
  have hAsub : Finset.image αf Finset.univ ⊆ coneVars c := by
    intro w hw
    obtain ⟨i, -, heA⟩ := Finset.mem_image.mp hw
    rw [← heA]
    exact Finset.mem_filter.mpr ⟨(hαf i).1, ⟨i, (hαf i).2⟩⟩
  have hBsub : Finset.image βf Dset ⊆ coneVars c := by
    intro w hw
    obtain ⟨g, hgD, heB⟩ := Finset.mem_image.mp hw
    obtain ⟨hcB, i', hg', -, -⟩ := hβf g hgD
    rw [← heB]
    exact Finset.mem_filter.mpr ⟨hcB, ⟨i', hg'⟩⟩
  have hdisj : Disjoint (Finset.image αf Finset.univ) (Finset.image βf Dset) := by
    rw [Finset.disjoint_left]
    intro w hwA hwB
    obtain ⟨i, -, heA⟩ := Finset.mem_image.mp hwA
    obtain ⟨g, hgD, heB⟩ := Finset.mem_image.mp hwB
    obtain ⟨hcB, i', hg', hd', hne'⟩ := hβf g hgD
    have gA := (hαf i).2
    rw [heA] at gA
    have gB := hg'
    rw [heB] at gB
    rw [gA] at gB
    have hii := CGate.var.inj gB
    exact hne' (by rw [heB, ← heA, hii])
  have hAcard : (Finset.image αf Finset.univ).card = 3 * m := by
    rw [Finset.card_image_of_injOn hαinj, Finset.card_univ, Fintype.card_fin]
  have hBcard : (Finset.image βf Dset).card = Dset.card := by
    rw [Finset.card_image_of_injOn hβinj]
  calc Dset.card + 3 * m
      = (Finset.image αf Finset.univ).card + (Finset.image βf Dset).card := by
        rw [hAcard, hBcard]
        omega
    _ = (Finset.image αf Finset.univ ∪ Finset.image βf Dset).card := by
        rw [Finset.card_union_of_disjoint hdisj]
    _ ≤ (coneVars c).card :=
        Finset.card_le_card (Finset.union_subset hAsub hBsub)

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.dup_plus_vars_le
