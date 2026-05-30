import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHypercubeIsoperimetric
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinCNF

/-!
# The hypercube as a Tseitin graph, and its numeric exponential size bound

We realise the hypercube `Q_k` as a `TseitinGraph` (edges = `{x, flip x i}`,
anchored at the endpoint with `i`-th coordinate `0`), show its edge boundary
equals `bdry` (so Harper's inequality gives `HasExpansion 1`), and instantiate the
canonical-CNF exponential size lower bound to obtain a fully explicit, numeric
result.
-/

namespace PallLean.Paper93.DeepMath.PathB.Hypercube

open PallLean.Paper93.DeepMath.PathB
open scoped BigOperators

/-- Hypercube edges, anchored at the endpoint whose `i`-th coordinate is `0`. -/
abbrev HCEdge (k : ℕ) := {p : (Fin k → ZMod 2) × Fin k // p.1 p.2 = 0}

/-- The hypercube `Q_k` as a Tseitin graph. -/
def hypercubeGraph (k : ℕ) : TseitinGraph (Fin k → ZMod 2) (HCEdge k) where
  endpoints e := {e.1.1, flip e.1.1 e.1.2}
  card_endpoints e := Finset.card_pair (flip_ne e.1.1 e.1.2).symm

variable {k : ℕ}

/-- `bdry S` as the cardinality of the product filter of "boundary darts". -/
theorem bdry_eq_prod (S : Finset (Fin k → ZMod 2)) :
    bdry S = (Finset.univ.filter
      (fun p : (Fin k → ZMod 2) × Fin k => p.1 ∈ S ∧ flip p.1 p.2 ∉ S)).card := by
  rw [bdry, Finset.card_eq_sum_card_fiberwise (f := fun p => p.2) (fun p _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [dirBdry]
  refine Finset.card_bij' (fun z _ => ((z, i) : (Fin k → ZMod 2) × Fin k)) (fun p _ => p.1)
    ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact ⟨hz, trivial⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨⟨hpS, hpf⟩, hp2⟩ := hp
    rw [hp2] at hpf
    exact ⟨hpS, hpf⟩
  · intro z _; rfl
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact Prod.ext rfl hp.2.symm

/-- The coordinate-`0` endpoint of the edge a boundary dart `(z, i)` lies on. -/
def anchor (p : (Fin k → ZMod 2) × Fin k) : Fin k → ZMod 2 :=
  if p.1 p.2 = 0 then p.1 else flip p.1 p.2

theorem anchor_coord (p : (Fin k → ZMod 2) × Fin k) : anchor p p.2 = 0 := by
  unfold anchor
  split
  · assumption
  · rename_i h
    simp only [flip, Function.update_self]
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (p.1 p.2) with h0 | h1
    · exact absurd h0 h
    · rw [h1]; decide

/-- The hypercube edge carrying a boundary dart `(z, i)`. -/
def anchoredEdge (p : (Fin k → ZMod 2) × Fin k) : HCEdge k := ⟨(anchor p, p.2), anchor_coord p⟩

theorem endpoints_anchored (p : (Fin k → ZMod 2) × Fin k) :
    (hypercubeGraph k).endpoints (anchoredEdge p) = {p.1, flip p.1 p.2} := by
  show ({anchor p, flip (anchor p) p.2} : Finset (Fin k → ZMod 2)) = {p.1, flip p.1 p.2}
  unfold anchor
  split
  · rfl
  · rw [flip_flip]; exact Finset.pair_comm _ _

/-- **Boundary darts inject into graph edge boundary.**  Hence `bdry S` (the dart
count) is at most the graph's edge boundary. -/
theorem bdry_le_boundary (S : Finset (Fin k → ZMod 2)) :
    bdry S ≤ ((hypercubeGraph k).boundary S).card := by
  rw [bdry_eq_prod]
  refine Finset.card_le_card_of_injOn anchoredEdge ?_ ?_
  · intro p hp
    replace hp := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2
    rw [Finset.mem_coe, TseitinGraph.boundary, Finset.mem_filter, endpoints_anchored]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hinter : ({p.1, flip p.1 p.2} : Finset (Fin k → ZMod 2)) ∩ S = {p.1} := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hx | hx, hxS⟩
        · exact hx
        · exact absurd (hx ▸ hxS) hp.2
      · rintro rfl; exact ⟨Or.inl rfl, hp.1⟩
    rw [hinter, Finset.card_singleton]
  · intro p hp p' hp' heq
    replace hp := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2
    replace hp' := (Finset.mem_filter.mp (Finset.mem_coe.mp hp')).2
    have h2 : p.2 = p'.2 := congrArg (fun e => e.1.2) heq
    have hset : ({p.1, flip p.1 p.2} : Finset (Fin k → ZMod 2)) = {p'.1, flip p'.1 p'.2} := by
      rw [← endpoints_anchored, ← endpoints_anchored, heq]
    have hp1 : p.1 = p'.1 := by
      have hmem : p.1 ∈ ({p'.1, flip p'.1 p'.2} : Finset (Fin k → ZMod 2)) := by
        rw [← hset]; exact Finset.mem_insert_self _ _
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact h
      · exact absurd (h ▸ hp.1) hp'.2
    exact Prod.ext hp1 h2

/-- **`HasExpansion 1`** for the hypercube, from Harper's inequality and the dart
injection. -/
theorem hypercube_hasExpansion (k : ℕ) : (hypercubeGraph k).HasExpansion 1 := by
  intro S h1 h2
  rw [one_mul]
  have hk : 2 * S.card ≤ 2 ^ k := by
    rwa [show Fintype.card (Fin k → ZMod 2) = 2 ^ k from by
      rw [Fintype.card_pi_const, ZMod.card]] at h2
  exact le_trans (harper k S hk) (bdry_le_boundary S)

end PallLean.Paper93.DeepMath.PathB.Hypercube
