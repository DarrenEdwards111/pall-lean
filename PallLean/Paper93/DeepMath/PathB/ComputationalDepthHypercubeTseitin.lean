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
open PallLean.Paper93.DeepMath.PathB.TseitinResolution
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

/-- A vertex incident to an edge determines that edge's anchored endpoint. -/
theorem endpoint_of_incident (v : Fin k → ZMod 2) (e : HCEdge k)
    (he : v ∈ (hypercubeGraph k).endpoints e) :
    e.1.1 = if v e.1.2 = 0 then v else flip v e.1.2 := by
  have he' : v = e.1.1 ∨ v = flip e.1.1 e.1.2 := by
    simpa [hypercubeGraph, Finset.mem_insert, Finset.mem_singleton] using he
  split
  · rename_i hv0
    rcases he' with h | h
    · exact h.symm
    · exfalso
      rw [h] at hv0
      simp only [flip, Function.update_self] at hv0
      rw [e.2] at hv0
      exact absurd hv0 (by decide)
  · rename_i hv0
    rcases he' with h | h
    · exact absurd (by rw [h]; exact e.2) hv0
    · rw [h, flip_flip]

/-- **Degree bound.**  Every vertex of `Q_k` lies on at most `k` edges. -/
theorem hypercube_degree (k : ℕ) (v : Fin k → ZMod 2) :
    (TseitinResolution.incident (hypercubeGraph k) v).card ≤ k := by
  refine le_trans (Finset.card_le_card_of_injOn (fun e => e.1.2)
    (fun e _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_)
    (le_of_eq (by rw [Finset.card_univ, Fintype.card_fin]))
  intro e he e' he' heq
  replace he := (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2
  replace he' := (Finset.mem_filter.mp (Finset.mem_coe.mp he')).2
  have h2 : e.1.2 = e'.1.2 := heq
  have hx : e.1.1 = e'.1.1 := by
    rw [endpoint_of_incident v e he, endpoint_of_incident v e' he', h2]
  exact Subtype.ext (Prod.ext hx h2)

/-- **Explicit, numeric exponential resolution size lower bound.**  The Tseitin CNF
on the hypercube `Q_k` with odd charge (indicator of the all-zeros vertex) requires
resolution refutations of size `> 2^{t - k - 1}` for every `t` with `1 ≤ t`,
`4t ≤ 2^k`, and `k < t`.  Taking `t = 2^k/4` gives size `2^{Ω(2^k)} = 2^{Ω(|V|)}`. -/
theorem hypercube_tseitin_exp_size (k : ℕ) {t : ℕ}
    (ht1 : 1 ≤ t) (hcard : 4 * t ≤ 2 ^ k) (hgap : k < t)
    (Der : ResolutionDerivation tcompl
      (TseitinResolution.TseitinCNF (hypercubeGraph k) (fun v => if v = 0 then 1 else 0))
      (∅ : ResolutionClause (TLit (HCEdge k)))) :
    2 ^ (t - k - 1) < ResolutionDerivation.size Der := by
  have hV : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by rw [Fintype.card_pi_const, ZMod.card]
  have hodd : ∑ v : Fin k → ZMod 2, (if v = 0 then (1 : ZMod 2) else 0) = 1 := by
    rw [Finset.sum_ite_eq']; simp
  have hmain := TseitinResolution.tseitinCNF_exp_size (hypercubeGraph k)
    (fun v => if v = 0 then 1 else 0) hodd (c := 1) (t := t) (w₀ := k)
    (le_refl 1) (hypercube_hasExpansion k) ht1 (by rw [hV]; exact hcard)
    (hypercube_degree k) (by omega) Der
  rwa [one_mul] at hmain

end PallLean.Paper93.DeepMath.PathB.Hypercube

#print axioms PallLean.Paper93.DeepMath.PathB.Hypercube.hypercube_tseitin_exp_size
