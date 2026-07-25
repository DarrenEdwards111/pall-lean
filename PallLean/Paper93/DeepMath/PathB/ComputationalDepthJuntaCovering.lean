import PallLean.Paper93.DeepMath.PathB.ComputationalDepthJuntaHitting
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Discharging the covering step: every `k`-junta is a renamed `k`-variable polynomial

`JuntaHitting` left one elementary gap: to hit the *full* unknown-support `k`-junta class from
`juntaGrid_hits`, one needs that every degree-`d` polynomial depending on `≤ k` variables actually has
the form `rename e q` for some embedding `e : Fin k ↪ Fin n` and `k`-variable `q`.  This file proves
that (the **covering step**) by `MvPolynomial` support analysis, and combines it with
`juntaGrid_hits` into a self-contained hitting theorem for the whole class — unconditionally.

* **`totalDegree_rename_of_injective` (proved)** — injective renaming preserves total degree, via
  `support_rename_of_injective` and `toMultiset_map` (so the extracted `q` has the same degree as the
  junta, and the degree hypothesis transfers).
* **`junta_covering` (proved)** — if `p.vars.card ≤ k ≤ n`, then `p = rename e q` for some
  `e : Fin k ↪ Fin n` and `q : MvPolynomial (Fin k) F`.  (Enlarge `p.vars` to a `k`-set `T'`
  (`exists_subsuperset_card_eq`), take `e` = `T'.orderEmbOfFin`, and apply
  `exists_rename_eq_of_vars_subset_range` since `p.vars ⊆ range e`.)
* **`junta_class_hit` (proved capstone)** — every nonzero `p` with `p.vars.card ≤ k ≤ n` and
  `totalDegree p < #S` is non-vanishing at some point of a junta grid: the `k`-junta class is hit,
  fully and unconditionally.

**Honest scope.**  This closes the `k`-junta hitting set completely (per-embedding grid of size `(#S)ᵏ`,
union over `\binom{n}{k}` embeddings = `poly(n)` for fixed `k`) with no remaining socket.  It is a real
unconditional small hitting set for an arity-growing class — but only for the *junta* restriction; the
general sparse / small-circuit case remains the open derandomization target.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.JuntaCovering

open PallLean.Paper93.DeepMath.PathB.SchwartzZippel
open PallLean.Paper93.DeepMath.PathB.JuntaHitting

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Injective renaming preserves total degree (proved).**  Renaming the variables by an injective
map neither raises nor lowers the total degree: each monomial's exponent multiset is relocated by an
injection, preserving its cardinality (`support_rename_of_injective` + `toMultiset_map`). -/
theorem totalDegree_rename_of_injective {σ τ : Type*} [DecidableEq τ] {f : σ → τ}
    (hf : Function.Injective f) (p : MvPolynomial σ F) :
    (MvPolynomial.rename f p).totalDegree = p.totalDegree := by
  rw [MvPolynomial.totalDegree_eq, MvPolynomial.totalDegree_eq,
    MvPolynomial.support_rename_of_injective hf, Finset.sup_image]
  apply Finset.sup_congr rfl
  intro m _
  show Multiset.card (Finsupp.toMultiset (Finsupp.mapDomain f m))
      = Multiset.card (Finsupp.toMultiset m)
  rw [← Finsupp.toMultiset_map, Multiset.card_map]

/-- **The covering step (proved).**  A polynomial in `n` variables depending on at most `k ≤ n` of
them equals `rename e q` for some embedding `e : Fin k ↪ Fin n` and `k`-variable polynomial `q` — i.e.
every `k`-junta is a genuine `k`-variable polynomial reindexed into `Fⁿ`. -/
theorem junta_covering {k n : ℕ} (hkn : k ≤ n) (p : MvPolynomial (Fin n) F)
    (hvars : p.vars.card ≤ k) :
    ∃ (e : Fin k ↪ Fin n) (q : MvPolynomial (Fin k) F), p = MvPolynomial.rename (⇑e) q := by
  classical
  obtain ⟨T', hsub, -, hcard⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ p.vars) hvars
      (by rw [Finset.card_univ, Fintype.card_fin]; exact hkn)
  refine ⟨(T'.orderEmbOfFin hcard).toEmbedding, ?_⟩
  have hrange : Set.range (⇑((T'.orderEmbOfFin hcard).toEmbedding) : Fin k → Fin n)
      = (↑T' : Set (Fin n)) := by
    rw [RelEmbedding.coe_toEmbedding]
    exact T'.range_orderEmbOfFin hcard
  have hvarsub : (↑p.vars : Set (Fin n))
      ⊆ Set.range (⇑((T'.orderEmbOfFin hcard).toEmbedding) : Fin k → Fin n) := by
    rw [hrange]; exact Finset.coe_subset.mpr hsub
  obtain ⟨q, hq⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range p
    (⇑((T'.orderEmbOfFin hcard).toEmbedding)) ((T'.orderEmbOfFin hcard).toEmbedding.injective) hvarsub
  exact ⟨q, hq.symm⟩

/-- **The full `k`-junta class is hit (proved capstone).**  Every nonzero `p : MvPolynomial (Fin n) F`
that depends on at most `k ≤ n` variables and has total degree `< #S` is non-vanishing at some point of
a junta grid `juntaGrid e base S`.  Combines `junta_covering` (extract `e`, `q`),
`totalDegree_rename_of_injective` (transfer the degree bound to `q`), and `juntaGrid_hits`. -/
theorem junta_class_hit {k n : ℕ} (hkn : k ≤ n) (base : Fin n → F) (S : Finset F)
    (p : MvPolynomial (Fin n) F) (hp0 : p ≠ 0) (hvars : p.vars.card ≤ k)
    (hdeg : p.totalDegree < S.card) :
    ∃ (e : Fin k ↪ Fin n) (f : Fin n → F),
      f ∈ juntaGrid e base S ∧ MvPolynomial.eval f p ≠ 0 := by
  obtain ⟨e, q, rfl⟩ := junta_covering hkn p hvars
  have hq0 : q ≠ 0 := fun h => hp0 (by rw [h]; simp)
  have hdq : q.totalDegree < S.card := by
    rwa [totalDegree_rename_of_injective e.injective] at hdeg
  obtain ⟨f, hf, hfne⟩ := juntaGrid_hits e base S q hq0 hdq
  exact ⟨e, f, hf, hfne⟩

end PallLean.Paper93.DeepMath.PathB.JuntaCovering

#print axioms PallLean.Paper93.DeepMath.PathB.JuntaCovering.totalDegree_rename_of_injective
#print axioms PallLean.Paper93.DeepMath.PathB.JuntaCovering.junta_covering
#print axioms PallLean.Paper93.DeepMath.PathB.JuntaCovering.junta_class_hit
