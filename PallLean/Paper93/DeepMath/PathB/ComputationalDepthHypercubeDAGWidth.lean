import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResolutionDAG
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHypercubeTseitin

/-!
# Concrete general-resolution width lower bound for the hypercube-Tseitin CNF

Combining the general (DAG) resolution width bound with the proven hypercube
expander, every **unrestricted (DAG) resolution** refutation of the explicit
hypercube-Tseitin CNF contains a clause of width `≥ t` for every `t` with
`2 ≤ t` and `4t ≤ 2^k` — taking `t = 2^k/4` gives width `Ω(|V|)`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Hypercube

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.TseitinResolution
open scoped BigOperators

/-- **Concrete DAG width bound.**  Every general resolution refutation of the
hypercube-Tseitin CNF (odd charge) has a clause of width `≥ t` (for `2 ≤ t`,
`4t ≤ 2^k`).  At `t = 2^k/4` this is `Ω(|V|)`. -/
theorem hypercube_dag_width (k : ℕ) {t : ℕ} (ht2 : 2 ≤ t) (hcard : 4 * t ≤ 2 ^ k) {n : ℕ}
    (D : ResolutionDAG tcompl
      (TseitinCNF (hypercubeGraph k) (fun v => if v = 0 then 1 else 0)) n)
    (i₀ : Fin n) (hi₀ : D.clause i₀ = (∅ : ResolutionClause (TLit (HCEdge k)))) :
    ∃ i : Fin n, t ≤ ResolutionClause.width (D.clause i) := by
  have hV : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by rw [Fintype.card_pi_const, ZMod.card]
  have hodd : ∑ v : Fin k → ZMod 2, (if v = 0 then (1 : ZMod 2) else 0) = 1 := by
    rw [Finset.sum_ite_eq']; simp
  have hmain := dag_resolution_width_lower_bound (hypercubeGraph k)
    (fun v => if v = 0 then 1 else 0) (tseitin_unsat _ _ hodd)
    (TseitinCNF (hypercubeGraph k) (fun v => if v = 0 then 1 else 0))
    (tseitinCNF_implies _ _) (c := 1) (t := t) (le_refl 1) (hypercube_hasExpansion k) ht2
    (by rw [hV]; exact hcard) D i₀ hi₀
  simpa only [one_mul] using hmain

end PallLean.Paper93.DeepMath.PathB.Hypercube

#print axioms PallLean.Paper93.DeepMath.PathB.Hypercube.hypercube_dag_width
