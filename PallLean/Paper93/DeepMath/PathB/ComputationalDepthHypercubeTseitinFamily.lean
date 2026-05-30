import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHypercubeTseitin

/-!
# The hypercube-Tseitin family: a self-contained explicit exponential bound

Specialising `hypercube_tseitin_exp_size` at `t = 2^k/4 = 2^{k-2}` removes the free
parameter: for **every** `k ≥ 5`, the hypercube-Tseitin CNF — an explicit
unsatisfiable CNF on `k · 2^{k-1}` variables — requires tree-like resolution
refutations of size `> 2^{2^{k-2} - k - 1}`, i.e. `2^{Ω(|V|)}`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Hypercube

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.TseitinResolution

/-- `k < 2^{k-2}` for `k ≥ 5` (so the width bound `c·t` exceeds the initial width). -/
theorem lt_two_pow_sub_two (k : ℕ) (hk : 5 ≤ k) : k < 2 ^ (k - 2) := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have hpow : (2 : ℕ) ^ (k - 1) = 2 ^ (k - 2) * 2 := by
      rw [show k - 1 = (k - 2) + 1 from by omega, pow_succ]
    rw [show k + 1 - 2 = (k - 2) + 1 from by omega, pow_succ]
    omega

/-- **The hypercube-Tseitin family.**  For every `k ≥ 5`, every tree-like resolution
refutation of the hypercube-Tseitin CNF (odd charge) has size `> 2^{2^{k-2}-k-1}`. -/
theorem hypercube_tseitin_family (k : ℕ) (hk : 5 ≤ k)
    (Der : ResolutionDerivation tcompl
      (TseitinCNF (hypercubeGraph k) (fun v => if v = 0 then 1 else 0))
      (∅ : ResolutionClause (TLit (HCEdge k)))) :
    2 ^ (2 ^ (k - 2) - k - 1) < ResolutionDerivation.size Der :=
  hypercube_tseitin_exp_size k (t := 2 ^ (k - 2))
    (Nat.one_le_pow _ _ (by norm_num))
    (by rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]
        exact Nat.pow_le_pow_right (by norm_num) (by omega))
    (lt_two_pow_sub_two k hk) Der

end PallLean.Paper93.DeepMath.PathB.Hypercube

#print axioms PallLean.Paper93.DeepMath.PathB.Hypercube.hypercube_tseitin_family
