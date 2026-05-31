import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseInterface
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHypercubeTseitin
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinUnsat

/-!
# Depth-3 collapse gate specialized to hypercube-Tseitin

**STATUS: REAL CONDITIONAL, SPECIALIZED.  COLLAPSE FIELD STILL THE OPEN GATE.**

The generic `Depth3CollapseModel` conditional bridge, instantiated at the concrete
hypercube-Tseitin instance `Q_k` already in the ladder (Rungs 1–2).  The
BSW-side hypotheses are discharged by the proven hypercube facts:

* unsatisfiability — `tseitin_unsat` from the odd charge (indicator of `0`);
* expansion `c = 1` — `Hypercube.hypercube_hasExpansion`;
* `|V| = 2^k`, so `4t ≤ 2^k` suffices.

So: for the hypercube-Tseitin depth-3 collapse model, the width budget
`w₀ + d + k·j < t` (using `c = 1`) forces `2^j ≤ collapseLen (size D)`.  The
`collapse` field of the model — the switching lemma — remains the open gate; this
file only specializes the conditional to the ladder's concrete object.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.TseitinResolution

/-- The odd hypercube charge (indicator of the all-zeros vertex). -/
abbrev hypercubeCharge (k : ℕ) : (Fin k → ZMod 2) → ZMod 2 := fun v => if v = 0 then 1 else 0

theorem hypercubeCharge_odd (k : ℕ) :
    ∑ v : (Fin k → ZMod 2), hypercubeCharge k v = 1 := by
  simp only [hypercubeCharge]
  rw [Finset.sum_ite_eq']
  simp

theorem hypercube_card_V (k : ℕ) : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by
  rw [Fintype.card_pi_const, ZMod.card]

variable {k : ℕ} [Nonempty (Hypercube.HCEdge k)]

/-- **Hypercube-Tseitin depth-3 size lower bound (explicit exponential, conditional).**
Given a depth-3 collapse model for `Q_k`-Tseitin, every refuting circuit has
`2^j ≤ collapseLen (size D)` whenever the doubling condition holds and the width
budget `w₀ + d + kk·j < t` stays below the (`c=1`) expander bound `t`. -/
theorem hypercube_depth3_size_exp
    (M : Depth3CollapseModel (Hypercube.hypercubeGraph k) (hypercubeCharge k))
    {t : ℕ} (ht2 : 2 ≤ t) (hcard : 4 * t ≤ 2 ^ k)
    {d kk j : ℕ} (hd : 0 < d) (hk1 : 1 ≤ kk)
    (hdn : d < Fintype.card (TLit (Hypercube.HCEdge k)))
    (hkd : Fintype.card (TLit (Hypercube.HCEdge k)) - d ≤ kk * d)
    (hsmall : M.w₀ + d + kk * j < t)
    (D : M.Circuit) (hD : M.Refutes D) :
    2 ^ j ≤ M.collapseLen (M.size D) := by
  have hunsat := tseitin_unsat (Hypercube.hypercubeGraph k) (hypercubeCharge k)
    (hypercubeCharge_odd k)
  exact M.size_lower_exp hunsat (le_refl 1) (Hypercube.hypercube_hasExpansion k) ht2
    (by rw [hypercube_card_V]; exact hcard) hd hk1 hdn hkd (by rw [one_mul]; exact hsmall) D hD

/-- **Hypercube-Tseitin depth-3 size lower bound (length form, conditional).** -/
theorem hypercube_depth3_size_length
    (M : Depth3CollapseModel (Hypercube.hypercubeGraph k) (hypercubeCharge k))
    {t : ℕ} (ht2 : 2 ≤ t) (hcard : 4 * t ≤ 2 ^ k) {d b : ℕ} (hd : 0 < d)
    (hsmall : M.w₀ + d + b < t)
    (D : M.Circuit) (hD : M.Refutes D) :
    Fintype.card (TLit (Hypercube.HCEdge k)) ^ b
      ≤ (Fintype.card (TLit (Hypercube.HCEdge k)) - d) ^ b * M.collapseLen (M.size D) := by
  have hunsat := tseitin_unsat (Hypercube.hypercubeGraph k) (hypercubeCharge k)
    (hypercubeCharge_odd k)
  exact M.size_lower_length hunsat (le_refl 1) (Hypercube.hypercube_hasExpansion k) ht2
    (by rw [hypercube_card_V]; exact hcard) hd (by rw [one_mul]; exact hsmall) D hD

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.hypercube_depth3_size_exp
#print axioms PallLean.Paper93.DeepMath.PathB.hypercube_depth3_size_length
