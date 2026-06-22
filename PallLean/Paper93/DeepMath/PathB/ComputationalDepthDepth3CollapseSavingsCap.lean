import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseInterface

/-!
# Depth-3 collapse — the savings cap: why the gate is AC⁰-ceilinged (PROVED)

Attacking `Depth3CollapseModel.collapse` (THE OPEN GATE).  The gate factors through a switching
**kernel** (`collapseModel_of_dtRefKernel`); the kernel is concretely built (`tautDNF_to_dtRef`), and
its depth-smallness *is* the switching lemma (built unconditionally for AC⁰ via the witness route).
The conditional bridge `size_lower_exp` already gives, in the BSW regime, `2^j ≤ collapseLen (size D)`
for any refuting object `D`.

This brick states the **precise wall**: the collapse route's resolution-width savings `j` is
*logarithmically capped* by the collapse length —

  `collapse_savings_le_log` — `j ≤ log₂ (collapseLen (size D))`.

So if `collapseLen` is polynomial (`collapseLen (size D) ≤ size D^O(1)`), the savings is only
`j = O(log size)` — width savings `O(log)`, i.e. quasi-polynomial / AC⁰-ceilinged, **never** the linear
`j = Ω(c·t)` a super-polynomial general-circuit (P≠NP) bound would need.  Equivalently: a refuting
object forces `collapseLen (size D) ≥ 2^j`, so any class with *poly-size* refuters (general circuits
refute Tseitin in poly size) must have **super-polynomial** `collapseLen` — the gate cannot be
discharged with poly `collapseLen` for general circuits.  That is exactly why the route tops out at
AC⁰ and the general case is P≠NP-strength.

## What is proved (clean axioms, no `sorry`)

* `collapse_savings_le_log` — `j ≤ log₂ (collapseLen (size D))` in the BSW regime.
* `collapseLen_ge_two_pow` — equivalently `2^j ≤ collapseLen (size D)` (the cap, restated).

## Honest scope

The precise AC⁰-ceiling of the collapse route: poly `collapseLen` ⇒ only `O(log)` width savings.  The
AC⁰ kernel + switching are built; the general-circuit gate (poly `collapseLen` for general circuits) is
BSW-forbidden / P≠NP-strength and is **not** faked.  `Depth3CollapseModel.collapse` for general circuits
and P≠NP remain untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3CollapseModel

open PallLean.Paper93.DeepMath.PathB.TseitinResolution

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]
  [Nonempty Edge] {G : TseitinGraph V Edge} {charge : V → ZMod 2}

/-- **The collapse length is at least `2^j`** (restating `size_lower_exp`). -/
theorem collapseLen_ge_two_pow (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TConstr G charge v a)
    (M : Depth3CollapseModel G charge)
    {c t : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht2 : 2 ≤ t)
    (hcard : 4 * t ≤ Fintype.card V) {d k j : ℕ} (hd : 0 < d) (hk1 : 1 ≤ k)
    (hdn : d < Fintype.card (TLit Edge)) (hkd : Fintype.card (TLit Edge) - d ≤ k * d)
    (hsmall : M.w₀ + d + k * j < c * t)
    (D : M.Circuit) (hD : M.Refutes D) :
    2 ^ j ≤ M.collapseLen (M.size D) :=
  size_lower_exp hunsat M hc hexp ht2 hcard hd hk1 hdn hkd hsmall D hD

/-- **The savings cap.**  In the BSW regime, the collapse route's resolution-width savings `j` is at
most `log₂` of the collapse length.  Polynomial `collapseLen` therefore caps `j` at `O(log size)` —
the AC⁰ ceiling; a super-polynomial (P≠NP) bound would need linear `j`, which the gate cannot supply
with poly `collapseLen`. -/
theorem collapse_savings_le_log (hunsat : ∀ a : Edge → ZMod 2, ∃ v, ¬ TConstr G charge v a)
    (M : Depth3CollapseModel G charge)
    {c t : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht2 : 2 ≤ t)
    (hcard : 4 * t ≤ Fintype.card V) {d k j : ℕ} (hd : 0 < d) (hk1 : 1 ≤ k)
    (hdn : d < Fintype.card (TLit Edge)) (hkd : Fintype.card (TLit Edge) - d ≤ k * d)
    (hsmall : M.w₀ + d + k * j < c * t)
    (D : M.Circuit) (hD : M.Refutes D) :
    j ≤ Nat.log 2 (M.collapseLen (M.size D)) := by
  have h := collapseLen_ge_two_pow hunsat M hc hexp ht2 hcard hd hk1 hdn hkd hsmall D hD
  have hpos : 0 < M.collapseLen (M.size D) := lt_of_lt_of_le (pow_pos (by norm_num) j) h
  exact (Nat.le_log_iff_pow_le (by norm_num) hpos.ne').mpr h

/-!
**Collapse savings cap proved.**  `j ≤ log₂ (collapseLen (size D))` — poly `collapseLen` ⇒ `O(log)`
savings ⇒ AC⁰ ceiling.  The general-circuit gate (poly `collapseLen` for general circuits, which refute
Tseitin in poly size) is BSW-forbidden / P≠NP-strength; not faked.  Collapse for general circuits and
P≠NP untouched.
-/

end Depth3CollapseModel

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3CollapseModel.collapse_savings_le_log
