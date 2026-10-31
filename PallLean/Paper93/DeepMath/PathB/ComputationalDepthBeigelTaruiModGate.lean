import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRazborovSmolenskyPoly
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBeigelTaruiBase

/-!
# Beigel–Tarui, rung 13: `MOD_p` gates — the ACC⁰-specific gate, arithmetised via Fermat

`ACC⁰` is `AND`/`OR`/`NOT`/`MOD_m`.  Rungs 1–12 handled the `AND`/`OR`/`NOT` part (reducing formulas to `SYM∘AND`); this
file adds the **`MOD_p` gate** (modulus = the field characteristic), the one whose arithmetisation is *exact and
low-degree* over `F_p`.  By Fermat (rung 2's `fermatInd`), the subset-sum raised to the `(p-1)` is the nonzero-indicator
mod `p` — so a `MOD_p` gate is the degree-`(p-1)` polynomial `(∑_{i∈S} Xᵢ)^{p-1}`, exactly.

  `modGateP` — the `MOD_p` gate over subset `S` as a polynomial: `(∑_{i∈S} Xᵢ)^{p-1}`.
  `modGate_arith` — **PROVED, exact arithmetisation**: over `F_p`, `modGateP` evaluates to the `MOD_p` gate — `1` iff the
        number of set bits in `S` is nonzero mod `p`, `0` otherwise.
  `modGateP_totalDegree_le` — **PROVED**: the gate polynomial has degree `≤ p-1`.

So a `MOD_p` gate is a single degree-`(p-1)` polynomial, which the `SYM∘AND` fold (rungs 9–12) then turns into a
`SYM∘AND` — extending the reduction to `ACC⁰[p]` gates.

## Honest scope

This arithmetises the `MOD_p` gate (modulus equal to the field characteristic `p`) exactly and at degree `p-1`, via
Fermat — the ACC⁰-specific gate the `AND`/`OR`/`NOT` polynomial method alone cannot cheaply express.  What remains: (i)
**composite `MOD_m`** with `m ≠ p` — the genuinely hard case (no single field makes every modulus of a multi-prime
circuit low-degree; this is the `MOD_6`/`ACC⁰[6]` two-fields wall the earlier arc proved as a *barrier*, so `MOD_m` needs
Toda's `ℤ`-lifting / the composite route, not this Fermat trick); and (ii) folding `MOD_p` gates into the formula type
(`BForm` has no `MOD` constructor) to reduce full `ACC⁰[p]` circuits.  This file supplies the exact low-degree `MOD_p`
gate, reusing rung 2's `fermatInd`.  Nothing here is the Beigel–Tarui reduction, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase (embed)
open scoped Classical

variable {p n : ℕ} [Fact p.Prime]

/-- The `MOD_p` gate over subset `S` as a polynomial: `(∑_{i∈S} Xᵢ)^{p-1}`. -/
noncomputable def modGateP (S : Finset (Fin n)) : MvPolynomial (Fin n) (ZMod p) := (∑ i ∈ S, X i) ^ (p - 1)

/-- **Exact arithmetisation of `MOD_p` (proved)**: over `F_p`, `modGateP S` evaluates to `1` iff the number of set bits
in `S` is nonzero mod `p`, and `0` otherwise — the `MOD_p` gate, via Fermat. -/
theorem modGate_arith (S : Finset (Fin n)) (x : Fin n → Bool) :
    (eval (fun i => embed (x i))) (modGateP (p := p) S)
      = embed (decide ((∑ i ∈ S, (embed (x i) : ZMod p)) ≠ 0)) := by
  rw [modGateP, map_pow, map_sum]
  simp only [eval_X]
  rw [fermatInd]
  by_cases h : (∑ i ∈ S, (embed (x i) : ZMod p)) = 0 <;> simp_all [embed]

/-- **The `MOD_p` gate has degree `≤ p-1` (proved)**. -/
theorem modGateP_totalDegree_le (S : Finset (Fin n)) : (modGateP (p := p) S).totalDegree ≤ p - 1 := by
  refine le_trans (totalDegree_pow _ _) ?_
  have h1 : (∑ i ∈ S, (X i : MvPolynomial (Fin n) (ZMod p))).totalDegree ≤ 1 :=
    le_trans (totalDegree_finset_sum S _) (Finset.sup_le (fun i _ => (totalDegree_X i).le))
  calc (p - 1) * _ ≤ (p - 1) * 1 := Nat.mul_le_mul_left _ h1
    _ = p - 1 := Nat.mul_one _

end PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.modGate_arith
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.modGateP_totalDegree_le
