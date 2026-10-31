import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCubeApproxSmolensky
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Agreement

/-!
# The `AC⁰[p]` easy side: every `AC⁰[p]` circuit has a low `LowApproxDeg`

The hard side (`…CubeApproxSmolensky`) proved parity has *high* approximate degree.  This file supplies the matching
**easy side**: every `AC⁰[p]` circuit is *itself* low approximate degree — it agrees with a degree-`((p-1)t)^depth`
polynomial on a `≥3/4` set.  Together they are the two halves of `PARITY ∉ AC⁰[p]`, both now in the cube measure's
language (`LowApproxDeg`).

The quantitative content is the repo's proved probabilistic-degree machinery — `exists_large_agreement_set` (a random
approximant agrees on `≥3/4` of the cube) and `toAgree_totalDegree_le` (its degree is `((p-1)t)^depth`).  This file
bridges it: the approximant `toAgree` is a low-degree polynomial, so `boolFn (toAgree …) ∈ lowDegSpan`, giving
`LowApproxDeg` directly.

  `boolFn_mem_lowDegSpan` — the converse of `lowDegSpan_repr`: `boolFn` of a degree-`≤Δ` polynomial is in `lowDegSpan Δ`
        (via the repo's `boolFn_mem_sqfSpan` + the definitional span equality).
  `cubeCircuitFn p C` — the circuit's value as a cube function `x ↦ boolToZMod(C.eval x)`.
  **`lowApproxDeg_ac0p`** — for an `AC⁰[p]` circuit `C` (mod-gates all mod `p`) with horizon `t` covering its
        subcircuits, there is a `≥3/4` set `G` with `LowApproxDeg ((p-1)t)^{depth C} G (cubeCircuitFn p C)`.

Combined with the hard side: parity's approximate degree is `Ω(√m)` (`not_lowApproxDeg_chiUniv`), while any `AC⁰[p]`
circuit computing it would have approximate degree `((p-1)t)^depth` — small when depth is constant — a contradiction.
That assembly is the repo's `parity_function_lower_bound`; this file places the easy half in the cube framework.

## Honest scope

Both RS halves are now expressed as `LowApproxDeg` statements consuming the repo's proved bounds.  This is `AC⁰[p]`
(single prime `p`), **not** general `ACC⁰[6]` — the composite modulus still needs the `F_2`/`F_3` discharge (the standing
wall).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.NFrameACC0 (boolFn)
open PallLean.Paper93.DeepMath.PathB.Layer3
  (toAgree oracleOf subcircuits boolToZMod exists_large_agreement_set toAgree_totalDegree_le)

variable {n : ℕ}

/-- **The converse of `lowDegSpan_repr` (proved)**: `boolFn` of a degree-`≤Δ` polynomial lies in `lowDegSpan Δ`.  (The
repo's `boolFn_mem_sqfSpan`, transported through the definitional span equality.) -/
theorem boolFn_mem_lowDegSpan {F : Type*} [Field F] {q : MvPolynomial (Fin n) F} {Δ : ℕ}
    (hq : q.totalDegree ≤ Δ) : boolFn q ∈ lowDegSpan (F := F) Δ := by
  rw [lowDegSpan_eq_sqfSpan]
  exact NFrameACC0.boolFn_mem_sqfSpan q hq

/-- The circuit's value as a cube function over `ZMod p`. -/
def cubeCircuitFn (p : ℕ) (C : BoolCircuitSyntax n) : (Fin n → Bool) → ZMod p :=
  fun x => boolToZMod p (C.eval x)

open Classical in
/-- **The `AC⁰[p]` easy side (proved)**: an `AC⁰[p]` circuit (mod-gates all mod `p`) whose horizon `t` covers its
subcircuits has a `≥3/4` agreement set `G` on which it equals a degree-`((p-1)t)^{depth C}` polynomial — i.e.
`LowApproxDeg` is small.  The repo's probabilistic-degree bound, in the cube measure's language. -/
theorem lowApproxDeg_ac0p (p t : ℕ) [Fact p.Prime] (C : BoolCircuitSyntax n) (ht1 : 1 ≤ t)
    (hmod : ∀ q r cs,
      (BoolCircuitSyntax.modGate q r cs : BoolCircuitSyntax n) ∈ subcircuits C → q = p)
    (ht : 4 * (subcircuits C).toFinset.card ≤ p ^ t) :
    ∃ G : Finset (Fin n → Bool), 3 * 2 ^ n ≤ 4 * G.card ∧
      LowApproxDeg (F := ZMod p) (((p - 1) * t) ^ C.depth) G (cubeCircuitFn p C) := by
  obtain ⟨ω, hω⟩ := exists_large_agreement_set p t C hmod ht
  refine ⟨Finset.univ.filter (fun x : Fin n → Bool =>
        eval (fun i => boolToZMod p (x i)) (toAgree p t (oracleOf p t C ω) C)
          = boolToZMod p (C.eval x)),
    hω, boolFn (toAgree p t (oracleOf p t C ω) C), ?_, ?_⟩
  · exact boolFn_mem_lowDegSpan (toAgree_totalDegree_le p t ht1 _ C)
  · intro x hx
    have hxmem := (Finset.mem_filter.mp hx).2
    show cubeCircuitFn p C x
        = eval (fun i => boolToZMod p (x i)) (toAgree p t (oracleOf p t C ω) C)
    rw [cubeCircuitFn]
    exact hxmem.symm

end PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.boolFn_mem_lowDegSpan
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.lowApproxDeg_ac0p
