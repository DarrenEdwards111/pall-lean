import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCubeApproxDegree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMODqHigh

/-!
# Bridge: the cube approximation measure ⟷ the repo's `NFrameComplexity` / `MOD_q` bound

`…CubeApproxDegree` built the bounded low-degree measure and proved hard functions exist by counting.  This file wires it
to the repo's *proved* Razborov–Smolensky number: the cube approximation space `lowDegSpan d` is **definitionally** the
repo's `span (sqfGens F n d)` (same subsets, same monomials `∏[xᵢ]`), so `MOD_q`'s N-Frame lower bound transfers directly
into a statement about `LowApproxDeg`.

  `cubeMonomial_eq_sqfEval`, `lowDegSpan_eq_sqfSpan` — the two measures coincide (`cubeMonomial = sqfEval`,
        `lowDegSubsets = lowDegMonomials`).
  `nframeComplexity_le_of_mem_lowDegSpan` / `not_mem_lowDegSpan_of_nframeComplexity_gt` — the `sInf` bridge.
  `lowApproxDeg_univ_iff_mem` — exact agreement (`G = univ`) `⟺` membership in `lowDegSpan`.
  **`not_lowApproxDeg_omegaFn`** — the payoff: over a field with an order-`q` root `ω`, `MOD_q` (`omegaFn`) has **no
        degree-`< ⌈n/2⌉` polynomial agreeing with it everywhere** — the repo's `nframeComplexity_omegaFn_univ_ge`
        (`≥ n − n/2`) transported into the cube approximation framework.

## Honest scope — this is the EXACT (`G = univ`) bound, not yet the approximate one

`not_lowApproxDeg_omegaFn` uses `G = univ`: it rules out a low-degree polynomial agreeing with `MOD_q` on **all** inputs.
That is the exact `AC⁰`-level low-degree bound (the `Ω(√n)`-vs-here-`⌈n/2⌉` degree wall), transported cleanly.  The
`ACC⁰[p]` separation needs the **approximate** version — no low-degree polynomial agreeing on a `(1−ε)` *fraction*
(`|G| ≥ (1−ε)2ⁿ`) — which requires the repo's probabilistic-degree easy side and the `Ω(√n)` *approximate*-degree hard
side.  Those quantitative bounds are the standing RS work; this bridge makes the framework consume them.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

open PallLean.Paper93.DeepMath.PathB.NFrameACC0 (NFrameComplexity)
open PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact (sqfGens)
open PallLean.Paper93.DeepMath.PathB.Layer4 (sqfEval)
open PallLean.Paper93.DeepMath.PathB.ModQReduction (omegaFn)

variable {n : ℕ} {F : Type*} [Field F]

/-- The cube monomial is exactly the repo's squarefree evaluation. -/
theorem cubeMonomial_eq_sqfEval (S : Finset (Fin n)) :
    cubeMonomial (F := F) S = sqfEval F S := rfl

/-- **The two measures coincide (proved)**: the cube approximation space is the repo's degree-`≤ d` squarefree span. -/
theorem lowDegSpan_eq_sqfSpan (d : ℕ) :
    lowDegSpan (F := F) (n := n) d = Submodule.span F (sqfGens F n d) := rfl

/-- Membership in `lowDegSpan d` bounds the repo's N-Frame complexity. -/
theorem nframeComplexity_le_of_mem_lowDegSpan {f : (Fin n → Bool) → F} {d : ℕ}
    (h : f ∈ lowDegSpan (F := F) d) : NFrameComplexity F f ≤ d := by
  apply Nat.sInf_le
  rw [Set.mem_setOf_eq, ← lowDegSpan_eq_sqfSpan]
  exact h

/-- High N-Frame complexity ⟹ outside the low-degree space. -/
theorem not_mem_lowDegSpan_of_nframeComplexity_gt {f : (Fin n → Bool) → F} {d : ℕ}
    (h : d < NFrameComplexity F f) : f ∉ lowDegSpan (F := F) d :=
  fun hmem => absurd (nframeComplexity_le_of_mem_lowDegSpan hmem) (not_le.mpr h)

/-- Exact agreement on all inputs `⟺` membership in `lowDegSpan`. -/
theorem lowApproxDeg_univ_iff_mem {d : ℕ} {f : (Fin n → Bool) → F} :
    LowApproxDeg (F := F) d Finset.univ f ↔ f ∈ lowDegSpan (F := F) d := by
  constructor
  · rintro ⟨g, hg, hagree⟩
    have hfg : f = g := funext (fun x => hagree x (Finset.mem_univ x))
    rw [hfg]; exact hg
  · intro hf; exact ⟨f, hf, fun x _ => rfl⟩

/-- **The payoff (proved)**: over a field with an order-`q` root `ω` (`q ≥ 2`), `MOD_q` has **no degree-`< ⌈n/2⌉`
polynomial agreeing with it on every input** — the repo's `nframeComplexity_omegaFn_univ_ge` transported into the cube
approximation framework. -/
theorem not_lowApproxDeg_omegaFn [Fintype F] [DecidableEq F] {q : ℕ} (ω : F)
    (hω : orderOf ω = q) (hq2 : 2 ≤ q) {d : ℕ} (hd : d < n - n / 2) :
    ¬ LowApproxDeg (F := F) d Finset.univ (omegaFn ω (Finset.univ : Finset (Fin n))) := by
  rw [lowApproxDeg_univ_iff_mem]
  exact not_mem_lowDegSpan_of_nframeComplexity_gt
    (lt_of_lt_of_le hd (NFrameACC0.nframeComplexity_omegaFn_univ_ge ω hω hq2))

end PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.lowDegSpan_eq_sqfSpan
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.not_lowApproxDeg_omegaFn
