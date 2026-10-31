import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Agreement
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Smolensky
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BeigelTaruiSparsity
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Multilinearisation

/-!
# RS depth-composition headline: quasipoly size *and* bounded error, at once (PROVED)

The probabilistic-polynomial side of the wall.  The exact route (`ACC0MiniBTSize`) collapses ACC⁰[p] to
a single-count `SYM∘AND` but at a size that **towers** over depth.  Beigel–Tarui / Razborov–Smolensky
escapes this by *approximating*: this brick assembles the three already-proved RS depth-recursion
ingredients into one headline — a single oracle `ω` giving an approximant that is simultaneously
**low-degree, quasipoly-sparse, and small-error**, for *every* constant-depth ACC⁰[p] circuit.

  `toAgree_rs_depth_composition` — there exists `ω` such that the RS approximant
  `A := toAgree p t (oracleOf … ω) C` satisfies, all at once:
    * `deg A ≤ ((p−1)·t)^{depth C}`                         (degree recursion, `toAgree_totalDegree_le`)
    * `#{monomial supports of A} ≤ (n+1)^{((p−1)·t)^{depth C}}`   (quasipoly support, BT sparsity)
    * `#{x : A(x) ≠ C(x)} · p^t ≤ #subcircuits(C) · 2^n`    (error union bound, `composed_error_le`).

For `(p−1)·t = polylog` and *constant* depth, this is **degree polylog, support quasipolynomial, error
`≤ #subcircuits·p^{−t}`** — the genuine RS/BT depth-composed approximate `SYM∘AND`, with the size kept
quasipoly *because* it is approximate (unlike the exact tower).

## What is proved (clean axioms, no `sorry`)

* `toAgree_rs_depth_composition` — the combined degree + quasipoly-support + error headline for one `ω`.

## Honest scope

This packages the RS depth recursion: low degree (`toAgree_totalDegree_le`), quasipoly support
(`support_mem_lowDeg` + `beigelTarui_monomial_count_le`), and the depth error union bound
(`composed_error_le`) — *simultaneously*.  It is the **approximate** representation; the remaining open
content (`QuasipolyApproxCompression` / `composite_BT_degree`) is turning this small-error approximant
into the *exact* decision the Williams `#SAT` cash-out consumes.  Single modulus `p` (hypothesis
`hmod`).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RSDepthComposition

open scoped Classical
open MvPolynomial Finset
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.ACC0BeigelTaruiSparsity (beigelTarui_monomial_count_le)
open PallLean.Paper93.DeepMath.PathB.ACC0Multilinearisation (support_mem_lowDeg)

variable {n : ℕ}

/-- **RS depth-composition headline (proved).**  For every constant-depth ACC⁰[p] circuit `C` (single
modulus `p`, hypothesis `hmod`), there is an oracle `ω` whose RS approximant
`A = toAgree p t (oracleOf p t C ω) C` is, *simultaneously*, low-degree, quasipoly-sparse, and
small-error:
`deg A ≤ ((p−1)t)^{depth}`, `#supports(A) ≤ (n+1)^{((p−1)t)^{depth}}`, and
`#errors · p^t ≤ #subcircuits · 2^n`. -/
theorem toAgree_rs_depth_composition (p t : ℕ) [Fact p.Prime] (ht : 1 ≤ t)
    (C : BoolCircuitSyntax n)
    (hmod : ∀ q r cs, (BoolCircuitSyntax.modGate q r cs : BoolCircuitSyntax n) ∈ subcircuits C →
      q = p) :
    ∃ ω : FormSpace p t C,
      (toAgree p t (oracleOf p t C ω) C).totalDegree ≤ ((p - 1) * t) ^ C.depth
      ∧ ((toAgree p t (oracleOf p t C ω) C).support.image (fun d => d.support)).card
          ≤ (n + 1) ^ (((p - 1) * t) ^ C.depth)
      ∧ (Finset.univ.filter (fun x : Fin n → Bool =>
            eval (fun i => boolToZMod p (x i)) (toAgree p t (oracleOf p t C ω) C)
              ≠ boolToZMod p (C.eval x))).card * p ^ t
          ≤ (subcircuits C).toFinset.card * Fintype.card (Fin n → Bool) := by
  obtain ⟨ω, herr⟩ := composed_error_le p t C hmod
  refine ⟨ω, toAgree_totalDegree_le p t ht (oracleOf p t C ω) C, ?_, herr⟩
  refine le_trans (Finset.card_le_card ?_)
    (beigelTarui_monomial_count_le n (((p - 1) * t) ^ C.depth))
  intro S hS
  rw [Finset.mem_image] at hS
  obtain ⟨d, hd, rfl⟩ := hS
  exact support_mem_lowDeg (toAgree p t (oracleOf p t C ω) C)
    (toAgree_totalDegree_le p t ht (oracleOf p t C ω) C) hd

/-!
**RS depth-composition headline proved.**  One oracle yields a degree-`≤ L^D`, support-`≤ (n+1)^{L^D}`,
error-`≤ #subcircuits·p^{−t}` approximant of any constant-depth ACC⁰[p] circuit — the size stays
quasipoly *because* it is approximate (the exact route towers, `ACC0MiniBTSize`).  Turning this
small-error approximant into the exact decision Williams' `#SAT` cash-out needs is the remaining open
content.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0RSDepthComposition

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RSDepthComposition.toAgree_rs_depth_composition
