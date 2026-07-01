import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCubeApproxBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Smolensky

/-!
# Exact → approximate: parity has high *approximate* degree (via the repo's Smolensky engine)

The bridge (`…CubeApproxBridge`) gave the **exact** bound (`G = univ`): no low-degree polynomial agrees with `MOD_q`
*everywhere*.  This file strengthens it to the genuine Razborov–Smolensky statement: no low-degree polynomial agrees with
**parity** on a large *fraction* (`≥ 3/4`) of inputs — the approximate-degree lower bound.

The hard core is already proved in the repo: `Layer3.smolensky_contradiction` (a degree-`≤Δ` polynomial over `ZMod p`
cannot agree with the `±1` parity character `χ_univ = ∏ᵢ pmOne(xᵢ)` on a `≥3/4` set `G` when `16Δ² < 2m+3`).  This file
supplies the missing bridge: every element of the cube approximation space `lowDegSpan Δ` **is** `boolFn` of a degree-`≤Δ`
polynomial, so `LowApproxDeg` agreement with `χ_univ` feeds directly into `smolensky_contradiction`.

  `chiUniv p` — the `±1` parity character as a cube function.
  `boolFn_prod_eq_cubeMonomial`, `boolFn_add`, `boolFn_smul` — `boolFn` is linear and sends monomials to `cubeMonomial`.
  **`lowDegSpan_repr`** — every `g ∈ lowDegSpan Δ` is `boolFn q` for some `q` with `totalDegree ≤ Δ` (span induction).
  **`not_lowApproxDeg_chiUniv`** — over `ZMod p` (`p` odd prime), **no degree-`≤Δ` polynomial agrees with parity on a
        `≥3/4` set `G` when `16Δ² < 2m+3`** — parity's *approximate* degree is `Ω(√m)`.

This is the exact→approximate strengthening for the cube framework: the measure now certifies an *approximate* lower
bound (agreement on a large fraction, not just everywhere), by consuming the repo's proved Smolensky dimension argument.

## Honest scope

`not_lowApproxDeg_chiUniv` is the RS hard side (parity has high approximate degree), the genuine content — discharged via
the repo's `smolensky_contradiction`, not re-derived.  The full `PARITY ∉ AC⁰[p]` also needs the easy side (every
`AC⁰[p]` circuit *has* a degree-`((p-1)t)^depth` approximant on a `≥3/4` set), which the repo carries separately
(`toAgree_totalDegree_le`, `exists_large_agreement_set`, assembled in `parity_function_lower_bound`).  This file is the
approximate hard-side bound in the cube measure's language.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.NFrameACC0 (boolFn)

variable {n : ℕ} {F : Type*} [Field F]

/-- `boolFn` of a squarefree monomial is the cube monomial. -/
theorem boolFn_prod_eq_cubeMonomial (S : Finset (Fin n)) :
    boolFn (∏ i ∈ S, X i : MvPolynomial (Fin n) F) = cubeMonomial S := by
  funext x
  rw [boolFn, map_prod, cubeMonomial]
  exact Finset.prod_congr rfl (fun i _ => by rw [MvPolynomial.eval_X])

theorem boolFn_zero : boolFn (0 : MvPolynomial (Fin n) F) = 0 := by
  funext x; simp [boolFn]

theorem boolFn_add (p q : MvPolynomial (Fin n) F) : boolFn (p + q) = boolFn p + boolFn q := by
  funext x; simp only [boolFn, map_add, Pi.add_apply]

theorem boolFn_smul (c : F) (q : MvPolynomial (Fin n) F) : boolFn (c • q) = c • boolFn q := by
  funext x
  simp only [boolFn, Pi.smul_apply, smul_eq_mul, MvPolynomial.smul_eq_C_mul, map_mul,
    MvPolynomial.eval_C]

/-- **Every low-degree cube function is `boolFn` of a low-degree polynomial (proved)** — the representation lemma bridging
the cube approximation space to `MvPolynomial` degree. -/
theorem lowDegSpan_repr {d : ℕ} {g : (Fin n → Bool) → F} (hg : g ∈ lowDegSpan (F := F) d) :
    ∃ q : MvPolynomial (Fin n) F, q.totalDegree ≤ d ∧ boolFn q = g := by
  induction hg using Submodule.span_induction with
  | mem g hgmem =>
    obtain ⟨S, rfl⟩ := hgmem
    have hcard : S.val.card ≤ d := (Finset.mem_filter.mp S.2).2
    refine ⟨∏ i ∈ S.val, X i, ?_, boolFn_prod_eq_cubeMonomial S.val⟩
    refine le_trans (MvPolynomial.totalDegree_finset_prod _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun i _ => (MvPolynomial.totalDegree_X i).le)) ?_
    rw [Finset.sum_const, smul_eq_mul, mul_one]
    exact hcard
  | zero => exact ⟨0, by simp, boolFn_zero⟩
  | add g1 g2 _ _ ih1 ih2 =>
    obtain ⟨q1, hd1, hb1⟩ := ih1
    obtain ⟨q2, hd2, hb2⟩ := ih2
    exact ⟨q1 + q2, le_trans (MvPolynomial.totalDegree_add _ _) (max_le hd1 hd2),
      by rw [boolFn_add, hb1, hb2]⟩
  | smul c g _ ih =>
    obtain ⟨q, hd, hb⟩ := ih
    exact ⟨c • q, le_trans (MvPolynomial.totalDegree_smul_le _ _) hd, by rw [boolFn_smul, hb]⟩

/-- The `±1` parity character as a cube function: `χ_univ(x) = ∏ᵢ pmOne(xᵢ)`. -/
def chiUniv (p : ℕ) {n : ℕ} : (Fin n → Bool) → ZMod p :=
  fun x => ∏ i, PallLean.Paper93.DeepMath.PathB.Layer3.pmOne p (x i)

/-- **The approximate-degree lower bound for parity (proved)**: over `ZMod p` (`p` odd prime), no degree-`≤Δ` polynomial
agrees with parity on a `≥3/4` set `G` when `16Δ² < 2m+3` — parity has approximate degree `Ω(√m)`.  The exact→approximate
strengthening, discharged via the repo's Smolensky dimension argument. -/
theorem not_lowApproxDeg_chiUniv (p : ℕ) [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0) {m Δ : ℕ}
    (G : Finset (Fin (2 * m + 1) → Bool)) (hwindow : 16 * Δ ^ 2 < 2 * m + 3)
    (hGsize : 3 * 2 ^ (2 * m + 1) ≤ 4 * G.card) :
    ¬ LowApproxDeg (F := ZMod p) Δ G (chiUniv p) := by
  rintro ⟨g, hg, hagree⟩
  obtain ⟨q, hqdeg, hqbool⟩ := lowDegSpan_repr hg
  refine PallLean.Paper93.DeepMath.PathB.Layer3.smolensky_contradiction p hp2 G q hqdeg ?_ hwindow hGsize
  intro x hx
  have h1 : boolFn q x = g x := congrFun hqbool x
  have h2 : chiUniv p x = g x := hagree x hx
  show eval (fun i => PallLean.Paper93.DeepMath.PathB.Layer3.boolToZMod p (x i)) q
      = ∏ i, PallLean.Paper93.DeepMath.PathB.Layer3.pmOne p (x i)
  have hev : eval (fun i => PallLean.Paper93.DeepMath.PathB.Layer3.boolToZMod p (x i)) q
      = boolFn q x := rfl
  rw [hev, h1, ← h2]
  rfl

end PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.lowDegSpan_repr
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.not_lowApproxDeg_chiUniv
