import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverNeciporukCalibration

/-!
# A structured decomposition class where the min IS provably super-logarithmic

The decomposition gap (`equality_decomposition_gap`) showed the `min` over decompositions can *collapse*
(EQUALITY: one cut needs `n`, another needs `1`).  The open frontier is whether the `min` is large for a
*hard* family over *all* decompositions.  This file attacks that in a **structured restricted class** and
the attack *pans out*: for the address-block continuation decompositions of the multiplexer `hardF`, the
minimum boundary is provably **super-logarithmic**.

## The class and the result

The multiplexer `hardF` lays out its `m` address blocks `blockS 0, …, blockS (m-1)`.  Each gives a
continuation decomposition (read that block, the rest is the suffix).  This is a structured class of `m`
decompositions.  The result:

* `hardF_minBlockBoundary_ge` — **every** block in this class forces boundary `≥ 2^b − 1`, so the *minimum*
  over the whole class is `≥ 2^b − 1`.  (Unlike a single cut, no decomposition in this class is cheap.)
* `minBlockBoundary_superlog` — and `2^b − 1` is genuinely **super-logarithmic**: for every constant `c`
  there is a family member where the min block boundary exceeds `c · log₂(input size)`.

So the `min`-over-decompositions, which *collapses* for EQUALITY over arbitrary cuts, is forced
**super-logarithmic** for `hardF` over the address-block class.  This is the gap-quantifier proved for a
structured class beyond proof-space — a genuine (if restricted) instance of the open inequality.

## Honest scope — why this is not P vs NP

The address-block class is **structured and restricted**: it is the `m` natural blocks of the `hardF`
layout, not *every* admissible decomposition.  A general decider could choose a decomposition outside this
class (e.g. one cutting across blocks), and nothing here rules that out — exactly the freedom
`equality_decomposition_gap` exploits.  So this is the min over a *chosen* structured class, super-log; the
min over *all* decompositions for a hard family stays open (`= CookLevinFrontierHyp`).  The contribution is a
second regime (after resolution proof-space) where the hard quantifier is genuinely proved, and where the
bound is super-logarithmic rather than collapsing.
-/

namespace PallLean.Paper93.DeepMath.PathB.BlockDecompositionMin

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.NecHard
open PallLean.Paper93.DeepMath.PathB.ObserverNeciporuk
open scoped BigOperators

variable {b m : ℕ}

/-- **The minimum boundary over the address-block decomposition class** (`m ≥ 1`): the least, over the `m`
address blocks, of the formula observer's block boundary. -/
noncomputable def minBlockBoundary (hm : 0 < m) (F : BFormula (nn b m)) : ℕ :=
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  (Finset.univ : Finset (Fin m)).inf' Finset.univ_nonempty
    (fun k => formulaBlockBoundary (blockS k) F)

/-- **Every address-block decomposition forces boundary `≥ 2^b − 1` — so the min does too.**  No
decomposition in this structured class is cheap (contrast the single-cut EQUALITY collapse). -/
theorem hardF_minBlockBoundary_ge (hm : 0 < m) (F : BFormula (nn b m))
    (hF : ∀ x, BFormula.eval F x = hardF x) :
    Dsize b - 1 ≤ minBlockBoundary hm F := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  unfold minBlockBoundary
  apply Finset.le_inf'
  intro k _
  exact hardF_blockBoundary_ge k F hF

/-- `b + 1 ≤ 2^b`. -/
private theorem succ_le_two_pow : ∀ k : ℕ, k + 1 ≤ 2 ^ k
  | 0 => by norm_num
  | (k + 1) => by
      have ih := succ_le_two_pow k
      have hp : 0 < 2 ^ k := pow_pos (by norm_num) k
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
      omega

/-- **The min block boundary is super-logarithmic.**  For every constant `c`, some balanced family member
(`m = 2^b`) has min block boundary `2^b − 1 > c · log₂(input size)`.  So the `min` over the address-block
class is not merely positive but grows faster than any logarithm of the input — genuinely super-logarithmic,
the regime a separation needs (here in a structured class). -/
theorem minBlockBoundary_superlog (c : ℕ) :
    ∃ b : ℕ, 5 ≤ b ∧ c * Nat.log 2 (nn b (2 ^ b)) < Dsize b - 1 := by
  obtain ⟨b, hb5, hbig⟩ := expBeatsQuad (2 * c + 1)
  refine ⟨b, hb5, ?_⟩
  have hdb : Dsize b = 2 ^ b := dsize_eq
  have hN : nn b (2 ^ b) = 2 ^ b * (b + 1) := by unfold nn; rw [hdb]; ring
  have hb1 : b + 1 ≤ 2 ^ b := succ_le_two_pow b
  have hnnle : nn b (2 ^ b) ≤ 2 ^ (2 * b) := by
    rw [hN, two_mul, pow_add]; exact Nat.mul_le_mul_left _ hb1
  have hlog : Nat.log 2 (nn b (2 ^ b)) ≤ 2 * b := by
    calc Nat.log 2 (nn b (2 ^ b)) ≤ Nat.log 2 (2 ^ (2 * b)) := Nat.log_mono_right hnnle
      _ = 2 * b := Nat.log_pow (by norm_num) _
  have hbb : b ≤ b ^ 2 := by
    calc b = b ^ 1 := (pow_one b).symm
      _ ≤ b ^ 2 := Nat.pow_le_pow_right (by omega) (by omega)
  have h2b2 : 2 ≤ b ^ 2 := le_trans (by omega) hbb
  have h1 : 2 * c * b ≤ 2 * c * b ^ 2 := mul_le_mul_left' hbb (2 * c)
  have hquad : 2 * c * b + 2 ≤ (2 * c + 1) * b ^ 2 := by
    calc 2 * c * b + 2 ≤ 2 * c * b ^ 2 + b ^ 2 := Nat.add_le_add h1 h2b2
      _ = (2 * c + 1) * b ^ 2 := by ring
  have hmul : c * Nat.log 2 (nn b (2 ^ b)) ≤ 2 * c * b := by
    calc c * Nat.log 2 (nn b (2 ^ b)) ≤ c * (2 * b) := Nat.mul_le_mul_left _ hlog
      _ = 2 * c * b := by ring
  have hfin : c * Nat.log 2 (nn b (2 ^ b)) + 2 < 2 ^ b :=
    lt_of_le_of_lt (le_trans (Nat.add_le_add_right hmul 2) hquad) hbig
  rw [hdb]; omega

end PallLean.Paper93.DeepMath.PathB.BlockDecompositionMin

#print axioms PallLean.Paper93.DeepMath.PathB.BlockDecompositionMin.hardF_minBlockBoundary_ge
#print axioms PallLean.Paper93.DeepMath.PathB.BlockDecompositionMin.minBlockBoundary_superlog
