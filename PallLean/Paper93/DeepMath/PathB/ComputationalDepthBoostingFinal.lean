import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBoostSurjection
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRSCapstone
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMonomialAlgebra
import Mathlib

/-!
# The boosting surjection, completed (PROVED) — `|G| < 2ⁿ` from a degree-`d` approximator

This finishes the boosting argument: it discharges the surjection hypothesis of
`RazborovSmolensky.dimension_argument` and derives the dimension bound directly.

  `collectCoef_support` — **the support bound**: if the approximator `aCoef` has degree `≤ d`, then the collected
        coefficient vector `collectCoef aCoef c` is supported on `|T| ≤ n/2 + d` (low monomials stay `≤ n/2`; high
        ones, folded to `aCoef`-coefficients shifted by `Sᶜ`, have degree `≤ d + |Sᶜ| ≤ d + n/2`).
  `boosting_surjection` — **the boosting lower bound**: if a degree-`d` Walsh polynomial `evalW aCoef` agrees
        with the full parity `walshFn univ` on a set `G ⊆ {-1,+1}ⁿ` and `n/2 + d < n`, then `|G| < 2ⁿ`.

`boosting_surjection` builds the surjection `φ` from the degree-`≤ n/2+d` coefficient space onto `G → 𝔽`
(extend a target via the Walsh span, fold to degree `≤ n/2+d` via `collectCoef`, which agrees on `G` by
`evalW_collectCoef_on_G` and is supported by `collectCoef_support`), then applies `dimension_argument`.  This is
exactly the contradiction Razborov–Smolensky drives: a low-degree approximator on a large `G` is impossible.
-/

open scoped symmDiff

namespace PallLean.Paper93.DeepMath.PathB.WalshSpan

variable {n : ℕ} {F : Type*} [Field F]

/-- **The support bound.**  With `aCoef` of degree `≤ d`, `collectCoef aCoef c` vanishes above degree `n/2 + d`:
low monomials contribute only at their own index (`≤ n/2`), and high ones contribute `aCoef (T ∆ Sᶜ)`, which is
zero once `|T ∆ Sᶜ| > d` — guaranteed when `|T| > n/2 + d` since `|T| ≤ |T∆Sᶜ| + |Sᶜ|` and `|Sᶜ| < n/2`. -/
theorem collectCoef_support {d : ℕ} (aCoef c : Finset (Fin n) → F)
    (hd : ∀ R, d < R.card → aCoef R = 0) (T : Finset (Fin n)) (hT : n / 2 + d < T.card) :
    collectCoef aCoef c T = 0 := by
  rw [collectCoef, Finset.sum_apply]
  refine Finset.sum_eq_zero (fun S _ => ?_)
  rw [Pi.smul_apply, smul_eq_mul]
  by_cases h : 2 * S.card ≤ n
  · rw [if_pos h, Pi.single_apply, if_neg (by intro e; subst e; omega), mul_zero]
  · rw [if_neg h]
    have h1 : T.card ≤ (T ∆ Sᶜ).card + Sᶜ.card := by
      calc T.card = ((T ∆ Sᶜ) ∆ Sᶜ).card := by rw [symmDiff_symmDiff_cancel_right]
        _ ≤ (T ∆ Sᶜ).card + Sᶜ.card := Boosting.card_symmDiff_le _ _
    have h2 : Sᶜ.card = n - S.card := by rw [Finset.card_compl, Fintype.card_fin]
    rw [hd (T ∆ Sᶜ) (by omega), mul_zero]

/-- **The boosting lower bound.**  If a degree-`d` Walsh polynomial `evalW aCoef` agrees with the full parity on
`G ⊆ {-1,+1}ⁿ`, and `n/2 + d < n`, then `|G| < 2ⁿ`.  Proof: every function on `G` is realised by a degree-`≤ n/2+d`
Walsh polynomial (`collectCoef` of its Walsh-span extension, which agrees on `G` and is supported), giving a
surjection from the degree-`≤ n/2+d` coefficient space onto `G → 𝔽`; `dimension_argument` then bounds `|G|`. -/
theorem boosting_surjection [Fintype F] [DecidableEq F] {d : ℕ} (h2 : (2 : F) ≠ 0)
    (aCoef : Finset (Fin n) → F) (hd : ∀ R, d < R.card → aCoef R = 0)
    (G : Finset (Fin n → Bool)) (hG : ∀ b ∈ G, evalW aCoef b = walshFn Finset.univ b)
    (hmn : n / 2 + d < n) :
    G.card < 2 ^ n := by
  have hkey : Fintype.card {b : Fin n → Bool // b ∈ G} < 2 ^ n := by
    refine RazborovSmolensky.dimension_argument (F := F) hmn (Fintype.one_lt_card (α := F))
      (φ := fun dCoef b =>
        evalW (fun T => if h : T.card ≤ n / 2 + d then dCoef ⟨T, h⟩ else 0) b.1) ?_
    intro g
    obtain ⟨c, hc⟩ := evalW_surjective h2 (fun b => if hb : b ∈ G then g ⟨b, hb⟩ else 0)
    refine ⟨fun Tsub => collectCoef aCoef c Tsub.1, ?_⟩
    funext b
    have hext :
        (fun T => if _h : T.card ≤ n / 2 + d then collectCoef aCoef c T else (0 : F))
          = collectCoef aCoef c := by
      funext T
      by_cases hTm : T.card ≤ n / 2 + d
      · rw [dif_pos hTm]
      · rw [dif_neg hTm]
        exact (collectCoef_support aCoef c hd T (by omega)).symm
    show evalW (fun T => if _h : T.card ≤ n / 2 + d then collectCoef aCoef c T else 0) b.1 = g b
    rw [hext, evalW_collectCoef_on_G aCoef c b.1 (hG b.1 b.2), hc]
    show (if hb : b.1 ∈ G then g ⟨b.1, hb⟩ else (0 : F)) = g b
    rw [dif_pos b.2]
  rwa [Fintype.card_coe] at hkey

/-- **The boosting surjection (factored out).**  The degree-`≤ n/2+d` coefficient space surjects onto the functions
`{b ∈ G} → 𝔽`: extend an arbitrary `g` to all of `{−1,+1}ⁿ` (`evalW_surjective`), then `collectCoef` it against the
parity-approximator `aCoef` to a degree-`≤ n/2+d` vector that still agrees on `G`.  The surjectivity content shared
by `boosting_surjection` and its sharp form. -/
theorem boosting_surjective [Fintype F] [DecidableEq F] {d : ℕ} (h2 : (2 : F) ≠ 0)
    (aCoef : Finset (Fin n) → F) (hd : ∀ R, d < R.card → aCoef R = 0)
    (G : Finset (Fin n → Bool)) (hG : ∀ b ∈ G, evalW aCoef b = walshFn Finset.univ b) :
    Function.Surjective
      (fun (dCoef : {S : Finset (Fin n) // S.card ≤ n / 2 + d} → F) (b : {b : Fin n → Bool // b ∈ G}) =>
        evalW (fun T => if h : T.card ≤ n / 2 + d then dCoef ⟨T, h⟩ else 0) b.1) := by
  intro g
  obtain ⟨c, hc⟩ := evalW_surjective h2 (fun b => if hb : b ∈ G then g ⟨b, hb⟩ else 0)
  refine ⟨fun Tsub => collectCoef aCoef c Tsub.1, ?_⟩
  funext b
  have hext :
      (fun T => if _h : T.card ≤ n / 2 + d then collectCoef aCoef c T else (0 : F))
        = collectCoef aCoef c := by
    funext T
    by_cases hTm : T.card ≤ n / 2 + d
    · rw [dif_pos hTm]
    · rw [dif_neg hTm]
      exact (collectCoef_support aCoef c hd T (by omega)).symm
  show evalW (fun T => if _h : T.card ≤ n / 2 + d then collectCoef aCoef c T else 0) b.1 = g b
  rw [hext, evalW_collectCoef_on_G aCoef c b.1 (hG b.1 b.2), hc]
  show (if hb : b.1 ∈ G then g ⟨b.1, hb⟩ else (0 : F)) = g b
  rw [dif_pos b.2]

/-- **The sharp boosting lower bound.**  If a degree-`d` Walsh polynomial agrees with the full parity on
`G ⊆ {−1,+1}ⁿ`, then `|G| ≤ Σ_{i ≤ n/2+d} C(n,i)` — the *exact* dimension bound, sharper than
`boosting_surjection`'s `< 2ⁿ`.  (`< 2ⁿ` follows when `n/2+d < n` via `sum_choose_lt`.)  This is the quantitative
strengthening the non-vacuous circuit lower bound needs. -/
theorem boosting_surjection_sharp [Fintype F] [DecidableEq F] {d : ℕ} (h2 : (2 : F) ≠ 0)
    (aCoef : Finset (Fin n) → F) (hd : ∀ R, d < R.card → aCoef R = 0)
    (G : Finset (Fin n → Bool)) (hG : ∀ b ∈ G, evalW aCoef b = walshFn Finset.univ b) :
    G.card ≤ ∑ i ∈ Finset.range (n / 2 + d + 1), n.choose i := by
  have h := RazborovSmolensky.dimension_argument_sharp (F := F) (Fintype.one_lt_card (α := F))
    _ (boosting_surjective h2 aCoef hd G hG)
  rwa [Fintype.card_coe] at h

end PallLean.Paper93.DeepMath.PathB.WalshSpan

#print axioms PallLean.Paper93.DeepMath.PathB.WalshSpan.collectCoef_support
#print axioms PallLean.Paper93.DeepMath.PathB.WalshSpan.boosting_surjection
#print axioms PallLean.Paper93.DeepMath.PathB.WalshSpan.boosting_surjection_sharp
