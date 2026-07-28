import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-!
# Discharging the parameter gap in the Smolensky reduction

`RSSmolenskyCounting.smolensky_from_spreading` still took two open inputs: the MOD_q-specific
`spreading` lemma, and a parameter gap `hparam : card {T : |T| ≤ D} < 2^n − e`.  The gap is a pure
binomial fact and is *not* open — this file discharges it, leaving only `spreading`.

The bound: for `2D < n`, `∑_{i≤D} C(n,i) ≤ 2^{n-1}`.  Proof by complementation — the low sets `{|T| ≤ D}`
and the high sets `{|T| ≥ n − D}` are disjoint (since `D < n − D`) and equinumerous (complement is a
bijection), so together they inject into all `2^n` subsets: `2 · |{|T| ≤ D}| ≤ 2^n`.

## What is proved

* **`two_card_lowdeg_le`** — `2 · |{T : |T| ≤ D}| ≤ 2^n` for `2D < n`.
* **`param_gap`** — hence `card {T : |T| ≤ D} < 2^n − e` whenever `2D < n` and `2e < 2^n` (approximation
  on more than half the inputs at degree `≤ n/2`): exactly the `hparam` of the Smolensky reduction.

## Honest scope

A clean combinatorial discharge of one of the two counting-side inputs — the parameter gap was never the
hard part.  With `param_gap` and `RSSmolenskyCounting.counting` both proved, the entire counting half of
Smolensky is closed; the sole remaining open piece is `spreading` (the `q`-th-roots change of variables).
`AC⁰[p]`-restricted; nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RSParamGap

variable {n D e : ℕ}

/-- **The binomial-half bound (proved).**  For `2D < n`, `2 · |{T : |T| ≤ D}| ≤ 2^n`.  Complementation
sends the low sets to the disjoint high sets, and both inject into all `2^n` subsets. -/
theorem two_card_lowdeg_le (n D : ℕ) (hD : 2 * D < n) :
    2 * (Finset.univ.filter (fun T : Finset (Fin n) => T.card ≤ D)).card ≤ 2 ^ n := by
  classical
  set L := Finset.univ.filter (fun T : Finset (Fin n) => T.card ≤ D) with hLdef
  have hinj : Function.Injective (fun s : Finset (Fin n) => sᶜ) := fun a b h => by simpa using h
  set U := L.image (fun s : Finset (Fin n) => sᶜ) with hUdef
  have hLU : U.card = L.card := Finset.card_image_of_injective L hinj
  have hdisj : Disjoint L U := by
    rw [Finset.disjoint_left]
    intro a haL haU
    simp only [hLdef, Finset.mem_filter, Finset.mem_univ, true_and] at haL
    simp only [hUdef, Finset.mem_image, hLdef, Finset.mem_filter, Finset.mem_univ, true_and] at haU
    obtain ⟨T, hT, rfl⟩ := haU
    simp only [Finset.card_compl, Fintype.card_fin] at haL
    have hTn : T.card ≤ n := by
      have := Finset.card_le_univ T
      rwa [Fintype.card_fin] at this
    omega
  have hunion : (L ∪ U).card = L.card + U.card := Finset.card_union_of_disjoint hdisj
  have hle : (L ∪ U).card ≤ 2 ^ n := by
    have h1 : (L ∪ U).card ≤ Fintype.card (Finset (Fin n)) := by
      rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
    rwa [Fintype.card_finset, Fintype.card_fin] at h1
  rw [hunion, hLU] at hle
  omega

/-- **The parameter gap (proved).**  For `2D < n` and `2e < 2^n`, `card {T : |T| ≤ D} < 2^n − e` — the
`hparam` hypothesis of the Smolensky reduction, discharged. -/
theorem param_gap (n D e : ℕ) (hD : 2 * D < n) (he : 2 * e < 2 ^ n) :
    Fintype.card {T : Finset (Fin n) // T.card ≤ D} < 2 ^ n - e := by
  have h1 := two_card_lowdeg_le n D hD
  have h2 : Fintype.card {T : Finset (Fin n) // T.card ≤ D}
      = (Finset.univ.filter (fun T : Finset (Fin n) => T.card ≤ D)).card := by
    rw [Fintype.card_subtype]
  rw [h2]
  omega

end PallLean.Paper93.DeepMath.PathB.RSParamGap

#print axioms PallLean.Paper93.DeepMath.PathB.RSParamGap.param_gap
