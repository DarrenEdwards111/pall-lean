import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# The algebraic engines of the two remaining RS/AC⁰[p] sockets

The two open sockets — Smolensky's **spreading** and the RS **switching-lemma approximation** — are
substantial constructive/probabilistic theorems, not clean one-brick formalizations.  But each has a
precise *algebraic engine* that is fully provable, and this file discharges both, isolating exactly the
constructive wrappers that remain.

* **spreading** ← the **roots-of-unity filter**: for `ω^q = 1`, `∑_{j<q} (ω^m)^j = q·[ω^m = 1]`.  This is
  how MOD_q's divisibility indicator `[q ∣ count]` becomes a linear combination of powers `ω^{m·count}` —
  the change of variables at the heart of spreading.
* **RS approximation** ← MOD_p gates are **exactly** degree `p−1`: over `F_p`, `1 − a^{p−1} = [a = 0]`
  (Fermat).  The exact low-degree structure of the MOD_p gates the switching lemma composes.

## What is proved

* **`roots_of_unity_filter`** — `∑_{j<q} (ω^m)^j = if ω^m = 1 then q else 0` (geometric-sum / Fermat).
* **`mod_p_indicator`** — over `ZMod p` (`p` prime), `1 − a^{p−1} = if a = 0 then 1 else 0`.

## Honest scope

These are the *engines*, proved and axiom-clean — not the full theorems.  The full **spreading** wraps the
filter over an extension field `F_{p^k}` (with a primitive `q`-th root) plus the degree bookkeeping; the
full **RS approximation** wraps the exact MOD_p gates with the *probabilistic* low-degree approximation of
AND/OR gates and the depth-`d` composition.  Those constructive wrappers remain the honest open pieces;
here the algebraic cores they rest on are discharged.  `AC⁰[p]`-restricted; nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RSAlgebraicCores

open scoped Classical

variable {F : Type*} [Field F]

/-- **The roots-of-unity filter (proved).**  If `ω^q = 1`, then `∑_{j<q} (ω^m)^j` is `q` when `ω^m = 1`
and `0` otherwise.  This turns MOD_q's divisibility indicator into a sum of powers — the spreading
change of variables. -/
theorem roots_of_unity_filter (ω : F) (q m : ℕ) (hω : ω ^ q = 1) :
    ∑ j ∈ Finset.range q, (ω ^ m) ^ j = if ω ^ m = 1 then (q : F) else 0 := by
  by_cases h : ω ^ m = 1
  · rw [if_pos h]
    simp [h]
  · rw [if_neg h, geom_sum_eq h q]
    have hq : (ω ^ m) ^ q = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω, one_pow]
    rw [hq, sub_self, zero_div]

/-- **MOD_p gates are exactly degree `p−1` (proved).**  Over `F_p`, `1 − a^{p−1}` is the indicator
`[a = 0]` (Fermat's little theorem).  The exact low-degree structure the switching lemma composes. -/
theorem mod_p_indicator {p : ℕ} [Fact p.Prime] (a : ZMod p) :
    1 - a ^ (p - 1) = if a = 0 then 1 else 0 := by
  by_cases h : a = 0
  · subst h
    have hp1 : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt
    rw [if_pos rfl, zero_pow hp1, sub_zero]
  · rw [if_neg h, ZMod.pow_card_sub_one_eq_one h, sub_self]

end PallLean.Paper93.DeepMath.PathB.RSAlgebraicCores

#print axioms PallLean.Paper93.DeepMath.PathB.RSAlgebraicCores.roots_of_unity_filter
#print axioms PallLean.Paper93.DeepMath.PathB.RSAlgebraicCores.mod_p_indicator
