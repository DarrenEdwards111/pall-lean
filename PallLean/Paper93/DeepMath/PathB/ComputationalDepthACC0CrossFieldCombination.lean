import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0LayeredCarryDegree

/-!
# Cross-field low-degree combination — the structural root of the wall (conservative)

Entry 242 showed each per-prime layer `MOD_{pᵢ}` is low-degree over its *own* field `F_{pᵢ}` (degree `≤ pᵢ-1`,
independent of `n`), and localised the composite-`ACC⁰[m]` wall to: combine the per-prime low-degree indicators into a
*single* low-degree polynomial over a *common* field.  This file analyses that **cross-field combination** — the actual
Smolensky / `ACC⁰[composite]` barrier.  The honest outcome: the **structural root** of why the combination fails is
proved (distinct primes force incompatible field characteristics, and the mod-`p` reduction is blind to mod-`q`); the
**degree lower bound itself** (MOD_q is not low-degree over `F_p` for `q ≠ p`) is Smolensky's deep theorem and remains
the named open wall.

⚠️ **No crossing, no faked no-go.**  I do not prove Smolensky's lower bound (the deep, separation-adjacent theorem), and
I do not cross it.  The proved content is *why the naive combination routes fail at the root*; the full degree lower
bound stays open.

## What is proved (clean axioms, no `sorry`)

* **`no_common_char`** (PROVED) — no field is simultaneously characteristic `p` and characteristic `q` for distinct
  `p, q` (`CharP.eq`).  So the `F_p`-indicator and the `F_q`-indicator cannot natively share a field — the root
  incompatibility.
* **`self_prime_zero`** / **`other_prime_unit`** (PROVED) — in `F_p`, `p ↦ 0` but the other prime `q ↦` a *unit*
  (`(q : ZMod p) ≠ 0`).  The field's characteristic privileges its own prime: the Fermat indicator (entry 242) is
  native to mod-`p`, not mod-`q`.
* **`reduction_blind_to_other_prime`** (PROVED) — the count-mod-`p` reduction is blind to mod-`q` structure: there are
  counts equal mod `p` but differing mod `q` (`0` and `p`).  So any decode that factors through `count mod p` cannot
  compute `MOD_q` — the naive (single-residue) route provably fails.

## The deep residual (named, not proved)

Combining over a single field `F_p` requires realising `MOD_q` (`q ≠ p`) by a *low-degree* `F_p`-polynomial in the input
bits.  Entry 242 gives the *native* case `MOD_p` at degree `≤ p-1`; the *non-native* case `MOD_q` at low degree is
**Smolensky's lower bound** — it provably requires high degree, the deep `ACC⁰[composite]` theorem.  This is the open
wall (entry-238 `CarryRefinementCrossing` / entry-241 layered question); not proved here.

## Honest scope

The proved content is the **structural root** of the cross-field obstruction — incompatible characteristics
(`no_common_char`), the characteristic asymmetry (`self_prime_zero`/`other_prime_unit`), and the mod-`p` reduction's
blindness to mod-`q` (`reduction_blind_to_other_prime`).  These explain *why* the naive cross-field combinations fail.
What remains is the genuine degree lower bound — `MOD_q` is not low-degree over `F_p` — which is **Smolensky's theorem**,
the deep open `ACC⁰[composite]` wall; this file neither proves nor crosses it.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CrossFieldCombination

/-- **No common field characteristic (PROVED).**  No field is simultaneously `CharP p` and `CharP q` for distinct
`p, q` (`CharP.eq` gives `p = q`).  Hence the `MOD_p` indicator (over `F_p`) and the `MOD_q` indicator (over `F_q`)
cannot natively live in one field — the root of the cross-field obstruction. -/
theorem no_common_char (F : Type*) [Field F] (p q : ℕ) (hpq : p ≠ q)
    (h1 : CharP F p) (h2 : CharP F q) : False :=
  hpq (CharP.eq F h1 h2)

/-- **The field's own prime collapses to `0` (PROVED).**  `(p : ZMod p) = 0`. -/
theorem self_prime_zero (p : ℕ) [Fact p.Prime] : (p : ZMod p) = 0 := ZMod.natCast_self p

/-- **The other prime is a unit in `F_p` (PROVED).**  For distinct primes `p, q`, `(q : ZMod p) ≠ 0` — the
characteristic privileges its own prime, so the native Fermat indicator (entry 242) detects mod-`p`, not mod-`q`. -/
theorem other_prime_unit (p q : ℕ) [Fact p.Prime] (hq : q.Prime) (hpq : p ≠ q) :
    (q : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  exact hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out) hq).mp hdvd)

/-- **The count-mod-`p` reduction is blind to mod-`q` (PROVED).**  There are counts equal mod `p` but differing mod `q`
(`0` and `p`: same mod `p` since `p ≡ 0`, different mod `q` since `q ∤ p`).  So any decode factoring through `count mod
p` cannot compute `MOD_q` — the naive single-residue cross-field route fails. -/
theorem reduction_blind_to_other_prime (p q : ℕ) [Fact p.Prime] (hq : q.Prime) (hpq : p ≠ q) :
    ∃ k k' : ℕ, (k : ZMod p) = (k' : ZMod p) ∧ k % q ≠ k' % q := by
  refine ⟨0, p, ?_, ?_⟩
  · simp
  · simp only [Nat.zero_mod]
    intro h
    have hd : q ∣ p := Nat.dvd_of_mod_eq_zero h.symm
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq (Fact.out)).mp hd).symm

/-!
**The deep residual (named, not proved).**  Over a single field `F_p`, combining requires realising `MOD_q` (`q ≠ p`)
by a low-degree `F_p`-polynomial in the input bits.  The *native* case `MOD_p` is degree `≤ p-1`
(entry-242 `ACC0LayeredCarryDegree.modpIndicator_totalDegree_le`); the *non-native* case `MOD_q` at low degree is
**Smolensky's lower bound** (high degree required) — the open `ACC⁰[composite]` wall (entry-238
`CarryRefinementCrossing`).  Not proved here; the structural facts above are the honest root, not the lower bound.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CrossFieldCombination

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CrossFieldCombination.no_common_char
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CrossFieldCombination.other_prime_unit
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CrossFieldCombination.reduction_blind_to_other_prime
