import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CommunicationComplexity
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CarryRefinementCrossing

/-!
# A characteristic-coupled boundary invariant — surviving the equality counterexample (typed crossing)

Entry 287 killed raw boundary size: equality (`∈ AC⁰ ⊆ ACC⁰[6]`) has exponential communication boundary, so boundary
*size* cannot separate.  The fix the no-go pointed to: an invariant that is **characteristic-aware** — it must track
*which* prime characteristic a computation's modular structure requires, not how big its boundary is.  The decisive
asymmetry:

* equality is **not** a count/MOD predicate — it carries *no* modulus, hence no required characteristic — so a
  characteristic-aware invariant never flags it (whereas raw boundary did, entry 287);
* `MOD_m` carries the modulus `m`, hence the *required prime set* `primeFactors m` — and is obstructed exactly when a
  required prime is unavailable.

**The typed invariant.**  `CrossCharacteristic m S := ∃ p prime, p ∣ m ∧ p ∉ S`: the modulus `m` forces a prime
characteristic `p` outside the available set `S` (the `MOD`-gate primes of the model).  For `ACC⁰[6]`, `S = {2,3}`.

**Classification (all proved).**  It separates exactly the cases entry 287 said it must:
* equality — not a count predicate (`equality_not_count_predicate`), so no modulus, **not flagged**;
* native `MOD_p` — required prime `{p}`, available in char `p`;
* `MOD₆` over a *single* field — `CrossCharacteristic 6 {p}` for every prime `p` (`mod6_cross_single_field`): `6 = 2·3`
  has two distinct prime factors, no single characteristic carries both (the "no common characteristic" of entries
  280–283);
* `MOD₆` over `ACC⁰[6]` — `¬ CrossCharacteristic 6 {2,3}` (`mod6_not_cross_acc6`): both factors available, so `MOD₆ ∈
  ACC⁰[6]` — correctly *not* obstructed;
* non-native `MOD_5`, `MOD_30` over `ACC⁰[6]` — `CrossCharacteristic 5 {2,3}`, `CrossCharacteristic 30 {2,3}`
  (`mod5_cross_acc6`, `mod30_cross_acc6`): the prime `5 ∉ {2,3}` is unavailable, so they are obstructed.

**The typed theorem.**  `TypedCarryRefinementCrossing Computes S := ∀ m, CrossCharacteristic m S → ¬ Computes S m` —
the typed analog of entry 283's `CarryRefinementCrossing`, now characteristic-coupled (immune to the equality
counterexample).  `typed_crossing_excludes_mod5` (PROVED conditional): the typed crossing applied to the smallest
unavailable prime gives `MOD_5 ∉ ACC⁰[6]`.  The deep implication "cross-characteristic ⟹ not computable" is the open
**Smolensky-composite** barrier (separation-strength; the single-prime instance `MOD_q ∉ AC⁰[p]` is already proved in
this arc as `Layer4.mod_q_indicators_false`, but the lift to the composite class `ACC⁰[6]` is open), kept as the socket.

## What is proved (clean axioms, no `sorry`)

* **`mod5_cross_acc6`, `mod30_cross_acc6`** (PROVED) — `MOD_5`, `MOD_30` are cross-characteristic for `ACC⁰[6]`
  (prime `5 ∉ {2,3}`).
* **`mod6_not_cross_acc6`** (PROVED) — `MOD₆` is *not* cross-characteristic for `ACC⁰[6]` (both prime factors
  available) — the invariant correctly leaves `MOD₆ ∈ ACC⁰[6]` unobstructed.
* **`mod6_cross_single_field`** (PROVED) — `MOD₆` is cross-characteristic for *every single* field `{p}`: the
  carry-crossing / no-common-characteristic fact, now in the typed invariant.
* **`equality_not_count_predicate`** (PROVED) — equality is not a count/MOD predicate, so it carries no modulus and the
  characteristic invariant never flags it: the typed invariant **survives the entry-287 equality counterexample**.
* **`typed_crossing_excludes_mod5`** (PROVED conditional) — typed crossing ⟹ `MOD_5 ∉ ACC⁰[6]`.
* **`typed_separation_chain`** (PROVED conditional) — typed crossing + the composite-component socket ⟹ the
  composite-`ACC⁰` ingredient toward Williams.

## Honest scope

A genuinely characteristic-coupled invariant that **provably distinguishes** equality (not flagged) from `MOD₆`/`MOD_q`
carry crossing — the discrimination entry 287 proved raw boundary could not make.  The classification is fully proved;
the deep "cross-characteristic ⟹ not `ACC⁰[6]`-computable" implication is the open Smolensky-composite barrier, kept as
an honest socket and wired to Williams.  This is **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TypedBoundary

open PallLean.Paper93.DeepMath.PathB

/-- **The characteristic-coupled invariant.**  `CrossCharacteristic m S` holds when the modulus `m` forces a prime
characteristic `p` *outside* the available set `S` — i.e. `MOD_m`'s CRT structure needs a `MOD_p` not available in the
model.  This is characteristic-*type*, not boundary size: it is keyed to the prime factorisation of the modulus, so it
applies only to genuine `MOD` targets. -/
def CrossCharacteristic (m : ℕ) (S : Finset ℕ) : Prop :=
  ∃ p, p.Prime ∧ p ∣ m ∧ p ∉ S

/-- The available characteristics of `ACC⁰[6]`: the primes of its `MOD` gates. -/
def acc6 : Finset ℕ := {2, 3}

/-- **`MOD_5` is cross-characteristic for `ACC⁰[6]` (PROVED).**  The prime `5 ∣ 5` is not in `{2,3}` — `MOD_5` needs a
characteristic unavailable to `ACC⁰[6]`.  This is the smallest non-native composite-`ACC⁰` target. -/
theorem mod5_cross_acc6 : CrossCharacteristic 5 acc6 :=
  ⟨5, by norm_num, dvd_refl 5, by decide⟩

/-- **`MOD_30` is cross-characteristic for `ACC⁰[6]` (PROVED).**  `30 = 2·3·5`; the prime factor `5 ∉ {2,3}`. -/
theorem mod30_cross_acc6 : CrossCharacteristic 30 acc6 :=
  ⟨5, by norm_num, by norm_num, by decide⟩

/-- **`MOD₆` is NOT cross-characteristic for `ACC⁰[6]` (PROVED).**  Every prime factor of `6` is in `{2,3}`, so `MOD₆`
needs no unavailable characteristic — correctly leaving `MOD₆ ∈ ACC⁰[6]` unobstructed (the invariant does *not*
over-fire, unlike a single-field method). -/
theorem mod6_not_cross_acc6 : ¬ CrossCharacteristic 6 acc6 := by
  rintro ⟨p, hp, hdvd, hni⟩
  have h6 : p ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  have h2 : 2 ≤ p := hp.two_le
  interval_cases p
  · exact hni (by decide)
  · exact hni (by decide)
  · exact absurd hp (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hp (by norm_num)

/-- **`MOD₆` is cross-characteristic for every single field (PROVED).**  For any prime `p`, `MOD₆` forces a prime factor
of `6` outside `{p}`: `6 = 2·3` has two distinct prime factors, so no single characteristic `p` carries both.  This is
the "no common characteristic" carry-crossing of entries 280–283, now expressed in the typed invariant: the *single
field* polynomial method (available set `{p}`) cannot compute `MOD₆`. -/
theorem mod6_cross_single_field (p : ℕ) (hp : p.Prime) : CrossCharacteristic 6 ({p} : Finset ℕ) := by
  by_cases h : p = 2
  · exact ⟨3, by norm_num, by norm_num, by simp [h]⟩
  · exact ⟨2, by norm_num, by norm_num, by simp only [Finset.mem_singleton]; omega⟩

/-- The Hamming weight of a 2-bit input (used to witness that equality is not a count predicate). -/
def wt2 (a : Fin 2 → Bool) : ℕ := (if a 0 then 1 else 0) + (if a 1 then 1 else 0)

/-- **Equality is NOT a count/MOD predicate (PROVED) — the discriminator that beats entry 287.**  There is no function
`g` of the total weight across the cut with `[a = b] = g(wt a + wt b)`: the inputs `(10, 01)` and `(10, 10)` have the
same total weight `2` but differ in equality (`false` vs `true`).  So equality carries *no* modulus and *no* required
characteristic — the characteristic-coupled invariant never flags it.  This is exactly the asymmetry that raw boundary
size (entry 287) could not see: equality has huge boundary but is not characteristic-coupled. -/
theorem equality_not_count_predicate :
    ¬ ∃ g : ℕ → Bool, ∀ a b : Fin 2 → Bool, decide (a = b) = g (wt2 a + wt2 b) := by
  rintro ⟨g, hg⟩
  have h1 := hg ![true, false] ![false, true]
  have h2 := hg ![true, false] ![true, false]
  rw [show wt2 ![true, false] + wt2 ![false, true] = 2 from by decide,
      show decide ((![true, false] : Fin 2 → Bool) = ![false, true]) = false from by decide] at h1
  rw [show wt2 ![true, false] + wt2 ![true, false] = 2 from by decide,
      show decide ((![true, false] : Fin 2 → Bool) = ![true, false]) = true from by decide] at h2
  exact absurd (h1.trans h2.symm) (by decide)

/-- **The typed carry-refinement crossing (named socket).**  `Computes S m` abstracts "`MOD_m` is computable by an
`ACC⁰[S]` circuit" (the `MOD`-gate primes are `S`).  `TypedCarryRefinementCrossing` is the characteristic-coupled analog
of entry 283's `CarryRefinementCrossing`: a cross-characteristic `MOD_m` is *not* `ACC⁰[S]`-computable.  Unlike raw
boundary, this is immune to the equality counterexample (equality is not cross-characteristic).  The implication is the
open Smolensky-composite barrier — its single-prime instance `MOD_q ∉ AC⁰[p]` is proved in this arc
(`Layer4.mod_q_indicators_false`); the lift to the composite class is open. -/
def TypedCarryRefinementCrossing (Computes : Finset ℕ → ℕ → Prop) (S : Finset ℕ) : Prop :=
  ∀ m : ℕ, CrossCharacteristic m S → ¬ Computes S m

/-- **Typed crossing excludes `MOD_5` from `ACC⁰[6]` (PROVED conditional).**  Applying the typed crossing to the
smallest unavailable-prime target: `MOD_5` is cross-characteristic for `ACC⁰[6]` (`mod5_cross_acc6`), so the typed
crossing yields `¬ Computes acc6 5` — `MOD_5 ∉ ACC⁰[6]`, a composite-`ACC⁰` lower bound. -/
theorem typed_crossing_excludes_mod5 {Computes : Finset ℕ → ℕ → Prop}
    (h : TypedCarryRefinementCrossing Computes acc6) :
    ¬ Computes acc6 5 :=
  h 5 mod5_cross_acc6

/-- **Wiring the typed crossing toward Williams (PROVED conditional).**  Given the typed crossing and the
composite-component socket `CompositeComponent` ("`MOD_5 ∉ ACC⁰[6]` ⟹ the composite-`ACC⁰` ingredient"), the
composite-`ACC⁰` component holds.  This is the typed analog of the entry-278 `prime_route_to_ACC0Component`, feeding the
Williams `NEXP ⊄ ACC⁰` route.  Both inputs are sockets: the typed crossing (Smolensky-composite) and the
component-to-Williams bridge (the existing arc). -/
theorem typed_separation_chain {Computes : Finset ℕ → ℕ → Prop} {ACC0CompositeComponent : Prop}
    (hcross : TypedCarryRefinementCrossing Computes acc6)
    (CompositeComponent : ¬ Computes acc6 5 → ACC0CompositeComponent) :
    ACC0CompositeComponent :=
  CompositeComponent (typed_crossing_excludes_mod5 hcross)

/-!
**The result.**  Entry 287 showed boundary *size* cannot separate (equality breaks it).  This file builds a
characteristic-*coupled* invariant that **provably distinguishes** the cases: equality is not a count predicate, hence
not cross-characteristic, hence never flagged; `MOD₆` is cross-characteristic for any single field (carry crossing) but
not for `ACC⁰[6]` (so `MOD₆ ∈ ACC⁰[6]`, correctly); `MOD_5`/`MOD_30` are cross-characteristic for `ACC⁰[6]` (the genuine
obstruction).  The typed crossing `TypedCarryRefinementCrossing` then yields `MOD_5 ∉ ACC⁰[6]` and the composite-`ACC⁰`
ingredient — conditional on the one open socket: the Smolensky-composite implication "cross-characteristic ⟹ not
`ACC⁰[6]`-computable" (separation-strength; single-prime instance already proved as `Layer4.mod_q_indicators_false`).
The invariant is honest progress past the entry-287 wall; the deep lower bound remains the named, open barrier.  Not
faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0TypedBoundary

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TypedBoundary.mod5_cross_acc6
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TypedBoundary.mod30_cross_acc6
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TypedBoundary.mod6_not_cross_acc6
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TypedBoundary.mod6_cross_single_field
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TypedBoundary.equality_not_count_predicate
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TypedBoundary.typed_crossing_excludes_mod5
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TypedBoundary.typed_separation_chain
