import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TriAspectBoundary
import Mathlib.Data.ZMod.Basic

/-!
# The composite-`MOD` Beigel–Tarui target — `MOD₆`, single-field RS failure, and the integer/product observer

Tri-aspect monism has selected the *algebraic* projection as the working observer (`…ACC0TriAspectBoundary`), and the
single remaining hard wall is the **composite-modulus** algebraic projection: the Yao/Beigel–Tarui `SYM∘AND` degree
theorem.  This file isolates that wall at the smallest composite obstruction, `MOD₆ = MOD₂ ∧ MOD₃`, and does two
genuine things before socketing the deep theorem:

1. **Proves why the single-field RS observer fails for `MOD₆`.**  The Razborov–Smolensky polynomial observer lives in a
   span over *one* prime field `ZMod p`.  But the `ℤ/6` residue structure embeds into **no** single prime field:
   there is no injective ring homomorphism `ZMod 6 → ZMod p` (the zero-divisor `2·3 = 0` of `ZMod 6` cannot survive in
   a field).  So a single-field span cannot faithfully carry both the `MOD₂` and the `MOD₃` information at once.

2. **Defines the replacement observer that can** — the integer/multi-prime *product* observer.  By CRT,
   `ZMod 6 ≃+* ZMod 2 × ZMod 3`: the product ring (not itself a field) faithfully carries the full residue structure,
   and the symmetric-count observer over this product decides `MOD₆` from the *pair* of residues.  This is exactly the
   Beigel–Tarui move: observe counts/residues symmetrically over `ℤ` (here `ℤ/2 × ℤ/3`), not over one field.

## What is proved (clean axioms, no `sorry`)

* **`mod6_iff_mod2_and_mod3`** — `6 ∣ m ↔ 2 ∣ m ∧ 3 ∣ m` (the composite obstruction `MOD₆ = MOD₂ ∧ MOD₃`).
* **`field_polynomial_projection_fails_for_MOD6`** (= `no_injective_ringHom_zmod6_to_prime_field`) — no injective ring
  hom `ZMod 6 → ZMod p` for any prime `p`: the single-field RS observer cannot carry the `ℤ/6` residue structure.
* **`compositeResidueObserver`** — the integer/product observer `ZMod 6 ≃+* ZMod 2 × ZMod 3` (CRT), with
  **`compositeResidueObserver_injective`** — it *is* faithful, unlike any single field.
* **`mod6_decided_by_residue_pair`** — `6 ∣ m ↔ (m mod 2 = 0 ∧ m mod 3 = 0)`: the product observer decides `MOD₆`.
* **`mod6_symAnd_residue_pair`** — restricted composite representation on boolean inputs: `MOD₆` of the Hamming weight
  is exactly the residue-pair conjunction — a genuine symmetric-count (`SYM`) representation via the product observer.

## The one open step (socketed honestly)

* **`mod6_composite_route_to_NEXP_not_ACC0`** — the remaining hard theorem in tri-aspect language: that every
  composite-`MOD` `ACC⁰` circuit admits a *quasipolynomial* `SYM∘AND` representation read by the integer/product
  observer (named open hypothesis `composite_BT_degree`).  Given it, the Route-B counting socket + Williams cash-out
  yields `¬ NEXP ⊆ ACC⁰` (re-exporting `…ACC0RankRouteFrontier.composite_route_to_NEXP_not_ACC0`).

## Honest scope

This proves the *exact* point where single-field RS breaks for composite modulus, and exhibits the genuine
integer/product observer that replaces it — both clean theorems, not placeholders.  It does **not** prove the
quasipolynomial composite `SYM∘AND` *representation* (the deep YBT content): that survives only as the named socket.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CompositeBT

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0RankRouteFrontier

variable {n : ℕ}

/-! ## 1. The composite obstruction — `MOD₆ = MOD₂ ∧ MOD₃` -/

/-- **`MOD₆ = MOD₂ ∧ MOD₃` (proved): `6 ∣ m ↔ 2 ∣ m ∧ 3 ∣ m`.**  The smallest composite obstruction, factored through
the coprime primes `2` and `3`. -/
theorem mod6_iff_mod2_and_mod3 (m : ℕ) : 6 ∣ m ↔ 2 ∣ m ∧ 3 ∣ m := by
  constructor
  · intro h
    exact ⟨dvd_trans (show (2 : ℕ) ∣ 6 by norm_num) h,
           dvd_trans (show (3 : ℕ) ∣ 6 by norm_num) h⟩
  · rintro ⟨h2, h3⟩
    have h := Nat.Coprime.mul_dvd_of_dvd_of_dvd (show Nat.Coprime 2 3 by decide) h2 h3
    have e : (2 * 3 : ℕ) = 6 := by norm_num
    rwa [e] at h

/-! ## 2. The single-field RS observer fails for `MOD₆` -/

/-- **The single-field RS observer fails for `MOD₆` (proved): no injective ring hom `ZMod 6 → ZMod p`.**  The `ℤ/6`
residue structure has the zero-divisor `2 · 3 = 0`; in a prime field `ZMod p` there are no zero divisors, so a faithful
(injective) ring hom is impossible.  Hence a single-field polynomial span cannot simultaneously carry the `MOD₂` and
`MOD₃` information — the precise failure of single-field Razborov–Smolensky for composite modulus. -/
theorem no_injective_ringHom_zmod6_to_prime_field (p : ℕ) [Fact p.Prime]
    (f : ZMod 6 →+* ZMod p) : ¬ Function.Injective f := by
  intro hinj
  have hf : (f 2 : ZMod p) * f 3 = 0 := by
    rw [← map_mul, show (2 : ZMod 6) * 3 = 0 from by decide]
    exact map_zero f
  have h2ne : (f 2 : ZMod p) ≠ 0 := by
    intro hc
    have : (2 : ZMod 6) = 0 := hinj (by rw [hc, map_zero])
    exact absurd this (by decide)
  have h3ne : (f 3 : ZMod p) ≠ 0 := by
    intro hc
    have : (3 : ZMod 6) = 0 := hinj (by rw [hc, map_zero])
    exact absurd this (by decide)
  rcases mul_eq_zero.mp hf with h | h
  · exact h2ne h
  · exact h3ne h

/-- Tri-aspect alias: the field (single-prime) algebraic projection fails for the composite `MOD₆` boundary. -/
theorem field_polynomial_projection_fails_for_MOD6 (p : ℕ) [Fact p.Prime]
    (f : ZMod 6 →+* ZMod p) : ¬ Function.Injective f :=
  no_injective_ringHom_zmod6_to_prime_field p f

/-! ## 3. The replacement — the integer / multi-prime product observer (CRT) -/

/-- **The composite residue observer (proved isomorphism): `ZMod 6 ≃+* ZMod 2 × ZMod 3`.**  The integer/multi-prime
observer of the Beigel–Tarui method — the *product* ring (not itself a field) that faithfully carries the full `ℤ/6`
residue structure that no single prime field could. -/
noncomputable def compositeResidueObserver : ZMod 6 ≃+* ZMod 2 × ZMod 3 :=
  ZMod.chineseRemainder (show Nat.Coprime 2 3 by decide)

/-- **The product observer is faithful (proved)** — in contrast with the single-field failure above. -/
theorem compositeResidueObserver_injective :
    Function.Injective compositeResidueObserver :=
  compositeResidueObserver.injective

/-! ## 4. The product observer decides `MOD₆` -/

/-- **The product observer decides `MOD₆` from the residue pair (proved): `6 ∣ m ↔ (m mod 2 = 0 ∧ m mod 3 = 0)`.** -/
theorem mod6_decided_by_residue_pair (m : ℕ) :
    6 ∣ m ↔ ((m : ZMod 2) = 0 ∧ (m : ZMod 3) = 0) := by
  rw [mod6_iff_mod2_and_mod3, ZMod.natCast_eq_zero_iff, ZMod.natCast_eq_zero_iff]

/-! ## 5. Restricted composite representation on boolean inputs -/

/-- The Hamming weight: the symmetric count of `true` coordinates. -/
def hammingWeight (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => x i = true)).card

/-- The `MOD₆` symmetric function at residue `0`. -/
def MOD6 (x : Fin n → Bool) : Prop := 6 ∣ hammingWeight x

/-- **Restricted composite representation (proved): the symmetric residue-pair observer represents `MOD₆`.**  On
boolean inputs, `MOD₆` of the Hamming weight is exactly the conjunction of the two residue observers over `ZMod 2` and
`ZMod 3` — a genuine `SYM` (symmetric-count) representation via the integer/product observer, not a single-field
span.  This is the smallest restricted composite case discharged. -/
theorem mod6_symAnd_residue_pair (x : Fin n → Bool) :
    MOD6 x ↔ ((hammingWeight x : ZMod 2) = 0 ∧ (hammingWeight x : ZMod 3) = 0) :=
  mod6_decided_by_residue_pair (hammingWeight x)

/-! ## 6. The open composite-Beigel–Tarui socket, in tri-aspect language -/

/-- **The open composite-`MOD` algebraic projection target (socket).**  The remaining hard theorem: that every
composite-`MOD` `ACC⁰` circuit admits a *quasipolynomial* `SYM∘AND` representation read off by the integer/product
residue observer (the `MOD₆ ≃ ZMod 2 × ZMod 3` move generalised through `ACC⁰` composition with quasipolynomial
blow-up) — the full Yao/Beigel–Tarui degree theorem, here the named open hypothesis `composite_BT_degree`.  Given it,
the Route-B counting socket + Williams cash-out yields `¬ NEXP ⊆ ACC⁰`. -/
theorem mod6_composite_route_to_NEXP_not_ACC0
    (RSRep ACC0SatSpeedup NEXPHasACC0Circuits Collapse : Prop)
    (composite_BT_degree : RSRep)
    (counting : RSRep → ACC0SatSpeedup)
    (williams : ACC0SatSpeedup → NEXPHasACC0Circuits → Collapse)
    (hierarchy : ¬ Collapse) :
    ¬ NEXPHasACC0Circuits :=
  composite_route_to_NEXP_not_ACC0 RSRep ACC0SatSpeedup NEXPHasACC0Circuits Collapse
    composite_BT_degree counting williams hierarchy

end PallLean.Paper93.DeepMath.PathB.ACC0CompositeBT

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeBT.mod6_iff_mod2_and_mod3
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeBT.no_injective_ringHom_zmod6_to_prime_field
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeBT.compositeResidueObserver_injective
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeBT.mod6_decided_by_residue_pair
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeBT.mod6_symAnd_residue_pair
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeBT.mod6_composite_route_to_NEXP_not_ACC0
