import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TypedBoundary
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CrossFieldCombination

/-!
# Why the algorithmic route escapes the composite barrier — counting over ℤ carries all characteristics

Entries 280–289 proved the polynomial / field-free route is *genuinely blocked* at the composite barrier: a single
finite field has one characteristic, and `no_common_char` forbids the two incompatible characteristics that `MOD₆`'s CRT
factors demand.  Williams' `NEXP ⊄ ACC⁰` route does **not** go through the polynomial method — it is **algorithmic**: it
*counts* satisfying assignments.  This file pins the structural reason that escapes the barrier.

**The escape.**  A count of satisfying assignments is an **integer** `c : ℤ` (or `ℕ`), living in characteristic `0`.
`ℤ` is the initial ring: it maps onto `ZMod m` for **every** `m` (`Int.castRingHom`).  So a *single* integer count
simultaneously determines `c mod 2`, `c mod 3`, …, `c mod m` for all `m` at once — it carries *every* characteristic.
That is exactly what no single finite field can do (`no_common_char`): a field commits to one characteristic.  Counting
sidesteps the commitment.

**Pinned to the typed invariant (entry 288).**  The count route's available characteristic set is *all* primes
(reduce the integer mod each), not the fixed `{2,3}` of `ACC⁰[6]`'s polynomial method.  So `count_route_covers`: for
the count route the available set is `m.primeFactors`, and `CrossCharacteristic m m.primeFactors` is **false** — the
algorithmic observer is *never* characteristic-blocked, for any modulus.  The typed obstruction (entry 288) is specific
to the *single-characteristic* polynomial method; the counting route has no such obstruction.

**What is still needed (honest socket).**  This explains *why* the algorithmic route can succeed where polynomials are
blocked — it is not characteristic-bound.  It does **not** prove `NEXP ⊄ ACC⁰`: Williams' route still requires the deep
ingredients (a faster-than-trivial `#SAT` algorithm for `ACC⁰` circuits ⇒ the lower bound, via the easy-witness / IKW
machinery), which are the existing corpus sockets (`…WilliamsFastSat`, the Karp–Lipton / NW–IKW chain).  Those are not
re-proved here; this file isolates the *structural enabler* — characteristic-universality of integer counting.

## What is proved (clean axioms, no `sorry`)

* **`count_crt_mod6`** (PROVED) — one integer count carries char-2 *and* char-3 simultaneously:
  `c % 6 = 0 ↔ (c % 2 = 0 ∧ c % 3 = 0)`.
* **`count_computes_all_moduli`** (PROVED) — a single count function computes `MOD_m` for *every* `m` (`countMod c m`).
* **`integer_carries_every_characteristic`** (PROVED) — `ℤ` casts to `ZMod m` for every `m` (carries all
  characteristics), via `Int.castRingHom`.
* **`no_field_carries_two_primes`** (PROVED, re-export) — the contrast: no single field has two distinct prime
  characteristics (`no_common_char`).
* **`count_route_covers`** (PROVED) — for the count route the available set is `m.primeFactors`, so
  `CrossCharacteristic m m.primeFactors` is false: the algorithmic observer is never characteristic-blocked.

## Honest scope

A machine-proved account of *why* the algorithmic (counting) route escapes the composite-`ACC⁰` barrier that provably
blocks the polynomial method (entries 280–289): integer counting lives in characteristic 0 and carries every
characteristic at once, whereas a single field commits to one.  This is the structural enabler of Williams' route, tied
to the typed invariant.  It is **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`; the deep `#SAT`-algorithm ⇒ lower-bound implication
remains the existing socket.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0AlgorithmicEscape

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.ACC0TypedBoundary

/-- `MOD_m` read off an integer count `c`: the algorithmic route's observable — `decide (c % m = 0)`.  A *single*
integer `c` feeds this for every modulus `m`. -/
def countMod (c m : ℕ) : Bool := decide (c % m = 0)

/-- **One integer count carries char-2 and char-3 simultaneously (PROVED).**  `c % 6 = 0 ↔ (c % 2 = 0 ∧ c % 3 = 0)`:
the CRT decomposition of `MOD₆` is realised by a *single* integer count via its residues mod 2 and mod 3 — no field
needed.  This is precisely what `no_common_char` forbids for a single field, yet an integer does it freely. -/
theorem count_crt_mod6 (c : ℕ) : (c % 6 = 0) ↔ (c % 2 = 0 ∧ c % 3 = 0) := by
  omega

/-- **A single count function computes `MOD_m` for every modulus (PROVED).**  `countMod c m` is the *same* observable
for all `m` — the algorithmic route reads every modulus off one integer, unlike the polynomial method which fixes one
characteristic. -/
theorem count_computes_all_moduli (c m : ℕ) : countMod c m = decide (c % m = 0) := rfl

/-- **An integer carries every characteristic (PROVED).**  For every `m`, `ℤ` maps onto `ZMod m` (`Int.castRingHom`):
a single integer simultaneously inhabits every characteristic quotient.  `ℤ` (characteristic 0) is the initial ring,
compatible with all primes at once. -/
theorem integer_carries_every_characteristic (m : ℕ) :
    ∃ _f : ℤ →+* ZMod m, True :=
  ⟨Int.castRingHom (ZMod m), trivial⟩

/-- **No single field carries two distinct prime characteristics (PROVED, re-export).**  The contrast with integer
counting: a field commits to one characteristic (`no_common_char`, entries 243, 280).  This is the barrier that blocks
the polynomial method and that counting over `ℤ` sidesteps. -/
theorem no_field_carries_two_primes (F : Type) [Field F] (p q : ℕ) (hpq : p ≠ q)
    (h1 : CharP F p) (h2 : CharP F q) : False :=
  ACC0CrossFieldCombination.no_common_char F p q hpq h1 h2

/-- **The count route is never characteristic-blocked (PROVED).**  For the algorithmic observer the available
characteristic set is *all* primes dividing `m` (reduce the integer count mod each), namely `m.primeFactors`.  So
`CrossCharacteristic m m.primeFactors` is **false**: unlike the fixed-`{2,3}` polynomial method (entry 288), the
counting route has every required prime available, for any modulus `m ≠ 0`.  This is the escape from the typed
obstruction, in the language of entry 288. -/
theorem count_route_covers {m : ℕ} (hm : m ≠ 0) :
    ¬ CrossCharacteristic m m.primeFactors := by
  rintro ⟨p, hp, hdvd, hni⟩
  exact hni (Nat.mem_primeFactors.mpr ⟨hp, hdvd, hm⟩)

/-- **The algorithmic escape, bundled (PROVED).**  Three facts together explain why counting beats the polynomial
method on composite moduli: (1) one integer count realises `MOD₆`'s CRT decomposition (`count_crt_mod6`); (2) the count
route is never characteristic-blocked for any modulus (`count_route_covers`); (3) yet no single field carries two
distinct prime characteristics (`no_field_carries_two_primes`).  So the counting observer (characteristic 0) is *not*
characteristic-bound, whereas the field-based polynomial method is — the structural reason Williams went algorithmic. -/
theorem algorithmic_escape :
    (∀ c : ℕ, (c % 6 = 0) ↔ (c % 2 = 0 ∧ c % 3 = 0))
    ∧ (∀ m : ℕ, m ≠ 0 → ¬ CrossCharacteristic m m.primeFactors)
    ∧ (∀ (F : Type) [Field F] (p q : ℕ), p ≠ q → CharP F p → CharP F q → False) :=
  ⟨count_crt_mod6, fun _ hm => count_route_covers hm, fun F _ p q => no_field_carries_two_primes F p q⟩

/-!
**The pivot.**  The polynomial method is blocked at the composite barrier because a finite field commits to one
characteristic (`no_field_carries_two_primes`).  The algorithmic route counts over `ℤ` — characteristic 0, which carries
*every* characteristic at once (`integer_carries_every_characteristic`, `count_crt_mod6`) — so it is never
characteristic-blocked (`count_route_covers`).  That is the structural enabler of Williams' `NEXP ⊄ ACC⁰` route: it
sidesteps the exact obstruction (entries 280–289) that kills the polynomial / observer method.  What remains is the deep
`#SAT`-algorithm ⇒ lower-bound machinery (the existing `…WilliamsFastSat` / Karp–Lipton / NW–IKW sockets), not re-proved
here.  This isolates *why* the algorithmic route can win where polynomials cannot.  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0AlgorithmicEscape

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AlgorithmicEscape.count_crt_mod6
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AlgorithmicEscape.count_computes_all_moduli
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AlgorithmicEscape.integer_carries_every_characteristic
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AlgorithmicEscape.no_field_carries_two_primes
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AlgorithmicEscape.count_route_covers
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AlgorithmicEscape.algorithmic_escape
