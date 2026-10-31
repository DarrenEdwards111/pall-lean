import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4Capstone

/-!
# Why Razborov–Smolensky does not extend to composite — the foreign-gate obstruction (proved)

Workstream B (composite barrier), continued.  Entry 317 showed the surviving §4 candidates collapse onto the *single*
open socket `PolynomialMethodApproximation` ("an `AC⁰[m]` circuit's gates admit a low-degree approximation over a single
field").  This file formalises **why that socket cannot be discharged for composite `m`** the way it is for a single
prime — the gate-level obstruction to the proof technique.

**The mechanism.**  The polynomial method runs over a *single* field `K`.  An `AC⁰[6]`-circuit has both `MOD₂` and
`MOD₃` gates; over `K` of characteristic `p`, a `MOD_q` gate is *native* only when `q ∣ p` (i.e. `q = p`), and `2 ≠ 3`
means **at least one of the two is always foreign** — exactly the algebraic root `1 = 3 − 2` of the native obstruction
(280/300/312), now in its proof-technique form.  And the in-arc general-`q` Razborov–Smolensky bound
(`Layer4.qary_full_contradiction`, the polynomial core of `mod_q_indicators_false`) proves the foreign gate has **no**
low-degree approximation: there is no family of degree-`≤ Δ` polynomials over `K = F_{p^{q-1}}` agreeing (tightly,
within the band-margin window) with the `q` residue indicators of `MOD_q`.  So the approximation step of the polynomial
method *cannot be carried out* for the foreign gate — the technique stalls at exactly the composite case.

## What is proved (clean axioms, no `sorry`)

* **`foreign_mod_no_lowDegree_approx`** — the polynomial-level RS gate no-go: for distinct primes `q ∤ p`, over
  `K = F_{p^{q-1}}`, there is **no** family of degree-`≤ Δ` polynomials tightly agreeing with the `q` residue indicators
  of `MOD_q` within the window `16·Δ² < 2m+3`.  A direct repackaging of the proved `Layer4.qary_full_contradiction`
  (the field/root/contradiction are reconstructed via `exists_primitiveRoot_galoisField`).
* **`composite_six_has_foreign_prime`** — over a field of any prime characteristic `p`, at least one of the prime
  factors `2, 3` of `6` is foreign (`¬ 2 ∣ p ∨ ¬ 3 ∣ p`) — the `2 ≠ 3` root, in proof-technique form.
* **`acc6_foreign_prime_exists`** — hence for `AC⁰[6]` over any single field there is a foreign prime `q ∈ {2,3}`,
  `q ∣ 6`, `¬ q ∣ p`: a gate whose RS approximation (`foreign_mod_no_lowDegree_approx`) is impossible.

## Honest scope

This proves the obstruction to the *proof technique*: the polynomial-method approximation step cannot produce a
low-degree approximant for a foreign `MOD` gate (the in-arc RS bound forbids it), and `AC⁰[6]` always has such a gate
over any single field.  This is the precise, formal statement of **why Razborov–Smolensky does not extend to composite
modulus** — the natural-proofs-flavoured wall.  It is **not** a lower bound against `AC⁰[6]`: it does not show `MOD₅ ∉
AC⁰[6]` (that is the genuine open problem); it shows the *single* available technique stalls.  Emphatically **not**
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `NFRAME_TWO_ROUTES.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ForeignGateObstruction

open Finset MvPolynomial
open PallLean.Paper93.DeepMath.PathB.Layer4

/-- **The polynomial-level Razborov–Smolensky gate no-go (PROVED).**  For distinct primes `q ∤ p`, over the field
`K = F_{p^{q-1}}` (characteristic `p`), there is **no** family of degree-`≤ Δ` polynomials `g j` that tightly agree
(`4q·|complement| ≤ 2ⁿ`) with the `q` residue indicators `modIndicator K q j` of `MOD_q` within the band-margin window
`16·Δ² < 2m+3`.  This is the proof-technique form of the foreign gate's hardness: the polynomial method cannot
low-degree-approximate a `MOD_q` gate over a field of the wrong characteristic.  Proved by reconstructing a primitive
`q`-th root of unity in `K` (`exists_primitiveRoot_galoisField`, available since `q ∤ p`) and invoking the proved
`qary_full_contradiction`. -/
theorem foreign_mod_no_lowDegree_approx (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : ¬ q ∣ p)
    {m Δ : ℕ} (hwindow : 16 * Δ ^ 2 < 2 * m + 3) :
    ¬ ∃ (g : ℕ → MvPolynomial (Fin (2 * m + 1)) (GaloisField p (q - 1)))
         (A : ℕ → Finset (Fin (2 * m + 1) → Bool)),
        (∀ j, (g j).totalDegree ≤ Δ) ∧
        (∀ j ∈ Finset.range q, ∀ x ∈ A j,
          eval (fun i => boolToField (GaloisField p (q - 1)) (x i)) (g j)
            = modIndicator (GaloisField p (q - 1)) q j x) ∧
        (∀ j ∈ Finset.range q, 4 * q * (Finset.univ \ A j).card ≤ 2 ^ (2 * m + 1)) := by
  rintro ⟨g, A, hdeg, hp, htight⟩
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_galoisField hpq
  have hq : 0 < q := (Fact.out (p := q.Prime)).pos
  have hζq : ζ ^ q = 1 := hζ.pow_eq_one
  have hζ0 : ζ ≠ 0 := fun h => by simp [h, zero_pow hq.ne'] at hζq
  have hζ1 : ζ ≠ 1 := hζ.ne_one (Fact.out (p := q.Prime)).one_lt
  exact qary_full_contradiction (GaloisField p (q - 1)) hζ0 hζ1 hq hζq g A hdeg hp htight hwindow

/-- **`AC⁰[6]` always has a foreign prime, over any characteristic (PROVED).**  For any prime `p`, at least one of the
prime factors `2, 3` of `6` does not divide `p` — because `2 ≠ 3` and `p` (being prime) is divisible by at most one of
them.  This is the `2 ≠ 3` algebraic root of the native obstruction, in proof-technique form: the field can be native
for at most one of the two `MOD` components. -/
theorem composite_six_has_foreign_prime (p : ℕ) (hp : p.Prime) :
    ¬ (2 ∣ p) ∨ ¬ (3 ∣ p) := by
  by_contra h
  push_neg at h
  have e2 : (2 : ℕ) = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h.1
  have e3 : (3 : ℕ) = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h.2
  omega

/-- **The foreign gate of `AC⁰[6]` (PROVED).**  Over a field of any prime characteristic `p`, there is a prime `q ∈
{2,3}` with `q ∣ 6` and `¬ q ∣ p` — a `MOD_q` gate of the composite circuit that is foreign to `K`.  Composing with
`foreign_mod_no_lowDegree_approx` (which applies precisely to such a `q`), the polynomial method's approximation step
cannot be carried out for this gate: this is why Razborov–Smolensky stalls at composite modulus. -/
theorem acc6_foreign_prime_exists (p : ℕ) (hp : p.Prime) :
    ∃ q : ℕ, q.Prime ∧ q ∣ 6 ∧ ¬ q ∣ p ∧ (q = 2 ∨ q = 3) := by
  rcases composite_six_has_foreign_prime p hp with h2 | h3
  · exact ⟨2, Nat.prime_two, ⟨3, rfl⟩, h2, Or.inl rfl⟩
  · exact ⟨3, Nat.prime_three, ⟨2, rfl⟩, h3, Or.inr rfl⟩

/-!
**The foreign-gate obstruction, formalised.**  The polynomial method runs over a single field; `AC⁰[6]` always presents
a foreign `MOD_q` gate to that field (`acc6_foreign_prime_exists`, the `2 ≠ 3` root); and the proved general-`q`
Razborov–Smolensky bound shows that foreign gate has **no** low-degree approximation
(`foreign_mod_no_lowDegree_approx`).  So the *single* open socket `PolynomialMethodApproximation` cannot be discharged
for composite modulus the way it is for a single prime — the technique stalls exactly there.  This is the honest, formal
statement of why RS does not extend to the composite barrier; it is **not** a lower bound against `AC⁰[6]` and **not** a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ForeignGateObstruction

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ForeignGateObstruction.foreign_mod_no_lowDegree_approx
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ForeignGateObstruction.composite_six_has_foreign_prime
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ForeignGateObstruction.acc6_foreign_prime_exists
