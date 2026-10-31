import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameFpDegree

/-!
# The composite / mixed MOD wall, formalised

The `F_p`-degree dynamic-SPDP handles `AC⁰[p]` for a *single* prime: `MOD_p` is degree `≤ p-1`
(`NFrameFpDegree`), AND/OR compose at `×(p-1)` per gate (`NFrameFpANDOR`), amplified to error `p^{-t}`
(`NFrameFpAmplify`).  The one remaining wall is **composite / mixed moduli**.  This file makes that wall
precise and *proves the obstruction* — it does **not** cross it (crossing it via the polynomial method would be
an ACC⁰ lower bound, which is exactly what the polynomial method cannot deliver; `NEXP ⊄ ACC⁰` required
Williams' algorithmic method instead).

## What the wall is

Two theorems, both about `MOD_m` viewed as a function of the input's Hamming weight.

* **Composite = conjunction at different primes** (`modGate_mul_coprime`).  For coprime `a, b`,
  `MOD_{ab} = MOD_a ∧ MOD_b`, by CRT (`ab ∣ n ↔ a ∣ n ∧ b ∣ n`).  So `MOD_{pq}` for distinct primes `p, q` is
  `MOD_p ∧ MOD_q` — it demands *both* moduli simultaneously.

* **The `F_p` construction is characteristic-locked** (`symForm_char_locked`).  The Razborov–Smolensky building
  block over `F_p` is the symmetric linear form `symForm z = Σᵢ zᵢ`, which equals `(popcount z : F_p)` and hence
  depends only on `popcount z mod p`.  A function of `symForm` therefore *cannot distinguish* inputs with equal
  weight mod `p` — and `MOD_q` (for `q ∤ p`) does distinguish them (weight `0` vs weight `p`).  So **no function
  of the `F_p` symmetric form computes `MOD_q`**, while it *does* compute `MOD_p` (`symForm_computes_MODp`).

## The wall (`composite_mod_wall`)

Combining: for distinct primes `p, q`, `MOD_{pq} = MOD_p ∧ MOD_q`, and over `F_p` the symmetric construction
computes `MOD_p` but provably **not** `MOD_q` (dually over `F_q`).  So no single prime field's symmetric-form
construction computes the composite gate — the polynomial/degree method is field-specific and cannot span two
primes at once.  This is precisely why `AC⁰[p]` falls to the polynomial method but full `ACC⁰` does not.

## Honest scope

A rigorous formalisation of the composite-MOD obstruction (CRT decomposition + characteristic-locking of the
`F_p` symmetric form).  It proves **no** ACC⁰ lower bound and does **not** cross the wall — it explains why the
polynomial method cannot.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameCompositeMODWall

open PallLean.Paper93.DeepMath.PathB.NFrameFpDegree

/-- The `MOD_m` gate as a function of the input: fires iff the Hamming weight is `≡ 0 (mod m)`. -/
def modGate (m : Nat) {k : Nat} (z : Fin k → Bool) : Bool := decide (weight z % m = 0)

/-! ## Composite = conjunction of coprime factors (CRT) -/

/-- **CRT decomposition.**  For coprime `a, b`, `MOD_{ab} = MOD_a ∧ MOD_b`. -/
theorem modGate_mul_coprime {k : Nat} (a b : Nat) (hab : Nat.Coprime a b) (z : Fin k → Bool) :
    modGate (a * b) z = (modGate a z && modGate b z) := by
  have hiff : (a * b) ∣ weight z ↔ (a ∣ weight z ∧ b ∣ weight z) :=
    ⟨fun h => ⟨dvd_trans (dvd_mul_right a b) h, dvd_trans (dvd_mul_left b a) h⟩,
      fun ⟨hda, hdb⟩ => hab.mul_dvd_of_dvd_of_dvd hda hdb⟩
  have key : (weight z % (a * b) = 0) ↔ (weight z % a = 0 ∧ weight z % b = 0) :=
    Iff.trans (Nat.dvd_iff_mod_eq_zero (m := a * b) (n := weight z)).symm
      (Iff.trans hiff (and_congr (Nat.dvd_iff_mod_eq_zero (m := a) (n := weight z))
        (Nat.dvd_iff_mod_eq_zero (m := b) (n := weight z))))
  simp only [modGate]
  rw [decide_eq_decide.mpr key, Bool.decide_and]

section
variable (p : Nat) [Fact p.Prime]

/-! ## The `F_p` symmetric form is characteristic-locked -/

/-- The symmetric linear form `Σᵢ zᵢ` over `F_p`. -/
def symForm {k : Nat} (z : Fin k → Bool) : ZMod p := ∑ i, boolToZMod p (z i)

/-- The symmetric form is the Hamming weight, cast into `F_p`. -/
theorem symForm_eq_weight {k : Nat} (z : Fin k → Bool) : symForm p z = (weight z : ZMod p) := by
  simp only [symForm, boolToZMod, weight]
  rw [Finset.sum_boole]

/-- **The lock.**  Inputs with equal weight `mod p` have equal symmetric form — so any function of `symForm`
cannot tell them apart. -/
theorem symForm_eq_of_modEq {k : Nat} (x y : Fin k → Bool) (h : weight x ≡ weight y [MOD p]) :
    symForm p x = symForm p y := by
  rw [symForm_eq_weight, symForm_eq_weight]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h

/-- **`F_p` computes its own modulus.**  `MOD_p` is a function of the symmetric form (`s = 0`). -/
theorem symForm_computes_MODp {k : Nat} (z : Fin k → Bool) :
    modGate p z = decide (symForm p z = 0) := by
  simp only [modGate, symForm_eq_weight]
  exact decide_eq_decide.mpr
    (Iff.trans Nat.dvd_iff_mod_eq_zero.symm (ZMod.natCast_eq_zero_iff (weight z) p).symm)

/-- **The characteristic lock.**  For `q ∤ p`, **no** function of the `F_p` symmetric form computes `MOD_q`:
the all-`0` input (weight `0`) and the all-`1` input (weight `p`) have equal symmetric form but differ under
`MOD_q`. -/
theorem symForm_char_locked (q : Nat) (hq : ¬ q ∣ p) :
    ¬ ∃ g : ZMod p → Bool, ∀ z : Fin p → Bool, modGate q z = g (symForm p z) := by
  rintro ⟨g, hg⟩
  have hx : weight (fun _ : Fin p => false) = 0 := by simp [weight]
  have hy : weight (fun _ : Fin p => true) = p := by simp [weight]
  have hsym : symForm p (fun _ : Fin p => false) = symForm p (fun _ : Fin p => true) := by
    apply symForm_eq_of_modEq
    rw [hx, hy]
    exact (Nat.modEq_zero_iff_dvd.mpr (dvd_refl p)).symm
  have h1 : modGate q (fun _ : Fin p => false) = true := by simp [modGate, hx]
  have h2 : modGate q (fun _ : Fin p => true) = false := by
    simp only [modGate, hy]
    exact decide_eq_false (fun hpq => hq (Nat.dvd_of_mod_eq_zero hpq))
  rw [hg] at h1 h2
  rw [hsym] at h1
  rw [h1] at h2
  exact Bool.noConfusion h2

/-! ## The wall -/

/-- **The composite / mixed MOD wall.**  For distinct primes `p, q`: `MOD_{pq} = MOD_p ∧ MOD_q`, and over `F_p`
the symmetric-form construction computes `MOD_p` but **cannot** compute `MOD_q`.  So the composite gate demands
two different primes at once, and no single prime field's symmetric-form (Razborov–Smolensky) construction spans
both — the polynomial/degree method is characteristic-locked.  This is the obstruction that keeps the method at
`AC⁰[p]` and forced `NEXP ⊄ ACC⁰` to use Williams' algorithmic method instead. -/
theorem composite_mod_wall (q : Nat) [Fact q.Prime] (hpq : p ≠ q) :
    (∀ (k : Nat) (z : Fin k → Bool), modGate (p * q) z = (modGate p z && modGate q z))
      ∧ (∀ (k : Nat) (z : Fin k → Bool), modGate p z = decide (symForm p z = 0))
      ∧ (¬ ∃ g : ZMod p → Bool, ∀ z : Fin p → Bool, modGate q z = g (symForm p z)) := by
  refine ⟨fun k z => ?_, fun k z => symForm_computes_MODp p z, ?_⟩
  · exact modGate_mul_coprime p q ((Nat.coprime_primes Fact.out Fact.out).mpr hpq) z
  · refine symForm_char_locked p q (fun hqp => hpq ?_)
    exact ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp hqp).symm

end

end PallLean.Paper93.DeepMath.PathB.NFrameCompositeMODWall

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameCompositeMODWall.modGate_mul_coprime
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameCompositeMODWall.symForm_char_locked
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameCompositeMODWall.composite_mod_wall
