import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3ModulusBoundary

/-!
# Tier 3: the mixed-modulus frontier — `MOD_6 = MOD_2 ∧ MOD_3` over incompatible fields

Sockets 1–3 cap the polynomial method at single-prime `AC⁰[p]`: over `F_p`, `MOD_p` gates linearise
(`…Layer3ModulusBoundary`).  General `ACC⁰` allows **mixed/composite** moduli (`MOD_6`, `MOD_{10}`, …), and this
file formalises the genuine structural reason that is the frontier.

**The CRT decomposition.**  By coprimality `mod6_eq_mod2_and_mod3`: `c ≡ r (mod 6) ↔ (c ≡ r mod 2) ∧ (c ≡ r mod 3)`,
so a `MOD_6` detector is `AND(MOD_2 detector, MOD_3 detector)` — a *modulus-stratified* object.  Each component is
low-degree, but over a **different** field: `MOD_2` ∈ `V_1` over `F_2` (`mod2_detector_lowdeg_F2`), `MOD_3` ∈ `V_2`
over `F_3` (`mod3_detector_lowdeg_F3`), both instances of socket 3's Fermat linearisation.  The `F_p` statistic
`∑ boolToZMod p (x_i)` is exactly the count mod `p` (`fp_statistic_eq_count`), so a single-`F_p` observer sees only
one CRT component; the other (`MOD_3` over `F_2`, `MOD_2` over `F_3`) is high-degree (Smolensky, `…Layer4ModqChar`).
No single prime field linearises a mixed gate — the precise wall.

**The frontier.**  Capturing a mixed-modulus gate needs a *modulus-stratified / hybrid* observer, named here as the
open socket `MixedModulusStratifiedObserverSocket`.  Whether such an observer yields an `ACC⁰` lower bound is the
genuine frontier — and the route that crosses it is **not** more polynomial method but **Williams' algorithmic
method** (faster ACC⁰-SAT + the nondeterministic time hierarchy), i.e. the PathB SAT-speedup arc.

## What is proved (clean axioms, no `sorry`)

* `fp_statistic_eq_count` — `∑ boolToZMod p (x_i) = (count : ZMod p)` (the `F_p` statistic is count mod `p`).
* `mod6_eq_mod2_and_mod3` — **`MOD_6 = MOD_2 ∧ MOD_3`** (CRT decomposition of a mixed gate).
* `mod2_detector_lowdeg_F2`, `mod3_detector_lowdeg_F3` — each CRT component is low-degree over *its* prime field.

## Honest scope

The structural decomposition and the per-field low-degree of the components — true and proved.  The wall (no common
field; mixed-modulus lower bounds) is *delimited*, not faked: `MixedModulusStratifiedObserverSocket` is a named OPEN
target, and the genuine resolution is the algorithmic method, not this `F_p` machinery.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer3MixedModulus

open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.Layer3ModulusBoundary
open MvPolynomial

variable {n : ℕ}

/-- **The `F_p` statistic is the count mod `p` (proved).**  `∑_{i∈S} boolToZMod p (x_i)` equals the cast of the
number of `true` coordinates in `S` — so `F_p` arithmetic of the inputs sees the count only mod `p`. -/
theorem fp_statistic_eq_count (p : ℕ) (S : Finset (Fin n)) (x : Fin n → Bool) :
    (∑ i ∈ S, boolToZMod p (x i)) = ((S.filter (fun i => x i = true)).card : ZMod p) := by
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : x i = true <;> simp [boolToZMod, h]

/-- **The CRT decomposition of a mixed-modulus gate (proved): `MOD_6 = MOD_2 ∧ MOD_3`.**  A `MOD_6` detector on a
count `c` is the conjunction of the `MOD_2` and `MOD_3` detectors — the modulus-stratified structure of a composite
gate.  By coprimality of `2` and `3` (`Nat.modEq_and_modEq_iff_modEq_mul`). -/
theorem mod6_eq_mod2_and_mod3 (c r : ℕ) :
    decide (c ≡ r [MOD 6]) = (decide (c ≡ r [MOD 2]) && decide (c ≡ r [MOD 3])) := by
  have hiff : (c ≡ r [MOD 6]) ↔ ((c ≡ r [MOD 2]) ∧ (c ≡ r [MOD 3])) :=
    (Nat.modEq_and_modEq_iff_modEq_mul (a := c) (b := r) (show Nat.Coprime 2 3 by decide)).symm
  simp [hiff]

/-- **`MOD_2` is low-degree over `F_2` (proved): the detector lies in `V_1` over `F_2`.**  Instance of socket 3's
Fermat linearisation at `p = 2` (`p - 1 = 1`). -/
theorem mod2_detector_lowdeg_F2 (r : ZMod 2) :
    (fun x : Fin n → Bool =>
        eval (fun i => boolToZMod 2 (x i)) (modpIndicatorPoly 2 Finset.univ r))
      ∈ Submodule.span (ZMod 2)
        (Set.range (fun T : {T // T ∈ lowDegMonomials n (2 - 1)} => squarefreeEvalMonomial 2 T.1)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact modp_eval_mem_lowDegSpan 2 Finset.univ r

/-- **`MOD_3` is low-degree over `F_3` (proved): the detector lies in `V_2` over `F_3`.**  Instance of socket 3's
Fermat linearisation at `p = 3` (`p - 1 = 2`) — a *different* field from `MOD_2`'s. -/
theorem mod3_detector_lowdeg_F3 (r : ZMod 3) :
    (fun x : Fin n → Bool =>
        eval (fun i => boolToZMod 3 (x i)) (modpIndicatorPoly 3 Finset.univ r))
      ∈ Submodule.span (ZMod 3)
        (Set.range (fun T : {T // T ∈ lowDegMonomials n (3 - 1)} => squarefreeEvalMonomial 3 T.1)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact modp_eval_mem_lowDegSpan 3 Finset.univ r

/-- **(The named OPEN frontier socket.)**  A *single*-field low-effective-dimension observer that captures a
mixed-modulus `MOD_6` gate: a prime `p`, a degree `D`, and a function in `V_D` over `F_p` computing the `MOD_6`
detector on the cube.  Sockets 1–3 show each CRT component is low-degree only over its *own* prime field, and
`MOD_3` over `F_2` / `MOD_2` over `F_3` are high-degree (Smolensky) — so this socket is **not** discharged by the
`F_p`-polynomial method.  Capturing a mixed gate needs a modulus-stratified / hybrid observer, and whether that
yields a lower bound is the `ACC⁰` frontier (Williams' algorithmic method, not RS). -/
def MixedModulusStratifiedObserverSocket (n : ℕ) : Prop :=
  ∃ (p D : ℕ) (_hp : Fact p.Prime) (g : (Fin n → Bool) → ZMod p),
    g ∈ Submodule.span (ZMod p)
        (Set.range (fun T : {T // T ∈ lowDegMonomials n D} => squarefreeEvalMonomial p T.1))
      ∧ ∀ x : Fin n → Bool,
          g x = boolToZMod p (decide ((Finset.univ.filter (fun i => x i = true)).card ≡ 0 [MOD 6]))

end PallLean.Paper93.DeepMath.PathB.Layer3MixedModulus

#print axioms PallLean.Paper93.DeepMath.PathB.Layer3MixedModulus.fp_statistic_eq_count
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3MixedModulus.mod6_eq_mod2_and_mod3
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3MixedModulus.mod2_detector_lowdeg_F2
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3MixedModulus.mod3_detector_lowdeg_F3
