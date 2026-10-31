import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer7ModqFamily

/-!
# The AC⁰[p] / approximate‑inverter class: restricted `InversionHardness` via Razborov–Smolensky

The previous restricted‑hardness classes (low‑degree algebraic, bounded‑crossing, bounded‑locality) were *exact*
combinatorial restrictions.  This file adds the genuinely harder **`AC⁰[p]` / approximate** inverter class,
discharged via the **Razborov–Smolensky approximation route** already formalized in the `Layer3/4/7` corpus:

* `Layer3` builds the low‑degree `F_p` polynomial that *approximates* any `AC⁰[p]` circuit on a `(1-ε)` fraction
  of inputs (`toPoly_eval_AC0p`, `genOrApprox_*`).
* `Layer4` proves the **no‑approximation** core: a `MOD_q` indicator (`q ≠ p`) is not in the span of low‑degree
  `F_p` polynomials on a large agreement set (`mod_q_indicators_false`, `mod_q_family_false`).
* `Layer7` assembles them into the circuit‑family lower bounds
  `modq_not_in_nonuniform_AC0p` and `parity_not_in_nonuniform_AC0p`.

An **`AC⁰[p]` inverter** is a constant‑depth, polynomially‑size‑bounded `AC⁰[p]` circuit family
(`AC0pFamily` + `IsPolyBounded`); it *correctly decides* a target language iff it `Computes` it.  Razborov–
Smolensky says no such family computes `MOD_q` or `PARITY` — so the `AC⁰[p]` (approximate‑polynomial) inverter
class is provably empty for those targets.

## Proved (reuses the formalized RS lower bounds; clean axioms, no `sorry`)

* `no_AC0p_inverter_modq` — no polynomially‑size‑bounded `AC⁰[p]` inverter decides `MOD_q` (`q ≠ p` primes).
* `no_AC0p_inverter_parity` — no polynomially‑size‑bounded `AC⁰[p]` inverter decides `PARITY` (`p` odd).
  Restricted `InversionHardness` for the `AC⁰[p]`/approximate‑polynomial class, **unconditional**, by the RS
  approximation route.

## Honest scope and the complementarity that *is* the wall

The heavy lifting (the RS approximation lemma + the no‑approximation counting) is the `Layer3/4/7` corpus; this
file connects it to the inverter frontier.  Two honest caveats:

1. **Target = `MOD_q` / `PARITY`, the RS‑native hard functions.**  These are exactly the functions easy in *some*
   algebra (`F_q`‑linear) yet hard for `AC⁰[p]` (`p ≠ q`).  Majority is also RS‑hard, but only `MOD_q`/`PARITY`
   are assembled at the family level in the corpus, so those are the honest targets here.
2. **Complementarity — no single proved predicate resists every class.**  `MOD_q` resists `AC⁰[p]` but is
   `F_q`‑*linear*, so it has a degree‑1 annihilator over `F_q` — it is algebraically *trivial*, the opposite of
   `Majority` (which has optimal algebraic immunity but whose `AC⁰[p]` hardness we did not separately assemble).
   The proved restricted classes — algebraic (`Majority`), `AC⁰[p]` (`MOD_q`/`PARITY`), bounded‑crossing,
   bounded‑locality — are **mutually incomparable**, and **no single predicate is proved to resist all of them
   at once**.  That simultaneous resistance — one explicit family hard for *every* poly‑time inverter — is
   exactly the global `InversionHardness` wall (`P ≠ NP`‑strength).  Each restricted class is a theorem; their
   conjunction over a single family is the open problem.
-/

namespace PallLean.Paper93.DeepMath.PathB.AC0pInverterHardness

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Layer7

/-- An **`AC⁰[p]` inverter** correctly decides the target language `L` iff its (constant‑depth,
polynomially‑size‑bounded) `AC⁰[p]` circuit family `Computes L`. -/
def IsAC0pInverter {p : ℕ} (F : Layer7.AC0pFamily p) (L : BoolLang) : Prop :=
  IsPolyBounded F.sizeBound ∧ F.Computes L

/-- **No `AC⁰[p]` inverter for `MOD_q` (proved — restricted `InversionHardness` via RS).**  For distinct primes
`p ≠ q`, no constant‑depth polynomially‑size‑bounded `AC⁰[p]` circuit family correctly decides the `MOD_q`
language.  The `AC⁰[p]` / approximate‑polynomial inverter class is provably empty for the `MOD_q` target —
unconditional, by the Razborov–Smolensky approximation route. -/
theorem no_AC0p_inverter_modq (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : ¬ q ∣ p)
    (F : Layer7.AC0pFamily p) : ¬ IsAC0pInverter F (modqLang q) := by
  rintro ⟨hpoly, hComp⟩
  exact modq_not_in_nonuniform_AC0p p q hpq F hpoly hComp

/-- **No `AC⁰[p]` inverter for `PARITY` (proved — restricted `InversionHardness` via RS).**  For `p` odd, no
constant‑depth polynomially‑size‑bounded `AC⁰[p]` circuit family correctly decides the `PARITY` language. -/
theorem no_AC0p_inverter_parity (p : ℕ) [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    (F : Layer7.AC0pFamily p) : ¬ IsAC0pInverter F parityLang := by
  rintro ⟨hpoly, hComp⟩
  exact parity_not_in_nonuniform_AC0p p hp2 F hpoly hComp

/-- **The `AC⁰[p]` inverter class is empty for `MOD_q` (existential form).**  No `AC⁰[p]` inverter decides
`MOD_q`. -/
theorem no_AC0p_inverter_exists_modq (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : ¬ q ∣ p) :
    ¬ ∃ F : Layer7.AC0pFamily p, IsAC0pInverter F (modqLang q) := by
  rintro ⟨F, hF⟩
  exact no_AC0p_inverter_modq p q hpq F hF

end PallLean.Paper93.DeepMath.PathB.AC0pInverterHardness

#print axioms PallLean.Paper93.DeepMath.PathB.AC0pInverterHardness.no_AC0p_inverter_modq
#print axioms PallLean.Paper93.DeepMath.PathB.AC0pInverterHardness.no_AC0p_inverter_parity
