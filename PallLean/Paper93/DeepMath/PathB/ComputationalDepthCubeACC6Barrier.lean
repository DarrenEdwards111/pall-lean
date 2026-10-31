import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCubeApproxBridge

/-!
# The composite `MOD_6` / `ACC⁰[6]` barrier: why the `AC⁰[p]` easy side does not extend

`PARITY ∉ AC⁰[p]` worked because the two RS halves fit together *over a single prime field `F_p`*: parity is high
approximate degree over `F_p` (hard side), while every `AC⁰[p]` gate — including the `MOD_p` gate — is **low** approximate
degree over `F_p` (easy side, `lowApproxDeg_ac0p`; the `MOD_p` gate flattens by Fermat, repo
`nframeComplexity_charModAndFn_le`).  This file records — as a *proved barrier*, not a crossing — why that structure
**breaks** for the composite modulus `6`.

`MOD_6 = MOD_2 ∧ MOD_3` (repo `mod6_eq_mod2_and_mod3`, CRT).  A `MOD_6` gate is a legitimate `ACC⁰[6]` gate, but it does
**not** flatten over any single prime field:

* over `F_p` with `p` coprime to `6` (its natural arithmetization field, carrying an order-`6` root `ω`), the `MOD_6`
  gate is the *full-support* character `omegaFn ω`, which has **high** approximate degree — proved below;
* over `char 2` the `MOD_3` factor is coprime to the characteristic and is high degree; over `char 3` the `MOD_2` factor
  is (repo `composite_middle_no_lowdeg_flatten`, `two_fields_blindspot`).

So there is **no single field over which all of `MOD_6`'s structure is low degree** — the `AC⁰[p]` easy-side mechanism
(*every gate is low approximate degree over the working field*) has no analogue for `ACC⁰[6]`.

  **`not_lowApproxDeg_mod6`** — over a field with an order-`6` root, the `MOD_6` gate has **no** degree-`< ⌈n/2⌉`
        polynomial agreeing with it everywhere: it is high approximate degree (`q = 6` instance of
        `not_lowApproxDeg_omegaFn`).
  **`acc6_easySide_gate_not_low`** — hence there is an `ACC⁰[6]` gate (`MOD_6`) that is *not* low approximate degree; the
        easy side `lowApproxDeg_ac0p` does not extend to `ACC⁰[6]`.

## Honest scope — this is the barrier, not a lower bound

`MOD_6 ∉ ACC⁰[6]` — indeed **any** explicit `ACC⁰[6]` lower bound — is a **major open problem** (the frontier the whole
arc keeps reaching; only `NEXP ⊄ ACC⁰` is known, by Williams, via non-RS techniques).  This file does **not** prove any
separation.  It proves the *precise obstruction*: the Razborov–Smolensky easy side is single-field, and `MOD_6` refuses to
be low degree over any single field — so the method that gives `PARITY ∉ AC⁰[p]` provably cannot be pushed to `ACC⁰[6]`.
Crossing it needs a fundamentally different idea (a measure bounded on `ACC⁰[6]` despite its high-degree gates), which is
`P≠NP`-adjacent and is **not** built here (and not fakeable).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

open PallLean.Paper93.DeepMath.PathB.ModQReduction (omegaFn)

variable {n : ℕ} {F : Type*} [Field F]

/-- **The `MOD_6` gate is high approximate degree (proved)**: over a field with an order-`6` root `ω`, no degree-`< ⌈n/2⌉`
polynomial agrees with the `MOD_6` gate (`omegaFn ω`) on every input.  This is the `q = 6` instance of
`not_lowApproxDeg_omegaFn` — the composite gate is *not* low degree over its arithmetization field, unlike the `MOD_p`
gate of `AC⁰[p]`. -/
theorem not_lowApproxDeg_mod6 [Fintype F] [DecidableEq F] (ω : F) (hω : orderOf ω = 6) {d : ℕ}
    (hd : d < n - n / 2) :
    ¬ LowApproxDeg (F := F) d Finset.univ (omegaFn ω (Finset.univ : Finset (Fin n))) :=
  not_lowApproxDeg_omegaFn ω hω (by norm_num) hd

/-- **The barrier (proved)**: there is an `ACC⁰[6]` gate — the `MOD_6` gate `omegaFn ω` — that is **not** low approximate
degree.  So the `AC⁰[p]` easy side (`lowApproxDeg_ac0p`: every gate is low approximate degree over the working field) has
**no** analogue for `ACC⁰[6]`.  This is the Razborov–Smolensky obstruction to `ACC⁰[6]`, in the cube measure's language —
a barrier, *not* a separation. -/
theorem acc6_easySide_gate_not_low [Fintype F] [DecidableEq F] (ω : F) (hω : orderOf ω = 6)
    {d : ℕ} (hd : d < n - n / 2) :
    ∃ f : (Fin n → Bool) → F, ¬ LowApproxDeg (F := F) d Finset.univ f :=
  ⟨omegaFn ω (Finset.univ : Finset (Fin n)), not_lowApproxDeg_mod6 ω hω hd⟩

end PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.not_lowApproxDeg_mod6
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.acc6_easySide_gate_not_low
