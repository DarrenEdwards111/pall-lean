import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Smolensky
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4Capstone
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4PadSubcircuits
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0QuantBridgeWiring

/-!
# Prime `AC⁰[p]` capstone — the genuinely-proved restricted circuit lower bound

This file collects, under clean citable names, the **unconditional, `sorry`-free, custom-axiom-free**
restricted circuit lower bounds the prime Razborov–Smolensky route establishes: `PARITY ∉ AC⁰[p]` and
`MOD_q ∉ AC⁰[p]` for an odd prime `p` (and, for `MOD_q`, a distinct prime `q`). It also re-exports the
now-discharged quantitative bridge (`QuantitativeDepthBound`), so the prime polynomial-method assembly has
**no remaining socket** but the Smolensky wall — which is itself a theorem for prime `q`.

Each capstone name is verified by `#print axioms` to depend on **only** `propext`, `Classical.choice`,
`Quot.sound` — in particular on **none** of the arc's separation-strength axioms (`beigelTarui_faithful`,
`williams_decider_in_NEXP`) or the SPDP/gauge axioms. These are complete proofs, not conditional shells.

## The capstone theorems (all PROVED, clean-axiom, no `sorry`)

* **`parity_not_ac0p`** (`= Layer3.parity_function_lower_bound`) — any `AC⁰[p]` circuit (`p` odd prime,
  all mod-gates of modulus `p`) of depth `≤ d` on `2m+1` inputs that computes the Boolean parity function
  has, for every `t ≥ 1` with `8·((p-1)t)^{2d} ≤ m`, strictly more than `p^t/4` subcircuits — i.e.
  `2^{Ω(n^{1/2d})}` size. The classical Razborov–Smolensky theorem, from scratch.
* **`mod_q_not_ac0p_indicators`** (`= Layer4.mod_q_indicators_false`) — for distinct primes `p ≠ q`, over
  `K = 𝔽_{p^{q-1}}`, no family of `q` `AC⁰[p]` circuits can compute the residue indicators
  `[#ones ≡ j (mod q)]` within the band-margin window `16·((p-1)t)^{2d} < 2m+3` and size `4q·#sub ≤ p^t`.
  Since `MOD_q = [#ones ≡ 0]` is the `j=0` member, this is `MOD_q ∉ AC⁰[p]` (general `q`).
* **`mod_q_not_ac0p_literal`** (`= Layer4.mod_q_family_false`) — the same separation driven by a *literal*
  `MOD_q ∈ AC⁰[p]` family (via `padTrue`), size `4q·(#sub + (2m+1+q)) ≤ p^t`.
* **`quantitative_bridge`** (`= ACC0QuantBridgeWiring.quantitativeDepthBound_of_circ`) — the discharged
  polynomial-method bridge: every `MOD`-free `Circ` yields `QuantitativeDepthBound _ (t^{cdepth C}) E` with
  `2^t·E ≤ size C · 2^n`. Formerly a socket; now a theorem.

## Honest scope

These are **restricted-class** lower bounds — against `AC⁰[p]` for a *prime* `p`, the class where the
polynomial method has a genuine low-degree handle. They are real classical circuit lower bounds, proved
end-to-end. They are **not** `NEXP ⊄ ACC⁰` (composite modulus / Williams' algorithmic method — the open
`CarryRefinementCrossing` frontier) and **not** `P ≠ NP` (which needs a non-natural separating invariant
that no route in this repo supplies). Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`. See
`PRIME_ACC0_CAPSTONE.md` for the full proved-vs-conditional ledger.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0PrimeCapstone

/-- `PARITY ∉ AC⁰[p]` (odd prime `p`): a depth-`d`, parity-computing `AC⁰[p]` circuit on `2m+1` inputs has
`> p^t/4` subcircuits for `t` in the Smolensky window. Classical Razborov–Smolensky, proved from scratch. -/
alias parity_not_ac0p := PallLean.Paper93.DeepMath.PathB.Layer3.parity_function_lower_bound

/-- `MOD_q ∉ AC⁰[p]` (distinct primes `p ≠ q`), residue-indicator form: no `q`-family of small `AC⁰[p]`
circuits computes all residue indicators `[#ones ≡ j (mod q)]`; `MOD_q` is the `j = 0` member. -/
alias mod_q_not_ac0p_indicators := PallLean.Paper93.DeepMath.PathB.Layer4.mod_q_indicators_false

/-- `MOD_q ∉ AC⁰[p]`, literal-family form: no literal `MOD_q ∈ AC⁰[p]` family of the given size/depth
exists (assembled via `padTrue` from the indicator separation). -/
alias mod_q_not_ac0p_literal := PallLean.Paper93.DeepMath.PathB.Layer4.mod_q_family_false

/-- The discharged quantitative polynomial-method bridge: every `MOD`-free `Circ` yields a
`QuantitativeDepthBound` with degree `t^{cdepth}` and error `2^t·E ≤ size·2^n`. Formerly a socket. -/
alias quantitative_bridge := PallLean.Paper93.DeepMath.PathB.ACC0QuantBridgeWiring.quantitativeDepthBound_of_circ

end PallLean.Paper93.DeepMath.PathB.ACC0PrimeCapstone

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimeCapstone.parity_not_ac0p
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimeCapstone.mod_q_not_ac0p_indicators
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimeCapstone.mod_q_not_ac0p_literal
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimeCapstone.quantitative_bridge
