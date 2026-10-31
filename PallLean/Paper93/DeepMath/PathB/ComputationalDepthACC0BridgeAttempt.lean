import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHolonomyHardEffectiveRank

/-!
# Attempting the open bridge directly — `ACC0LowRealizedGodelSPDP` / `NP ⊄ ACC⁰`

This is a direct attempt at the open bridge: *poly‑time / ACC⁰ ⇒ the realized charges have low effective cycle
rank on hard instances*.  That implication is `NP ⊄ ACC⁰`‑strength — a major open problem.  **This file does not
prove it.**  It pushes the holonomy effective‑rank method as far as it genuinely goes, extracts the real
(restricted) lower bound that falls out, and documents the exact wall.

## What the attempt genuinely yields (proved, clean axioms)

* `effectiveRank_gate_lower_bound` — **a real gate lower bound**: a `MOD q` circuit whose realized charges have
  effective cycle rank `≥ m` (i.e. realize `≥ 2^m` holonomy classes) and factor through `k` modular statistics
  must satisfy `2^m ≤ q^k` — so it needs `k ≥ m / log₂ q` gates.  Combined with `expander_realizedClasses_eq`
  (the expander charge family has rank `m`), this says: **realizing the expander charge family with `MOD q` gates
  requires `≥ m/log₂ q` gates** — a genuine, restricted, super‑logarithmic gate lower bound.
* `logGate_bridge_holds` — **the bridge, proved for the restricted log‑gate case**: a circuit using only
  `≤ log₂ n` modular gates has `≤ n^q` realized classes — *polynomial*, low effective rank.  So `O(log n)`‑gate
  modular circuits are provably on the tame side.
* `polyGate_counting_bound_ge_two_pow` — **the wall**: at `g = n` (polynomially many) gates the method's bound is
  `q^n ≥ 2^n` — exponential, vacuous.  The rank‑counting method gives no A1 control past `O(log n)` gates.

## The wall, stated honestly

The attempt produces a genuine lower bound in the **restricted charge‑realization model** (modular gates producing
charges) — high effective rank needs many gates — and proves the bridge for `O(log n)`‑gate circuits.  But it does
**not** reach `NP ⊄ ACC⁰`, for two precise reasons:

1. **Model gap.**  The bound is about *realizing a charge family* with modular gates, not about an ACC⁰ circuit
   *deciding an NP language*.  A real ACC⁰ SAT decider need not present its computation as a low‑gate modular
   charge realization; bridging that is the open structural content.
2. **The log→poly gate jump.**  The method proves tameness only for `O(log n)` gates (`logGate_bridge_holds`); at
   poly gates the counting bound is `2^{poly}` (`polyGate_counting_bound_ge_two_pow`), so it cannot show a
   *poly‑gate* ACC⁰ circuit keeps the realized charges low‑rank — which is exactly what `NP ⊄ ACC⁰` needs, and is
   false for the raw graph (ACC⁰ encodes expanders).

And even were both crossed, the PRF‑free naturalness ceiling (`…DynamicSPDPNaturalnessRange`) caps the method below
`P ≠ NP`.  So: the bridge attempt yields a real restricted gate lower bound and the tame log‑gate case, and stops
— honestly — at the poly‑gate / language‑decision wall, which is `NP ⊄ ACC⁰`.  Not proved; the wall is documented.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0BridgeAttempt

open PallLean.Paper93.DeepMath.PathB.HolonomyPSideControl
open PallLean.Paper93.DeepMath.PathB.HolonomyEffectiveRank

variable {V : Type*}

/-- **A real gate lower bound (proved).**  If a `MOD q` circuit's realized charges have effective cycle rank `≥ m`
(realize `≥ 2^m` holonomy classes) and factor through `k` modular statistics, then `2^m ≤ q^k`: it needs
`k ≥ m / log₂ q` gates.  The expander charge family (`expander_realizedClasses_eq`, rank `m`) thus needs
`≥ m/log₂ q` modular gates — a genuine super‑logarithmic lower bound in the charge‑realization model. -/
theorem effectiveRank_gate_lower_bound {ι : Type*} {m k q : ℕ} [NeZero q]
    (cycle : Fin m → Finset V) (chargeOf : ι → (V → ZMod 2)) (Inputs : Finset ι)
    (stat : ι → (Fin k → ZMod q)) (chargeFromStat : (Fin k → ZMod q) → (V → ZMod 2))
    (hfac : ∀ x, chargeOf x = chargeFromStat (stat x))
    (hrank : 2 ^ m ≤ realizedClasses cycle chargeOf Inputs) :
    2 ^ m ≤ q ^ k :=
  le_trans hrank (modular_layer_realized_le cycle chargeOf Inputs stat chargeFromStat hfac)

/-- Helper: `q^{log₂ n} ≤ n^q` (so a log‑gate modular bound is polynomial). -/
theorem pow_log_le_pow (n q : ℕ) (hn : 1 ≤ n) : q ^ (Nat.log 2 n) ≤ n ^ q := by
  calc q ^ (Nat.log 2 n)
      ≤ (2 ^ q) ^ (Nat.log 2 n) := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    _ = (2 ^ (Nat.log 2 n)) ^ q := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ n ^ q := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 (by omega)) q

/-- **The bridge, proved for the restricted `O(log n)`‑gate case.**  A modular circuit using only `≤ log₂ n` gates
realizes `≤ n^q` holonomy classes — polynomial, low effective rank.  So `O(log n)`‑gate modular circuits are
provably tame; the bridge holds there. -/
theorem logGate_bridge_holds {ι : Type*} {m q : ℕ} [NeZero q] (n : ℕ) (hn : 1 ≤ n)
    (cycle : Fin m → Finset V) (chargeOf : ι → (V → ZMod 2)) (Inputs : Finset ι)
    (stat : ι → (Fin (Nat.log 2 n) → ZMod q)) (chargeFromStat : (Fin (Nat.log 2 n) → ZMod q) → (V → ZMod 2))
    (hfac : ∀ x, chargeOf x = chargeFromStat (stat x)) :
    realizedClasses cycle chargeOf Inputs ≤ n ^ q :=
  le_trans (modular_layer_realized_le cycle chargeOf Inputs stat chargeFromStat hfac)
    (pow_log_le_pow n q hn)

/-- **The wall (proved): at polynomially many gates the counting bound is exponential.**  At `g = n` gates the
method's upper bound `q^n` is `≥ 2^n` — vacuous for A1.  The rank‑counting method gives no polynomial control past
`O(log n)` gates, which is exactly the log→poly gap where `NP ⊄ ACC⁰` lives. -/
theorem polyGate_counting_bound_ge_two_pow (n q : ℕ) (hq : 2 ≤ q) : 2 ^ n ≤ q ^ n :=
  Nat.pow_le_pow_left hq n

end PallLean.Paper93.DeepMath.PathB.ACC0BridgeAttempt

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BridgeAttempt.effectiveRank_gate_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BridgeAttempt.logGate_bridge_holds
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BridgeAttempt.polyGate_counting_bound_ge_two_pow
