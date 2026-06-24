import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneUEncode
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EffSimRuntime

/-!
# Kleene interpreter project — step 1: the frozen target theorem (PROVED skeleton)

Per the roadmap, fix the exact target before the dispatch coding.  A configuration `(k, code, n)` is
encoded as `encConfig k (u.enc) n = Nat.pair k (Nat.pair u.enc n)`.  The two North-Star statements:

  `UniversalCodeCorrect` — `∃ U : Code, ∀ k u n, U.eval (encConfig k u.enc n) = Code.evaln k u.toCode n`:
    a single concrete `Code` `U` simulating `evaln` for every code (via the `UCode` mirror) and fuel.
  `UniversalCodeRuntimePoly` — `∃ U P, ∀ k u n (halting), runtimeOf U (encConfig k u.enc n) ≤ P k (u.enc + n)`:
    `U`'s own fuel is polynomially bounded — the efficient-simulation overhead.

These are the objects the whole EffSim machinery feeds: discharging `UniversalCodeRuntimePoly` (via the
explicit `U` + `runtimeOf_prec_le_linear` + `config_encode_le`) yields `DiagRuntimePolyBounded` and the
efficient hierarchy.

  `encConfig` — the config encoding; `encConfig_injective` — it is faithful (sanity).

## What is proved (clean axioms, no `sorry`)

* `encConfig`, `encConfig_injective` — the config encoding and its faithfulness.
* `UniversalCodeCorrect`, `UniversalCodeRuntimePoly` — the frozen target statements (definitions).

## Honest scope

Step 1: the target is frozen and the config encoding is faithful.  The targets themselves are **not**
proved — they require the explicit interpreter `U` (steps 4–7).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneTarget

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneUCode (UCode)
open PallLean.Paper93.DeepMath.PathB.ACC0EffSimRuntime (runtimeOf)

/-- Encode a configuration `(fuel k, code-encoding ec, input n)` as a single natural number. -/
def encConfig (k ec n : ℕ) : ℕ := Nat.pair k (Nat.pair ec n)

/-- **The config encoding is faithful (proved).** -/
theorem encConfig_injective {k₁ ec₁ n₁ k₂ ec₂ n₂ : ℕ}
    (h : encConfig k₁ ec₁ n₁ = encConfig k₂ ec₂ n₂) : k₁ = k₂ ∧ ec₁ = ec₂ ∧ n₁ = n₂ := by
  unfold encConfig at h
  rw [Nat.pair_eq_pair] at h
  obtain ⟨hk, hp⟩ := h
  rw [Nat.pair_eq_pair] at hp
  exact ⟨hk, hp.1, hp.2⟩

/-- **Target (correctness): a concrete universal `Code`.**  Frozen statement (roadmap step 1). -/
def UniversalCodeCorrect : Prop :=
  ∃ U : Code, ∀ (k : ℕ) (u : UCode) (n : ℕ),
    U.eval (encConfig k u.enc n) = Code.evaln k u.toCode n

/-- **Target (runtime): the universal `Code` runs in polynomial fuel.**  Frozen statement (roadmap step 1).
The runtime is taken over configs on which `U` halts (`hU`). -/
def UniversalCodeRuntimePoly : Prop :=
  ∃ (U : Code) (P : ℕ → ℕ → ℕ), ∀ (k : ℕ) (u : UCode) (n : ℕ)
    (hU : ∃ m, (Code.evaln m U (encConfig k u.enc n)).isSome),
    runtimeOf U (encConfig k u.enc n) hU ≤ P k (u.enc + n)

/-!
**Step 1 proved (target frozen).**  `encConfig` is faithful, and the two North-Star targets are stated.
Discharging them requires the explicit interpreter `U` (steps 4–7); the EffSim machinery (cost model,
`runtimeOf_prec_le_linear`, `config_encode_le`) is built to feed exactly the runtime target.  Nothing here
is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneTarget

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneTarget.encConfig_injective
