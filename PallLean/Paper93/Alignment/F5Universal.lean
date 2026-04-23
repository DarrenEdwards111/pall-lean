/-
  PallLean/Paper93/Alignment/F5Universal.lean

  Agent H8 (parallel, 8 of 10) — Alignment bridge between Agent F5's
  per-parameter `ambientInterfaceSpace_finrank_le_three`
  (in `PallLean/Paper93/Bridge/AmbientFinrank.lean`, commit `7091aa8`)
  and Agent G5's universal Prop
  `PallLean.Paper93.AgentF5_AmbientFinrankLeThree`
  (defined in `PallLean/Paper93/FinalDischarge.lean`, commit `9b4641d`).

  ## Scope

  This file does exactly one thing: it re-expresses Agent F5's
  per-parameter theorem as a direct inhabitant of G5's universal Prop
  `AgentF5_AmbientFinrankLeThree`. The universal Prop quantifies over
  `(M, n, hn, htb, hns)` with `hn : n ≥ 2`, whereas F5's ambient
  construction requires `n ≥ 4` (an injective `Fin 4 ↪ Fin n`). We
  therefore split on `4 ≤ n`:

    * If `4 ≤ n`: pick the canonical coordinate embedding
      `σ := Fin.castLEEmb hn4 : Fin 4 ↪ Fin n` (as in Agent F1's
      `embedAt`), and take `W τ := ambientInterfaceSpace n hn4 σ` for
      every `τ : ConstraintType`. Finite-dimensionality follows from
      `ambientInterfaceSpace_finite`; the ≤ 3 finrank bound is exactly
      Agent F5's `ambientInterfaceSpace_finrank_le_three`.

    * If `¬ 4 ≤ n` (i.e. `n ∈ {2, 3}` under G5's `n ≥ 2`): take
      `W τ := ⊥`. This is trivially finite-dimensional
      (`Module.Finite.bot`) and has finrank `0 ≤ 3` by `finrank_bot`.

  Both branches satisfy G5's two conjuncts
  `(∀ τ, Module.Finite ℚ ↥(W τ))` and `(∀ τ, finrank ℚ ↥(W τ) ≤ 3)`.

  ## Faithfulness

  The proof is a direct term-mode case split feeding the appropriate
  piece of Agent F5's ambient construction into G5's existential. No
  analytic content is simplified; the complexity of F5's ambient
  finrank argument lives intact in `ambientInterfaceSpace_finrank_le_three`
  via Agent A / F3 / F4. This file only performs a shape-level
  alignment and a single boundary case split on `4 ≤ n`.

  ## Axiom trace

  `#print axioms` at the end of this file should show only the
  kernel-level `propext`, `Classical.choice`, `Quot.sound` dependencies
  inherited from Mathlib, matching both F5 and G5.
-/

import PallLean.Paper93.Bridge.AmbientFinrank
import PallLean.Paper93.FinalDischarge
import Mathlib.Data.Fin.Embedding

open Module
open scoped BigOperators

namespace PallLean
namespace Paper93
namespace Alignment

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound
open PallLean.Paper93.Bridge

/-! ## Promotion of F5's per-parameter theorem to G5's universal Prop

Agent F5 delivers, for every `(n, hn4, σ)` with `hn4 : n ≥ 4` and
`σ : Fin 4 ↪ Fin n`, the ambient finrank bound

  `ambientInterfaceSpace_finrank_le_three :
      Module.finrank ℚ (ambientInterfaceSpace n hn4 σ) ≤ 3`

(see `PallLean/Paper93/Bridge/AmbientFinrank.lean`). G5's universal
Prop `AgentF5_AmbientFinrankLeThree` asks instead for existence of a
per-`ConstraintType` family `W` in `MvPolynomial (Fin n) ℚ` with

  `(∀ τ, Module.Finite ℚ ↥(W τ)) ∧ (∀ τ, finrank ℚ ↥(W τ) ≤ 3)`,

under the weaker binding hypothesis `hn : n ≥ 2`.

We bridge the two by:
  * taking `W τ := ambientInterfaceSpace n hn4 σ` when `4 ≤ n`
    (with `σ` the canonical `Fin.castLEEmb hn4`); and
  * taking `W τ := ⊥` when `¬ 4 ≤ n`, using the trivial
    finite-dimensionality and zero-dim fallback.

Both branches produce a family satisfying G5's two conjuncts, and the
existential is packaged accordingly. -/

/-- **Alignment: F5 per-parameter ⇒ G5's `AgentF5_AmbientFinrankLeThree`.**

    Promote Agent F5's `ambientInterfaceSpace_finrank_le_three` into
    G5's universal Prop, supplying a `W` family per parameter tuple
    `(M, n, hn, htb, hns)` with `n ≥ 2`. The proof is a boundary case
    split on `4 ≤ n`: when it holds, pick the F5 ambient construction;
    when it fails, fall back to `⊥` (finrank `0 ≤ 3`). -/
theorem F5_universal : PallLean.Paper93.AgentF5_AmbientFinrankLeThree := by
  intro M n hn htb hns
  classical
  by_cases hn4 : 4 ≤ n
  · -- Active branch: use the F5 ambient construction.
    refine
      ⟨fun _τ =>
          ambientInterfaceSpace n hn4 (Fin.castLEEmb hn4), ?_, ?_⟩
    · intro τ
      -- Finite-dimensionality of the F5 ambient space (F4 instance).
      exact ambientInterfaceSpace_finite n hn4 (Fin.castLEEmb hn4)
    · intro τ
      -- ≤ 3 finrank bound is exactly F5's theorem.
      exact ambientInterfaceSpace_finrank_le_three n hn4 (Fin.castLEEmb hn4)
  · -- Dormant branch: `n < 4`, fall back to ⊥.
    refine
      ⟨fun _τ => (⊥ : Submodule ℚ (MvPolynomial (Fin n) ℚ)), ?_, ?_⟩
    · intro τ
      -- `Module.Finite.bot` (mathlib's instance for ⊥ submodule).
      infer_instance
    · intro τ
      -- `finrank ⊥ = 0 ≤ 3`.
      have hbot :
          Module.finrank ℚ
              (⊥ : Submodule ℚ (MvPolynomial (Fin n) ℚ)) = 0 :=
        finrank_bot ℚ _
      rw [hbot]
      exact Nat.zero_le _

/-! ## Alias

Alternative name matching the task spec's mnemonic, useful when paired
with the final composition site in `Paper93/FinalDischarge.lean`. -/

/-- Alias of `F5_universal` under a descriptive name for clarity at
    the top-level `FinalDischarge` call site. -/
theorem agentF5_ambientFinrankLeThree_of_perParameter :
    PallLean.Paper93.AgentF5_AmbientFinrankLeThree :=
  F5_universal

-- **Axiom audit** — expected: kernel-only
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms F5_universal
#print axioms agentF5_ambientFinrankLeThree_of_perParameter

end Alignment
end Paper93
end PallLean
