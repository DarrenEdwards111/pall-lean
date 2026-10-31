import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ShallowAllUncond
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModComposition

/-!
# Step 3 (DNF fragment): a random restriction makes the DNF control shallow

`…ACC0OracleControl` reduced an `AC⁰` control over `MOD`-oracle leaves to a decision tree and proved: control with
decision-tree depth `d` ⇒ searchable in `≤ 2^d` cells.  The deterministic depth was `m` (the trivial complete tree).
This file supplies HAL's **step 3** for the DNF fragment: a *random restriction* of the control's oracle positions
makes its canonical decision tree **shallow** (depth `< s`) — the Håstad switching collapse — which the existing
**fully-discharged** switching lemma `Depth3.exists_shallow_all_tight_uncond` already proves (no reconstruction
hypotheses, only per-term width `≤ w` and clause-count `≤ M` and the union-bound smallness condition).

Composing the shallow tree with the `MOD` gates as oracles (`acc0_over_mod_searchable`) gives: **there is a
position-restriction `ρ` under which the (collapsed) DNF control composed with the `MOD` oracles is SAT-searchable in
`< 2^n`** whenever `s ≤ n`.  `canonicalDT` returns a `BoolDecisionTree` directly, so this composes with no extra bridge.

## What is proved (clean axioms, no `sorry`)

* `dnf_control_switching_searchable` — for a DNF control `D` over `k` oracle positions (width `≤ w`, `≤ M` clauses)
  meeting the switching union-bound condition, and `MOD` gates `gate : Fin k → ModGate n` with `s ≤ n`: there exists a
  position-restriction `ρ` such that `x ↦ (canonicalDT D F ρ).eval (gate-outputs)` is SAT-searchable in `< 2^n`.

## Honest scope — the position/`x` gap (the no-go's deeper form, NOT crossed)

The restriction `ρ : Restriction k = Fin k → Option Bool` fixes the **oracle-output positions**, not the `n` input
variables `x`.  The composed function plugs the gate outputs `gⱼ(x)` into the *position-restricted* tree — it is **not**
the original circuit `x ↦ D(gate(x))` restricted by an `x`-restriction, because the gate outputs are *determined* by
`x` and cannot be independently set to match `ρ`'s fixed positions.  So this is the switching collapse of the control
**at the oracle-position level** composed with the oracles — a genuine fragment result — and it does **not** yield an
`x`-level speedup of the original `ACC⁰` circuit.  Bridging the position-restriction to an `x`-restriction is exactly
the determined-not-independent obstruction (the no-go's deeper form), and is **not** done here; I do not fake it.  The
shallow tree computes the `ρ`-restricted DNF by `canonicalDT` soundness (cited from the switching arc, not re-proved).
Still the cell/observer model; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0DNFControlSwitching

open scoped Classical
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver
open PallLean.Paper93.DeepMath.PathB.ACC0ModComposition
open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting

variable {n : ℕ}

/-- **Step 3, DNF fragment (proved): a random restriction collapses the DNF control to a shallow tree, and composing
with the `MOD` oracles is SAT-searchable in `< 2^n`.**  The shallow restriction exists by the fully-discharged
switching lemma `exists_shallow_all_tight_uncond`; the composition is `acc0_over_mod_searchable`.  `ρ` restricts the
oracle *positions* (see the honest-scope note: the position/`x` gap is not crossed). -/
theorem dnf_control_switching_searchable {k : ℕ} {p : ℚ}
    (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s M : ℕ} [NeZero w] [NeZero M]
    (D : List (Clause k))
    (hw : ∀ T ∈ D, T.lits.length ≤ w) (hm : D.length ≤ M)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ) * (M : ℚ)) < 1)
    (hsmall : (((2 * p / (1 - p)) * (2 * (w : ℚ) * (M : ℚ))) ^ s
        / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (M : ℚ)))) < 1)
    (gate : Fin k → ModGate n) (hsn : s ≤ n) :
    ∃ ρ : Restriction k,
      ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (stat : (Fin n → Bool) → S) (g : S → Bool),
        (Satisfiable (fun x => BoolDecisionTree.eval (canonicalDT D F ρ) (fun j => (gate j).eval x)) ↔
            ∃ c ∈ Finset.univ.image stat, g c = true)
          ∧ (Finset.univ.image stat).card < 2 ^ n := by
  classical
  obtain ⟨ρ, hρ⟩ := exists_shallow_all_tight_uncond (F := F) hp0 hp3
    ({D} : Finset (List (Clause k)))
    (by intro g' hg'; rw [Finset.mem_singleton] at hg'; subst hg'; exact hw)
    (by intro g' hg'; rw [Finset.mem_singleton] at hg'; subst hg'; exact hm)
    hr1
    (by simp only [Finset.card_singleton, Nat.cast_one, one_mul]; exact hsmall)
  have hdepth : (canonicalDT D F ρ).depth < s := hρ D (Finset.mem_singleton_self D)
  have hreg : 2 ^ (canonicalDT D F ρ).depth < 2 ^ n :=
    Nat.pow_lt_pow_right (by norm_num) (lt_of_lt_of_le hdepth hsn)
  obtain ⟨S, fS, dS, stat, g, hsat, hcard⟩ := acc0_over_mod_searchable (canonicalDT D F ρ) gate hreg
  exact ⟨ρ, S, fS, dS, stat, g, hsat, hcard⟩

end PallLean.Paper93.DeepMath.PathB.ACC0DNFControlSwitching

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DNFControlSwitching.dnf_control_switching_searchable
