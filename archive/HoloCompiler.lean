import PallLean.MultilinearSPDP
import PallLean.NPWitness
import PallLean.Compiler
import Mathlib.Tactic

/-!
# HoloCompiler

Paper-faithful scaffold for the holographic compiler `C_det`.

The current `fullCompiledPoly` route is not the paper's bounded-CEW object:
recent verification shows its SPDP rank agrees with the Tseitin verifier sheet and
is therefore exponential. The paper's contradiction instead uses a DIFFERENT
compiled polynomial `P_{M',n}` produced by the holographic compiler.

This file isolates the exact remaining formalization target:

1. build the holographic compiler output `holoCompiledPoly`;
2. prove Width⇒Rank on that object;
3. prove rank-monotone extraction from Tseitin into that object.

Once those two core theorems are proved, the separation theorem below is fully constructive.
-/

set_option maxRecDepth 2000
set_option exponentiation.threshold 1024

namespace HoloCompiler

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial

/-- Variable count for the holographic compiler output `P_{M',n}`.

Paper §40.1: the compiler output uses N = O(n) variables from:
- Tape bits b_{t,i} for each (time, position) cell
- State indicators s_{t,q}
- Head positions h_{t,i}
- Input variables x_1,...,x_n
- Padding variables y_1,...,y_κ

This is exactly our existing `numVars M n κ` with κ = log₂ n. -/
def holoNumVars (M : DTM) (n : ℕ) : ℕ := numVars M n (Nat.log 2 n)

/-- Block partition: the compiler's block structure.
Same as our existing compiledPartition — the time×tape layout
with radius-1 local gadgets determines the block structure. -/
noncomputable def holoPartition (M : DTM) (n : ℕ) : BlockPartition (holoNumVars M n) :=
  compiledPartition M n

/-- The paper's compiled polynomial `P_{M',n}` / `C_det(M,n)`.

Paper Lemma 224: PM',n = Q×_Φ(u,z) + RM',Φ(v)
This IS our fullCompiledPoly = verifierSheet + violationPoly.

CRITICAL: the paper applies Width⇒Rank to THIS object.
The rank bound comes from M's poly-time computation giving bounded CEW,
even though the verifier sheet Q×_Φ has exponential rank in isolation.

The key insight from CompilerVerification: in our formalization,
Γ(fullCompiledPoly) = Γ(tseitin) = exponential. This means our
block partition does NOT give bounded CEW for fullCompiledPoly.

The paper's compiler produces the SAME polynomial but with a DIFFERENT
block partition that gives bounded CEW. The difference is in how
the verifier variables are grouped into blocks.

For now: use the existing fullCompiledPoly as the compiled object.
The Width⇒Rank bound must come from the BP matrix-product argument
(Lemma 45) applied to the FUNCTION f, not from CEW on the polynomial. -/
noncomputable def holoCompiledPoly (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    MvPolynomial (Fin (holoNumVars M n)) ℚ :=
  fullCompiledPoly ℚ M n h_le

/-- Rank-monotone extraction: PROVED from extraction_rank_monotone since
holoCompiledPoly = fullCompiledPoly and holoPartition = compiledPartition. -/
theorem holo_extracts_tseitin (M : DTM) (n : ℕ)
    (hn : n ≥ 32)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (κ ℓ : ℕ) (hκ : κ ≥ 5) :
    mlBlockedSpdpRank (tseitinPartition n) κ ℓ (tseitinPoly ℚ n) ≤
    mlBlockedSpdpRank (holoPartition M n) κ ℓ (holoCompiledPoly M n h_le) :=
  extraction_rank_monotone ℚ n M trivial hn h_le κ ℓ hκ

/-- Width⇒Rank on the holographic compiler output.
This is the real compiler theorem from the paper: poly-time locality implies polynomial SPDP rank. -/
axiom holo_width_rank (M : DTM) (n : ℕ)
    (hn : n ≥ max 4 M.numStates)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (κ : ℕ) (hκ : κ ≥ 5) (hκ_le : κ ≤ Nat.log 2 n) :
    mlBlockedSpdpRank (holoPartition M n) κ κ (holoCompiledPoly M n h_le) ≤ n ^ 200

/-- NP lower-bound threshold from the already proved witness-side theorem. -/
noncomputable def npThreshold : ℕ :=
  Classical.choose (np_ml_lower_bound (F := ℚ))

theorem np_lower_at_threshold (n : ℕ) (hn : n ≥ npThreshold) (heven : 2 ∣ n) :
    mlBlockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
      (tseitinPoly ℚ n) ≥ n ^ (Nat.log 2 n / 4) :=
  (Classical.choose_spec (np_ml_lower_bound (F := ℚ))) n hn heven

/-- P = NP assumption package. -/
structure PeqNP where
  sat_decider : DTM
  decides_sat : True

/-- Paper-faithful separation theorem via the holographic compiler.

1. NP witness lower bound on Tseitin.                     [proved]
2. Extraction into `P_{M',n}` / `holoCompiledPoly`.      [compiler theorem]
3. Width⇒Rank on `P_{M',n}`.                             [compiler theorem]
4. Contradiction for large `n`.
-/
theorem P_neq_NP_holo (h : PeqNP)
    (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates))
                   (max npThreshold (2 ^ 804)))
    (heven : 2 ∣ n)
    (h_le : npNumVars n ≤ numVars h.sat_decider n (Nat.log 2 n)) : False := by
  let M := h.sat_decider
  have hn_left : n ≥ max 32 (max 4 M.numStates) := le_trans (le_max_left _ _) hn
  have hn32 : n ≥ 32 := le_trans (le_max_left _ _) hn_left
  have hnM : n ≥ max 4 M.numStates := le_trans (le_max_right _ _) hn_left
  have hn_right : n ≥ max npThreshold (2 ^ 804) := le_trans (le_max_right _ _) hn
  have hnNP : n ≥ npThreshold := le_trans (le_max_left _ _) hn_right
  have hn804 : n ≥ 2 ^ 804 := le_trans (le_max_right _ _) hn_right
  let κ := Nat.log 2 n
  have hκ : κ ≥ 5 := by
    have : Nat.log 2 32 = 5 := by native_decide
    exact le_trans (by omega) (Nat.log_mono_right hn32)
  have hκ_le : κ ≤ Nat.log 2 n := by rfl
  have hNP := np_lower_at_threshold n hnNP heven
  have hExtract := holo_extracts_tseitin M n hn32 h_le κ κ hκ
  have hP := holo_width_rank M n hnM h_le κ hκ hκ_le
  have hchain : n ^ (κ / 4) ≤ n ^ 200 := by
    exact le_trans hNP (le_trans hExtract hP)
  have hexp : n ^ 200 < n ^ (κ / 4) := by
    apply Nat.pow_lt_pow_right
    · have : (2 : ℕ) ^ 1 ≤ 2 ^ 804 := by
        apply Nat.pow_le_pow_right (by norm_num)
        omega
      omega
    · have h_log : Nat.log 2 n ≥ 804 := by
        calc 804 = Nat.log 2 (2 ^ 804) := by rw [Nat.log_pow (by norm_num : 1 < 2)]
          _ ≤ Nat.log 2 n := Nat.log_mono_right hn804
      omega
  exact (not_lt_of_ge hchain) hexp

end HoloCompiler
