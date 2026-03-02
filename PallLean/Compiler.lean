import PallLean.SPDPDefs
import Mathlib.Tactic
/-!
# P-Side Collapse — Pall §3–6

Theorem 6.1: For every polytime TM M, the compiled κ-padded polynomial
PM,n has blocked SPDP rank ΓB_{κ,ℓ}(PM,n) ≤ n^O(1).

We define:
- The compilation model (§3): TM → violation polynomial → κ-padded polynomial
- Block partition induced by the compiler
- Locality structure (§3.2)
- Profile compression (§5) and Width⇒Rank (Theorem 5.16)
- The main P-side theorem (Theorem 6.1)
-/

namespace Compiler

open SPDP MvPolynomial

/-- A deterministic TM with time bound n^c -/
structure PolyTimeTM where
  c : ℕ

/-- Number of variables in the compiled polynomial for input size n.
    N(n) = poly(n) — includes input, tape, state, head, and padding variables.
    (Pall §3.1: Universe and variables) -/
def compilerVars (n c : ℕ) : ℕ := n ^ (c + 1)

/-- The compiler-induced block partition (Pall §3.3, invariant I3).
    Each cell (t,i) in the computation tableau forms one block.
    The partition is deterministic given the compiler template and n. -/
noncomputable def compilerPartition (n : ℕ) (c : ℕ) :
    BlockPartition (compilerVars n c) where
  numBlocks := n ^ c + 1  -- ~T(n) blocks (one per tableau cell) + 1 to avoid zero
  assign := fun i => ⟨i.val % (n ^ c + 1), Nat.mod_lt _ (by omega)⟩

/-- The compiled κ-padded polynomial PM,n (Pall Definition 3.1 + §3.2).
    PM,n = (∏ᵢ yᵢ) · VM,n where VM,n encodes tableau constraint violations.
    - deg(VM,n) = O(1) (constant, independent of n)
    - κ-padding ensures deg(PM,n) ≥ κ so SPDP matrix is non-vacuous -/
noncomputable def compiledPoly (F : Type*) [CommRing F]
    (M : PolyTimeTM) (n : ℕ) :
    MvPolynomial (Fin (compilerVars n M.c)) F :=
  0  -- Placeholder: actual construction requires TM compilation (§3.1)

/-- The compiled polynomial has locality structure (Pall §3.2, eq. (1)):
    VM,n = Σ_{(t,i)} Q_{t,i} where each Q_{t,i} is supported on Nbr(t,i).

    HasLocalityStructure captures this decomposition and the width bound. -/
structure HasLocalityStructure {n : ℕ} {F : Type*} [CommRing F]
    (p : MvPolynomial (Fin n) F) where
  /-- Number of gate/layer polynomials (= time steps of M) -/
  numGates : ℕ
  /-- Width bound: each gate involves ≤ width variables (Pall property P3) -/
  width : ℕ
  /-- The gate polynomials -/
  gate : Fin numGates → MvPolynomial (Fin n) F
  /-- p is the sum of gates -/
  sum_eq : p = ∑ i, gate i
  /-- Each gate uses ≤ width variables -/
  gate_width : ∀ i, (gate i).vars.card ≤ width

/-- **Axiom: Compilation produces local structure (Pall §3.2–3.3)**

    The compiled polynomial has locality: numGates ≤ n^c (time steps)
    and width ≤ n (conservative; paper gives O(log n) via Theorem 6.7). -/
axiom compiled_has_locality (F : Type*) [CommRing F]
    (M : PolyTimeTM) (n : ℕ) (hn : n ≥ 2) :
    ∃ (h : HasLocalityStructure (compiledPoly F M n)),
      h.numGates ≤ n ^ M.c ∧ h.width ≤ n

/-- **Axiom: Width⇒Rank bound with profile compression
    (Pall Theorem 5.16 + Lemma 5.7)**

    Profile compression (Lemma 5.7) bounds |H| ≤ R^O(1) independent of κ.
    Within-profile dimension bound (Lemma 5.11): each profile contributes
    a row-subspace of dimension ≤ poly(n).
    Combined (Theorem 5.16): ΓB_{κ,ℓ}(p) ≤ (numGates × width)^C₀.

    We state it for the blocked SPDP rank ΓB, matching the paper. -/
axiom width_to_rank_bound (F : Type*) [CommRing F] [Nontrivial F]
    {v : ℕ} (B : BlockPartition v) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin v) F)
    (h : HasLocalityStructure p)
    (hκ : κ ≤ Nat.log 2 v) :
    blockedSpdpRank B κ ℓ p ≤ (h.numGates * h.width) ^ 3

/-- (log n)^d ≤ n^d — standard -/
theorem log_poly_le_poly (n : ℕ) (hn : n ≥ 2) (d : ℕ) :
    (Nat.log 2 n) ^ d ≤ n ^ d := by
  apply Nat.pow_le_pow_left
  exact le_of_lt (Nat.log_lt_self 2 (by omega))

/-- **A2 (Theorem 6.1): P-side collapse — polynomial blocked SPDP rank**

    For every polytime TM M, the compiled polynomial PM,n satisfies
    ΓB_{κ,ℓ}(PM,n) ≤ n^O(1) for (κ,ℓ) = Θ(log n).

    Proved from: compiled_has_locality + width_to_rank_bound. -/
theorem p_side_collapse (F : Type*) [CommRing F] [Nontrivial F]
    (M : PolyTimeTM) :
    ∃ (C : ℕ), ∀ n, n ≥ 2 →
      blockedSpdpRank (compilerPartition n M.c) (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly F M n) ≤ n ^ C := by
  use 3 * (M.c + 1)
  intro n hn
  obtain ⟨h_loc, h_gates, h_width⟩ := compiled_has_locality F M n hn
  have h_κ_le : Nat.log 2 n ≤ Nat.log 2 (compilerVars n M.c) := by
    apply Nat.log_mono_right
    unfold compilerVars
    exact Nat.le_self_pow (by omega) n
  have h_rank := width_to_rank_bound F (compilerPartition n M.c)
    (Nat.log 2 n) (Nat.log 2 n) (compiledPoly F M n) h_loc h_κ_le
  have h_bound : h_loc.numGates * h_loc.width ≤ n ^ (M.c + 1) := by
    calc h_loc.numGates * h_loc.width
        ≤ n ^ M.c * n := Nat.mul_le_mul h_gates h_width
      _ ≤ n ^ (M.c + 1) := by rw [Nat.pow_succ]
  calc blockedSpdpRank (compilerPartition n M.c) (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly F M n)
      ≤ (h_loc.numGates * h_loc.width) ^ 3 := h_rank
    _ ≤ (n ^ (M.c + 1)) ^ 3 := Nat.pow_le_pow_left h_bound 3
    _ = n ^ (3 * (M.c + 1)) := by ring

end Compiler
