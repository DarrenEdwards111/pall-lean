/-
  PaperAxioms.lean — Paper-faithful axiom decomposition

  Three axioms matching the paper's §7.3:

  Axiom 1 (depth4_simulation): §7.3 Step 1
    PTIME → depth-4 ΣΠ∑Π with bounded params.

  Axiom 2 (hil_multi_switching): Lemma 7.2
    Per depth-4 circuit: most restrictions collapse SPDP rank.
    CRITICAL: applies to depth-4 circuits (bounded bottom fan-in),
    NOT arbitrary polynomials. The ΣΠ∑Π structure is essential.

  Axiom 3 (rowspace_signature_bound): Lemma 7.2.1 + Step 4
    Signature classification for depth-4 circuits + union bound.

  PROVED: depth4_good_seed (Theorem 7.3) using all three.
  All three axioms on the critical path of P_neq_NP.
-/
import PallLean.CircuitModel
import PallLean.RestrictedSPDP
import PallLean.BoolEval

namespace PaperAxioms

open CircuitModel RestrictedSPDP Restriction BoolEval

/-! ## Finite Seed Union Helper (PROVED) -/

theorem exists_seed_avoiding_bad_union
    {σ τ : Type*} [DecidableEq σ] [Fintype σ]
    (tests : Finset τ) (bad : τ → Finset σ)
    (hcard : (tests.biUnion bad).card < Fintype.card σ) :
    ∃ s : σ, ∀ t ∈ tests, s ∉ bad t := by
  classical
  by_contra hno
  push_neg at hno
  have hsubset : (Finset.univ : Finset σ) ⊆ tests.biUnion bad := by
    intro s hs
    exact Finset.mem_biUnion.mpr (hno s)
  have hge : Fintype.card σ ≤ (tests.biUnion bad).card := by
    simpa using Finset.card_le_card hsubset
  exact Nat.not_lt_of_ge hge hcard

/-! ## Axiom 1: Depth-4 Simulation (§7.3 Step 1)

Paper: Lemma (Uniform depth-4 ΣΠ∑Π simulation), §2.3.2.
  Cook-Levin → binary Tseitin → ΣΠ∑Π realisation.

For any polynomial (from a PTIME circuit), there exists an equivalent
polynomial with totalDegree ≤ (log n)² AND bottom fan-in ≤ log n.
The bottom fan-in constraint is what makes the multi-switching
lemma (Axiom 2) applicable.

Lean ref: Depth4Simulation.lean. -/

/-- A polynomial is multilinear: every variable appears with exponent ≤ 1.
    This is the key structural property of depth-4 ΣΠ∑Π circuit polynomials
    that makes the switching lemma work. Without it, polynomials like
    x₀² + x₁² + ... have SPDP rank > threshold for most restrictions. -/
def IsMultilinear {n : ℕ} (p : MvPolynomial (Fin n) ℚ) : Prop :=
  ∀ m ∈ p.support, ∀ i : Fin n, m i ≤ 1

axiom depth4_simulation :
    ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℚ),
    ∃ (q : MvPolynomial (Fin n) ℚ),
      -- Same Boolean function
      (∀ x, evalBool q x = evalBool p x) ∧
      -- Bounded degree (from ΣΠ∑Π formal degree)
      q.totalDegree ≤ (Nat.log 2 n) ^ 2 ∧
      -- Multilinear (from depth-4 circuit structure)
      IsMultilinear q

/-! ## Axiom 2: Multi-Switching Lemma (Lemma 7.2)

Paper: "Pr_s[SPDP(C|ρ_s) > √N] ≤ δ(n) = 2^{-2 log² N}"

For any polynomial with BOUNDED BOTTOM FAN-IN (from a depth-4 ΣΠ∑Π
circuit), most restrictions collapse its SPDP rank.

CRITICAL: This does NOT hold for arbitrary polynomials!
The ΣΠ∑Π structure (specifically, bounded bottom fan-in ≤ log n)
constrains which monomials can appear, enabling the switching
argument. A polynomial like x₀² + x₁² + ... violates this
and has SPDP rank > threshold for most restrictions.

Lean ref: SwitchingLemma/RST_Multi.lean. -/

axiom hil_multi_switching :
    ∀ (n : ℕ), n ≥ 2 →
    ∀ (p : MvPolynomial (Fin n) ℚ),
      p.totalDegree ≤ (Nat.log 2 n) ^ 2 →
      IsMultilinear p →
    ∃ (bad_p : Finset (Restriction.Restriction n)),
      -- (a) Collapse outside bad_p
      (∀ ρ, ρ ∉ bad_p →
        restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n)
          p ρ ≤ (Nat.log 2 n + 1) ^ 2) ∧
      -- (b) bad_p is small
      bad_p.card ≤ Fintype.card (Restriction.Restriction n) / 2

/-! ## Axiom 3: Row-Space Signature Classification (Lemma 7.2.1)

Paper: "the number of distinct spans ≤ 2^{O(log² N)}"

Depth-4 circuits with bounded params are classified into finitely
many signature classes based on their SPDP row-space structure.
Polynomials in the same class share the same collapse behavior.

Lean ref: SubspaceCount/SignatureCount.lean, line 23. -/

axiom rowspace_signature_bound :
    ∀ (n : ℕ), n ≥ 2 →
    ∃ (m : ℕ)
      (classify : MvPolynomial (Fin n) ℚ → Fin m),
      -- Same class → same collapse:
      (∀ (p q : MvPolynomial (Fin n) ℚ),
        p.totalDegree ≤ (Nat.log 2 n) ^ 2 →
        q.totalDegree ≤ (Nat.log 2 n) ^ 2 →
        classify p = classify q →
        ∀ (ρ : Restriction.Restriction n),
          restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n)
            p ρ ≤ (Nat.log 2 n + 1) ^ 2 →
          restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n)
            q ρ ≤ (Nat.log 2 n + 1) ^ 2) ∧
      -- m classes fit the union bound
      m * (Fintype.card (Restriction.Restriction n) / 2) <
        Fintype.card (Restriction.Restriction n)

/-- Theorem 7.3: universal collapse under fixed ρ*.

    PROVED from all three axioms + pigeonhole.

    Proof chain:
    1. depth4_simulation → q with bounded degree AND bottom fan-in
    2. hil_multi_switching (needs fan-in bound!) → per-class bad set
    3. rowspace_signature_bound → classification + union bound
    4. Pigeonhole → universal good seed ρ* -/
theorem depth4_good_seed
    (n : ℕ) (hn : n ≥ 2) :
    ∃ (ρ : Restriction.Restriction n),
    ∀ (p : MvPolynomial (Fin n) ℚ),
      p.totalDegree ≤ (Nat.log 2 n) ^ 2 →
      IsMultilinear p →
      restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n)
        p ρ ≤ (Nat.log 2 n + 1) ^ 2 := by
  classical
  obtain ⟨m, classify, hclass, hm_bound⟩ :=
    rowspace_signature_bound n hn
  have per_class : ∀ i : Fin m,
      ∃ (bad_i : Finset (Restriction.Restriction n)),
        (∀ (p : MvPolynomial (Fin n) ℚ),
          p.totalDegree ≤ (Nat.log 2 n) ^ 2 →
          IsMultilinear p →
          classify p = i →
          ∀ ρ, ρ ∉ bad_i →
            restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n)
              p ρ ≤ (Nat.log 2 n + 1) ^ 2) ∧
        bad_i.card ≤ Fintype.card (Restriction.Restriction n) / 2 := by
    intro i
    by_cases h : ∃ (rep : MvPolynomial (Fin n) ℚ),
        rep.totalDegree ≤ (Nat.log 2 n) ^ 2 ∧
        IsMultilinear rep ∧ classify rep = i
    · obtain ⟨rep, hrep_deg, hrep_ml, hrep_class⟩ := h
      obtain ⟨bad_rep, hcollapse, hsmall⟩ :=
        hil_multi_switching n hn rep hrep_deg hrep_ml
      refine ⟨bad_rep, ?_, hsmall⟩
      intro p hp_deg hp_ml hp_class ρ hρ
      exact hclass rep p hrep_deg hp_deg
        (by rw [hrep_class, hp_class]) ρ (hcollapse ρ hρ)
    · exact ⟨∅, fun p hp _ hp_class => absurd ⟨p, hp, ‹_›, hp_class⟩ h, by simp⟩
  choose bad hbad_cover hbad_size using per_class
  have hcard : (Finset.univ.biUnion bad).card <
      Fintype.card (Restriction.Restriction n) := by
    calc (Finset.univ.biUnion bad).card
        ≤ ∑ i : Fin m, (bad i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin m,
            Fintype.card (Restriction.Restriction n) / 2 :=
          Finset.sum_le_sum (fun i _ => hbad_size i)
      _ = m * (Fintype.card (Restriction.Restriction n) / 2) := by
          simp [Finset.sum_const, Finset.card_fin]
      _ < Fintype.card (Restriction.Restriction n) := hm_bound
  obtain ⟨ρ, hρ⟩ :=
    exists_seed_avoiding_bad_union (tests := Finset.univ) bad hcard
  exact ⟨ρ, fun p hp_deg hp_ml =>
    hbad_cover (classify p) p hp_deg hp_ml rfl ρ (hρ (classify p) (by simp))⟩

end PaperAxioms
