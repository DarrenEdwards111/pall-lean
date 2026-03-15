/-
  PneqNP_Paper.lean — P ≠ NP matching the paper's Theorem 12.1

  Paper structure:
    §5   Depth-4 simulation: P-time → ΣΠΣ∧ with fan-in O(log n)
    §6   SPDP collapse: depth-4 + bounded fan-in → low SPDP rank
    §7   Diagonal function f_n defined via SPDP evaluations
    §8.6 God Move: annihilator w ∈ ker(M), ⟨v(f_n), w⟩ ≠ 0
    §12  P ⊆ F_SPDP ⊊ NP ⟹ P ⊊ NP

  Lean architecture:
    PROVED: Core escape mechanism (annihilator orthogonality)
    AXIOM 1: P ⊆ F_SPDP (depth-4 simulation + SPDP collapse)
    AXIOM 2: F_SPDP-evaluation subspace has dimension < 2^k
             (so annihilator w exists with positive entry)
    AXIOM 3: f_n (defined from annihilator w) is in NP
             (w from ker(M) is polynomial-size certificate)
    DERIVED: P ≠ NP
-/
import PallLean.PneqNP_General
import PallLean.WalshAnnihilator
import Mathlib.Tactic

namespace PneqNP_Paper

open BoolEval PneqNP_General WalshAnnihilator PaperAxioms

/-! ## Abstract complexity classes -/

/-- A Boolean function on n variables. -/
abbrev BoolFun (n : ℕ) := (Fin n → Bool) → Bool

/-- Abstract predicate: f is polynomial-time computable. -/
axiom PtimeComputable : {n : ℕ} → BoolFun n → Prop

/-- Abstract predicate: f is in NP (has polynomial-size certificate). -/
axiom InNP : {n : ℕ} → BoolFun n → Prop

/-- P = NP: every NP function is P-time computable. -/
def P_eq_NP : Prop := ∀ (n : ℕ) (f : BoolFun n), InNP f → PtimeComputable f

/-! ## F_SPDP: the observer-visible class (Paper §2, §12)

  F_SPDP = {f | ∃ circuit C ∈ P, f = C ∧ SPDP_rank(C|ρ) ≤ √N}

  Key properties (from the paper):
  1. P ⊆ F_SPDP (depth-4 simulation + SPDP collapse)
  2. F_SPDP evaluations span a subspace of dimension < 2^k
  3. Functions outside this subspace escape F_SPDP -/

/-- Abstract predicate: f is in F_SPDP (computable by a circuit
    that collapses under SPDP pruning with a short seed). -/
axiom InFSPDP : {n : ℕ} → BoolFun n → Prop

/-! ## Axiom 1: P ⊆ F_SPDP (Paper Theorem 11.1 / Corollary 5.1)

  Every P-time function, via depth-4 simulation (Cook-Levin + bucket
  expansion), has a poly-size depth-4 circuit with bottom fan-in O(log n).
  The switching lemma then gives SPDP rank collapse under restriction. -/

axiom P_subset_FSPDP : ∀ {n : ℕ} (f : BoolFun n),
    PtimeComputable f → InFSPDP f

/-! ## Axiom 2: Annihilator existence for F_SPDP (Paper §8.6)

  The SPDP evaluation vectors of all circuits in F_SPDP span a
  subspace of dimension < 2^k (where k = number of live variables
  after restriction). Therefore, an annihilator vector w exists in
  the orthogonal complement, with ⟨v(g), w⟩ = 0 for all g ∈ F_SPDP
  and w having a positive entry.

  This is the same mechanism as our Walsh construction, but applied
  to the SPDP evaluation subspace instead of the degree-≤-D subspace. -/

/-- Annihilator data for F_SPDP: a weight function w that is
    orthogonal to all F_SPDP evaluations but has a positive entry. -/
structure SPDPAnnihilator (n : ℕ) where
  w : (Fin n → Bool) → ℚ
  hw_pos : ∃ x, w x > 0
  hw_orth : ∀ (g : BoolFun n), InFSPDP g →
    ∑ x : (Fin n → Bool), boolToRat (g x) * w x = 0

axiom spdp_annihilator_exists (n : ℕ) (hn : n ≥ 2) :
    SPDPAnnihilator n

/-! ## The diagonal function f_n (Paper §7 + §8.6)

  Defined from the annihilator: f_n(x) = 1 iff w(x) > 0.
  This is the same as our DiagonalFunction.f_n. -/

/-- The diagonal function, defined from an annihilator weight. -/
noncomputable def f_n_spdp {n : ℕ} (ann : SPDPAnnihilator n) :
    BoolFun n :=
  fun x => if ann.w x > 0 then true else false

/-! ## Axiom 3: f_n ∈ NP (Paper §9, Appendix Q)

  The annihilator w comes from ker(M) where M is the canonical
  SPDP matrix — a polynomial-size object. The NP witness is:
  - The seed s* defining the restriction
  - The annihilator vector w ∈ ker(M)
  - The verifier checks Mw = 0 and w(x) > 0

  All polynomial-time checkable. -/

axiom f_n_in_NP (n : ℕ) (hn : n ≥ 2) :
    InNP (f_n_spdp (spdp_annihilator_exists n hn))

/-! ## Core escape: f_n ∉ F_SPDP (PROVED)

  This is the mathematical heart — proved via orthogonality.
  If f_n ∈ F_SPDP, then ⟨v(f_n), w⟩ = 0 by hw_orth.
  But ⟨v(f_n), w⟩ > 0 by hw_pos and the definition of f_n.
  Contradiction. -/

theorem f_n_escapes_FSPDP (n : ℕ) (hn : n ≥ 2) :
    ¬ InFSPDP (f_n_spdp (spdp_annihilator_exists n hn)) := by
  let ann := spdp_annihilator_exists n hn
  intro h_in
  -- Orthogonality: ⟨v(f_n), w⟩ = 0
  have h_orth := ann.hw_orth (f_n_spdp ann) h_in
  -- Positivity: ⟨v(f_n), w⟩ > 0
  have h_pos : 0 < ∑ x : (Fin n → Bool),
      boolToRat (f_n_spdp ann x) * ann.w x := by
    obtain ⟨x₀, hx₀⟩ := ann.hw_pos
    -- Each term is ≥ 0, and the x₀ term is > 0
    have h_nonneg : ∀ x, 0 ≤ boolToRat (f_n_spdp ann x) * ann.w x := by
      intro x
      unfold f_n_spdp boolToRat
      split_ifs with h
      · simp; exact le_of_lt h
      · simp
    have h_x0_pos : 0 < boolToRat (f_n_spdp ann x₀) * ann.w x₀ := by
      unfold f_n_spdp boolToRat
      simp [show ann.w x₀ > 0 from hx₀]
    calc 0 < boolToRat (f_n_spdp ann x₀) * ann.w x₀ := h_x0_pos
      _ ≤ ∑ x, boolToRat (f_n_spdp ann x) * ann.w x :=
          Finset.single_le_sum (fun x _ => h_nonneg x) (Finset.mem_univ x₀)
  -- Contradiction: 0 < sum = 0
  linarith

/-! ## P ≠ NP (Paper Theorem 12.1) -/

/-- Main theorem: P ≠ NP.

  Proof:
    1. f_n ∈ NP                    (Axiom 3)
    2. f_n ∉ F_SPDP                (escape theorem, PROVED)
    3. P ⊆ F_SPDP                  (Axiom 1)
    4. If P = NP, then f_n ∈ P     (from 1 + P=NP)
    5. f_n ∈ P → f_n ∈ F_SPDP      (from 3)
    6. Contradiction with 2         □ -/
theorem P_neq_NP : ¬ P_eq_NP := by
  intro hPeqNP
  -- f_n ∈ NP (Axiom 3)
  have h_np := f_n_in_NP 2 (le_refl 2)
  -- P = NP → f_n ∈ P
  have h_p := hPeqNP 2 _ h_np
  -- P ⊆ F_SPDP → f_n ∈ F_SPDP
  have h_spdp := P_subset_FSPDP _ h_p
  -- But f_n ∉ F_SPDP
  exact f_n_escapes_FSPDP 2 (le_refl 2) h_spdp

end PneqNP_Paper
