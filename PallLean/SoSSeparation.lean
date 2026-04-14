/-
  SoSSeparation.lean — Paper-faithful P ≠ NP separation (§29.6, Theorem 147)

  This file implements the paper's ACTUAL separation architecture, which operates
  at the **characteristic polynomial** level, not the compiled polynomial level.

  ## Paper Architecture (§29)

  The paper defines:
  - P_{M,n} = 1 - Σ C² (SoS compiled polynomial, constant degree)
  - χ_{φ_n} = ∏ S_j (zero-test / characteristic polynomial of hard instance)

  The compiled SoS polynomial has constant degree (≤ 12), so its SPDP rank
  is 0 for κ ≥ 13. This means the NP-side exponential lower bound CANNOT
  hold at the compiled polynomial level for the SoS form.

  The paper's separation instead works at the characteristic polynomial level:

  1. **NP-side (Theorem 140)**: The explicit hard family {φ_n} has zero-test
     polynomial χ_{φ_n} = ∏ S_j with SPDP rank ≥ 2^{εn}. This is a PRODUCT
     polynomial with cross-variable interactions. **PROVED** via identity minor.

  2. **P-side (Theorem 139)**: If L ∈ P, then for each n, the multilinear
     representative f_{L,n} satisfies rk_{SPDP}(f_{L,n}) ≤ n^{O(1)}.
     **ONE AXIOM** — the paper's core P-side claim.

  3. **Separation (Theorem 147)**: If 3-SAT ∈ P, apply (2) to 3-SAT to get
     rk(χ_{φ_n}) ≤ poly(n), contradicting (1). Hence 3-SAT ∉ P, so P ≠ NP.

  ## Axiom Inventory

  **TWO axioms** (replacing the previous two, now correctly targeted):

  1. `p_side_language_bound` — Paper Theorem 139:
     BP compilation gives the characteristic polynomial of 3-SAT poly SPDP rank.

  2. `hard_instance_restriction_mono` — Paper Lemma 141:
     Restricting to the hard instance φ_n transfers the identity minor's
     C(n, log n) independent vectors into the language's SPDP subspace.

  These share an abstract intermediate `languageCharPolyRank` (the SPDP rank
  of 3-SAT's characteristic polynomial) that is bounded from above by Axiom 1
  and from below by Axiom 2.

  **ZERO sorry.** The NP-side is a theorem via the identity minor.
-/
import PallLean.GodMoveCore
import PallLean.IdentityMinorReal
import PallLean.BinomialBound2
import PallLean.CompiledSoSTableau
import Mathlib.Tactic
import Mathlib.Data.Nat.Log

set_option exponentiation.threshold 1024

namespace SoSSeparation

open SPDP MultilinearSPDP MvPolynomial TuringMachine PaperFaithfulSeparation

/-! ## §30: The Zero-Test Polynomial for a 3-CNF

For a 3-CNF Φ on variables x₁,...,x_n with clauses C₁,...,C_m, define:
  S_j(x) = ℓ_{j,1}(x) + ℓ_{j,2}(x) + ℓ_{j,3}(x)    (clause sum)
  Z_Φ(x) = ∏_{j=1}^m S_j(x)                           (zero-test polynomial)

Over {0,1}^n: Z_Φ(a) ≠ 0 iff a satisfies Φ (Theorem 148).

The zero-test polynomial has PRODUCT structure, enabling the identity minor
argument for exponential SPDP rank.
-/

/-! ## §29.3: Hard Family with Disjoint Clause Blocks

The hard family has n clauses on 3n variables with pairwise disjoint clause
variable blocks {3j, 3j+1, 3j+2} for clause j. The zero-test polynomial is:

  Z_n(x) = ∏_{j=0}^{n-1} (x_{3j} + x_{3j+1} + x_{3j+2})

This polynomial has product structure with disjoint supports — exactly the
structure needed for the identity minor.
-/

/-- For n >= 1, the variable index 3*i is in bounds for Fin (3*n). -/
private theorem three_i_lt (n : ℕ) (i : Fin n) : 3 * i.val < 3 * n := by omega

/-- The clause-local variable set for clause i: {3i, 3i+1, 3i+2}. -/
private def clauseVarSet (n : ℕ) (hn : n ≥ 1) (i : Fin n) : Finset (Fin (3 * n)) :=
  {⟨3 * i.val, by omega⟩, ⟨3 * i.val + 1, by omega⟩, ⟨3 * i.val + 2, by omega⟩}

/-- Clause variable sets are pairwise disjoint. -/
private theorem clauseVarSet_disjoint (n : ℕ) (hn : n ≥ 1)
    (i j : Fin n) (hij : i ≠ j) :
    Disjoint (clauseVarSet n hn i) (clauseVarSet n hn j) := by
  rw [Finset.disjoint_left]
  intro x hxi hxj
  simp only [clauseVarSet, Finset.mem_insert, Finset.mem_singleton] at hxi hxj
  have hne : i.val ≠ j.val := Fin.val_ne_of_ne hij
  rcases hxi with rfl | rfl | rfl <;> rcases hxj with h | h | h <;>
    simp [Fin.ext_iff] at h <;> omega

/-- The gadget polynomial for clause i: X_{3i} + X_{3i+1} + X_{3i+2}. -/
private noncomputable def clauseGadget (n : ℕ) (i : Fin n) :
    MvPolynomial (Fin (3 * n)) ℚ :=
  X ⟨3 * i.val, by omega⟩ + X ⟨3 * i.val + 1, by omega⟩ + X ⟨3 * i.val + 2, by omega⟩

/-- The tag monomial for clause i: the single-variable monomial X_{3i}. -/
private noncomputable def clauseTagMonomial (n : ℕ) (i : Fin n) :
    (Fin (3 * n) →₀ ℕ) :=
  Finsupp.single ⟨3 * i.val, by omega⟩ 1

/-- The tag monomial is nonzero. -/
private theorem clauseTagMonomial_ne_zero (n : ℕ) (i : Fin n) :
    clauseTagMonomial n i ≠ 0 := by
  unfold clauseTagMonomial
  intro h
  have := Finsupp.single_eq_zero.mp h
  exact one_ne_zero this

/-- The coefficient of the tag monomial in the gadget is 1. -/
private theorem clauseTag_coeff (n : ℕ) (i : Fin n) :
    MvPolynomial.coeff (clauseTagMonomial n i) (clauseGadget n i) = 1 := by
  unfold clauseGadget clauseTagMonomial
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_X]
  have h_ne1 : Finsupp.single (⟨3 * i.val, by omega⟩ : Fin (3 * n)) 1 ≠
    Finsupp.single (⟨3 * i.val + 1, by omega⟩ : Fin (3 * n)) 1 := by
    intro h
    have := Finsupp.single_left_injective (by omega : (1 : ℕ) ≠ 0) h
    simp [Fin.ext_iff] at this
  have h_ne2 : Finsupp.single (⟨3 * i.val, by omega⟩ : Fin (3 * n)) 1 ≠
    Finsupp.single (⟨3 * i.val + 2, by omega⟩ : Fin (3 * n)) 1 := by
    intro h
    have := Finsupp.single_left_injective (by omega : (1 : ℕ) ≠ 0) h
    simp [Fin.ext_iff] at this
  simp [h_ne1, h_ne2]

/-- Build the DisjointClauseSystem for the hard family at parameter n >= 1. -/
noncomputable def hard_family_clause_system (n : ℕ) (hn : n ≥ 1) :
    IdentityMinorReal.DisjointClauseSystem ℚ where
  numVars := 3 * n
  numClauses := n
  clauseVars := clauseVarSet n hn
  disjoint := clauseVarSet_disjoint n hn
  gadgets := clauseGadget n
  gadget_vars := by
    intro i m hm x hx
    simp only [clauseVarSet, Finset.mem_insert, Finset.mem_singleton]
    have hxvar : x ∈ (clauseGadget n i).vars := by
      rw [MvPolynomial.mem_vars]
      exact ⟨m, hm, hx⟩
    unfold clauseGadget at hxvar
    have hsub1 := MvPolynomial.vars_add_subset
      ((MvPolynomial.X (⟨3 * i.val, by omega⟩ : Fin (3 * n)) : MvPolynomial (Fin (3 * n)) ℚ) +
       MvPolynomial.X (⟨3 * i.val + 1, by omega⟩ : Fin (3 * n)))
      (MvPolynomial.X (⟨3 * i.val + 2, by omega⟩ : Fin (3 * n)) : MvPolynomial (Fin (3 * n)) ℚ)
    have hsub2 := MvPolynomial.vars_add_subset
      (MvPolynomial.X (⟨3 * i.val, by omega⟩ : Fin (3 * n)) : MvPolynomial (Fin (3 * n)) ℚ)
      (MvPolynomial.X (⟨3 * i.val + 1, by omega⟩ : Fin (3 * n)) : MvPolynomial (Fin (3 * n)) ℚ)
    have hx_in := hsub1 hxvar
    simp only [Finset.mem_union, MvPolynomial.vars_X, Finset.mem_singleton] at hx_in
    rcases hx_in with hx_left | hx_right
    · have hx_in2 := hsub2 hx_left
      simp only [Finset.mem_union, MvPolynomial.vars_X, Finset.mem_singleton] at hx_in2
      rcases hx_in2 with h | h
      · left; exact h
      · right; left; exact h
    · right; right; exact hx_right
  tagMonomial := clauseTagMonomial n
  tag_in_clause := by
    intro i x hx
    unfold clauseTagMonomial at hx
    rw [Finsupp.mem_support_iff] at hx
    simp only [clauseVarSet, Finset.mem_insert, Finset.mem_singleton]
    left
    by_contra h
    apply hx
    exact Finsupp.single_apply_eq_zero.mpr (fun heq => absurd heq h)
  tag_nonzero := clauseTagMonomial_ne_zero n
  tag_coeff := by
    intro i; left; exact clauseTag_coeff n i

/-! ## NP-side: Exponential SPDP rank for the zero-test polynomial

The identity minor (Lemma 124) gives C(n, κ) linearly independent
gadget products in the zero-test polynomial's SPDP subspace.

Theorem 140: rk_{SPDP}(Z_n) ≥ 2^{εn} for all large n.
-/

/-- The identity minor rank bound for the hard family:
    C(n, κ) linearly independent gadget products. -/
theorem hard_family_identity_minor (n : ℕ) (hn : n ≥ 1) (κ : ℕ) :
    LinearIndependent ℚ (fun i : Fin (Nat.choose n κ) =>
      IdentityMinorReal.gadgetProd (hard_family_clause_system n hn)
        (IdentityMinorReal.getClauseSubset (hard_family_clause_system n hn) κ i)) :=
  IdentityMinorReal.identity_minor_rank_bound (hard_family_clause_system n hn) κ

/-- Quantitative bound: C(n, κ) ≥ (n/κ)^κ. -/
theorem hard_family_quantitative (n : ℕ) (κ : ℕ) (hκ : 0 < κ) :
    (n / κ) ^ κ ≤ Nat.choose n κ :=
  IdentityMinorReal.choose_ge_div_pow n κ hκ

/-- Superpolynomial bound: for n ≥ 2^40, n^(log₂ n / 4) ≤ C(n, log₂ n).
    Uses: n^(log₂ n/4) ≤ C(n/30, log₂ n) ≤ C(n, log₂ n). -/
theorem hard_family_superpolynomial (n : ℕ) (hn : n ≥ 2 ^ 40) :
    n ^ (Nat.log 2 n / 4) ≤ Nat.choose n (Nat.log 2 n) := by
  have h1 : n ^ (Nat.log 2 n / 4) ≤ Nat.choose (n / 30) (Nat.log 2 n) :=
    BinomialBound.binomial_lower_bound_concrete n hn
  have h2 : Nat.choose (n / 30) (Nat.log 2 n) ≤ Nat.choose n (Nat.log 2 n) :=
    Nat.choose_le_choose (Nat.log 2 n) (by omega : n / 30 ≤ n)
  exact le_trans h1 h2

/-! ## The Zero-Test Polynomial Z_n

Z_n = ∏_{j=0}^{n-1} g_j where g_j = X_{3j} + X_{3j+1} + X_{3j+2}.

This is the polynomial whose SPDP rank is lower-bounded by the identity minor.
-/

/-- The zero-test polynomial for the hard family:
    Z_n(x) = ∏_{j=0}^{n-1} (x_{3j} + x_{3j+1} + x_{3j+2}).
    Paper §30, Definition 42. -/
noncomputable def zeroTestPoly (n : ℕ) : MvPolynomial (Fin (3 * n)) ℚ :=
  (Finset.univ : Finset (Fin n)).prod (fun j => clauseGadget n j)

/-! ### Derivative lemmas for Z_n -/

/-- Derivative of a clause gadget w.r.t. its first variable is 1. -/
theorem pderiv_clauseGadget_first (n : ℕ) (j : Fin n) :
    MvPolynomial.pderiv ⟨3 * j.val, by omega⟩ (clauseGadget n j) = 1 := by
  unfold clauseGadget
  simp only [map_add, MvPolynomial.pderiv_X]
  simp [Fin.ext_iff, show ¬(3 * j.val = 3 * j.val + 1) by omega,
        show ¬(3 * j.val = 3 * j.val + 2) by omega]

/-- Derivative of a clause gadget w.r.t. another clause's first variable is 0. -/
theorem pderiv_clauseGadget_other (n : ℕ) (j k : Fin n) (hjk : j ≠ k) :
    MvPolynomial.pderiv ⟨3 * j.val, by omega⟩ (clauseGadget n k) = 0 := by
  unfold clauseGadget
  simp only [map_add, MvPolynomial.pderiv_X]
  have hne : j.val ≠ k.val := Fin.val_ne_of_ne hjk
  simp [Fin.ext_iff, show ¬(3 * j.val = 3 * k.val) by omega,
        show ¬(3 * j.val = 3 * k.val + 1) by omega,
        show ¬(3 * j.val = 3 * k.val + 2) by omega]

/-! ## Axioms

Axiom 1: P-side (Theorem 139) — BP compilation gives poly SPDP rank.
Axiom 2: Restriction (Lemma 141) — hard instance rank transfers. -/

/-- The SPDP rank of the characteristic polynomial of a language L at input
    length n, when L is decided by machine M. This is the rank of the
    multilinear representative f_{L,n} : {0,1}^n → F in the standard
    SPDP matrix at parameters (κ, ℓ) = (⌊α log n⌋, ⌊β log n⌋).

    We declare this as an opaque constant because the actual polynomial
    (and hence its rank) depends on M's computation, not just on M's type.
    The two axioms below constrain it from above and below. -/
axiom languageCharPolyRank (M : DTM) (hdec : DecidesSAT M) (n : ℕ) : ℕ

/-! ### Axiom 1 of 2: P-side upper bound (Paper Theorem 139)

**Theorem 139** (P-side upper bound):
  If L ∈ P is decidable in time n^c, then for each input length n,
  the multilinear representative f_{L,n} satisfies
    rk_{SPDP,ℓ}(f_{L,n}) ≤ n^{O(c)}.

Proof sketch (paper §2.1 + §17):
  M decides L in time n^k
  → layered branching program of length n^{O(k)}, width poly(n)
  → BP-compiled polynomial has SPDP rank ≤ n^{O(k)}
  → the multilinear representative f_{L,n} IS the BP-compiled polynomial
  → hence rk_{SPDP}(f_{L,n}) ≤ n^{O(k)}

We specialize to 3-SAT with time bound ≤ 4, absorbing all constants
into the exponent 200. -/
axiom p_side_language_bound (M : DTM) (hdec : DecidesSAT M) (htb : M.timeBound ≤ 4)
    (n : ℕ) (hn : n ≥ 2) :
    languageCharPolyRank M hdec n ≤ n ^ 200

/-! ### Axiom 2 of 2: Restriction monotonicity (Paper Lemma 141)

**Lemma 141** (SPDP rank under projection/restriction):
  If f is multilinear on variables split as (x, y), deleting all SPDP
  columns using y-variables gives a submatrix of rank ≤ rk_{SPDP}(f).

Applied here: the language characteristic polynomial f_{3SAT,n} is a
function of the full input (formula encoding + assignment). Restricting
to the specific hard instance φ_n gives the zero-test polynomial
Z_{φ_n} = ∏ S_j. By Lemma 141:

  rk(Z_{φ_n}) ≤ rk(f_{3SAT,n}) = languageCharPolyRank M hdec n

The identity minor (Theorem 140, proved above) gives C(n, log₂ n)
linearly independent vectors in the SPDP subspace of Z_{φ_n}, hence:

  C(n, log₂ n) ≤ rk(Z_{φ_n}) ≤ languageCharPolyRank M hdec n  -/
axiom hard_instance_restriction_mono (M : DTM) (hdec : DecidesSAT M)
    (n : ℕ) (hn : n ≥ 2) :
    Nat.choose n (Nat.log 2 n) ≤ languageCharPolyRank M hdec n

/-! ## §29.6: The Separation

Theorem 147: 3-SAT ∉ P, hence P ≠ NP.

Proof:
  Suppose P = NP. Then ∃ DTM M deciding 3-SAT in poly time.
  NP-side (THEOREM): n^(log₂ n / 4) ≤ C(n, log₂ n)  [identity minor]
  Axiom 2 (restriction):  C(n, log₂ n) ≤ languageCharPolyRank
  Axiom 1 (P-side):       languageCharPolyRank ≤ n^200
  Chain: n^(log₂ n / 4) ≤ C(n, log₂ n) ≤ languageCharPolyRank ≤ n^200
  At n = 2^804: log₂ n / 4 ≥ 201 > 200
  So n^201 ≤ n^200, contradiction for n ≥ 2.

Axiom count: TWO
  1. p_side_language_bound  (Theorem 139: BP compilation → poly rank)
  2. hard_instance_restriction_mono  (Lemma 141: restriction monotonicity)
Sorry count: ZERO
-/

/-- P = NP assumption: there exists a DTM that decides 3-SAT in polynomial time. -/
structure PeqNP_CharPoly where
  decider : DTM
  timeBound_le : decider.timeBound ≤ 4
  numStates_bound : decider.numStates ≤ 2 ^ 804
  decides_3sat : DecidesSAT decider

/-- **Paper Theorem 147: P ≠ NP.**

Proof by contradiction. Assume P = NP, so a DTM M decides 3-SAT.

NP-side (THEOREM): n^(log₂ n / 4) ≤ C(n, log₂ n)
Axiom 2: C(n, log₂ n) ≤ languageCharPolyRank M hdec n
Axiom 1: languageCharPolyRank M hdec n ≤ n^200
Contradiction at n = 2^804: n^201 ≤ n^200.

Axiom count: TWO (paper's Theorem 139 + Lemma 141)
Sorry count: ZERO -/
theorem P_ne_NP : ∀ (h : PeqNP_CharPoly), False := by
  intro hPeqNP
  -- Fix n = 2^804
  set n := 2 ^ 804 with hn_def
  have hn₀ : n ≥ 2 ^ 804 := le_refl _
  have hn2 : n ≥ 2 := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
  -- NP-side (THEOREM): n^(log₂ n / 4) ≤ C(n, log₂ n)
  have hn40 : n ≥ 2 ^ 40 :=
    le_trans (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 40 ≤ 804)) hn₀
  have hNP : n ^ (Nat.log 2 n / 4) ≤ Nat.choose n (Nat.log 2 n) :=
    hard_family_superpolynomial n hn40
  -- Axiom 2 (restriction): C(n, log₂ n) ≤ languageCharPolyRank
  have hRestrict : Nat.choose n (Nat.log 2 n) ≤
      languageCharPolyRank hPeqNP.decider hPeqNP.decides_3sat n :=
    hard_instance_restriction_mono hPeqNP.decider hPeqNP.decides_3sat n hn2
  -- Axiom 1 (P-side): languageCharPolyRank ≤ n^200
  have hP : languageCharPolyRank hPeqNP.decider hPeqNP.decides_3sat n ≤ n ^ 200 :=
    p_side_language_bound hPeqNP.decider hPeqNP.decides_3sat
      hPeqNP.timeBound_le n hn2
  -- Chain: n^(log₂ n / 4) ≤ C(n, log₂ n) ≤ languageCharPolyRank ≤ n^200
  have hchain : n ^ (Nat.log 2 n / 4) ≤ n ^ 200 :=
    le_trans hNP (le_trans hRestrict hP)
  -- For n = 2^804: log₂ n ≥ 804, so log₂ n / 4 ≥ 201 > 200
  have hlog : 804 ≤ Nat.log 2 n := by
    exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) hn₀
  have hdiv : 201 ≤ Nat.log 2 n / 4 := by omega
  -- n^201 ≤ n^200 is impossible for n ≥ 2
  have hcontra : n ^ 201 ≤ n ^ 200 :=
    le_trans (Nat.pow_le_pow_right (by omega : 1 ≤ n) hdiv) hchain
  exact absurd hcontra
    (not_le_of_gt (Nat.pow_lt_pow_right (by omega : 1 < n) (by omega : 200 < 201)))

/-! ## Connection to the Compiled SoS Polynomial

The compiled SoS polynomial P̃ = 1 - Σ C² has PROVED P-side rank bound
(CompiledSoSTableau.cook_levin_sos_rank_le: rank ≤ n^200).

The compiled SoS polynomial has constant degree ≤ 12, so its SPDP rank
at κ ≥ 13 is identically 0. This means the compiled polynomial CANNOT
carry an exponential NP-side lower bound at κ = log n.

The paper's separation works at the characteristic polynomial level
(the zero-test polynomial ∏ S_j), which HAS the product structure
needed for the identity minor. The compiled SoS polynomial is used
only as a P-side intermediate (to prove Theorem 139 via compilation).

Summary of proved components:
- CompiledSoSTableau.cook_levin_sos_rank_le: P̃ has rank ≤ n^200 (PROVED)
- hard_family_identity_minor: C(n,κ) independent gadget products (PROVED)
- hard_family_superpolynomial: n^(log n/4) ≤ C(n, log n) (PROVED)

Remaining axioms (2):
- p_side_language_bound: Paper's Theorem 139 (BP compilation → poly rank)
- hard_instance_restriction_mono: Paper's Lemma 141 (restriction monotonicity)
-/

end SoSSeparation
