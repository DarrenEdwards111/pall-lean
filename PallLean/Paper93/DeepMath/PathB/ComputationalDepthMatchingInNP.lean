import Mathlib.Tactic
import Mathlib.Data.Fintype.Perm

/-!
# The honest `matching / permanent-nonzero ∈ NP` lemma (ported from the SPDP repo's `sorry`)

The desktop SPDP `P≠NP` repo left `perm_f_in_NP` and `perm_via_determinant` as `sorry`, with the
permanent-nonzero predicate itself undefined.  This file proves the honest content those stubs were
standing in for — fully, axiom-clean:

* the permanent of a nonnegative integer matrix is **positive iff the matrix has a perfect matching**
  (a permutation hitting only nonzero entries), and
* that matching is an **NP certificate**: a polynomial-size witness (a permutation of `Fin n`, one of
  `n!`, encodable in `O(n log n)` bits) checked by a **local verifier** that inspects exactly `n`
  entries.

## What is proved

* **`permanent_pos_iff`** — `0 < permanent M ↔ HasPerfectMatching M`.  Forward: if no permutation avoids
  a zero, every product term is `0`, so the sum is `0`.  Backward: a matching's term is positive and
  bounds the sum below.
* **`matching_in_NP`** — `HasPerfectMatching M ↔ ∃ σ, matchingCert M σ = true`: membership is equivalent
  to the existence of a certificate the verifier accepts.
* **`cert_is_local`** — the verifier is a conjunction over exactly `Fin n` (an `O(n)` local check).
* **`witness_count`** — the certificate space has size `n!`, so a witness is `O(n log n)` bits.

## Honest scope — NOT a hardness or separation claim

This is genuine, but it is the **easy** side of NP and it advances nothing about `P` vs `NP`.  In fact
the same predicate is **also in `P`** (bipartite perfect matching, Hopcroft–Karp), so it is not hard at
all.  It says nothing about `perm ∉ VP` (Valiant's conjecture) — the load-bearing step the SPDP repo
also left as `sorry` — and nothing about a separation.  It is exactly the provable plumbing, clearly
labelled as such.
-/

namespace PallLean.Paper93.DeepMath.PathB.MatchingInNP

open scoped BigOperators

variable {n : ℕ}

/-- The permanent of a nonnegative integer matrix: `∑_σ ∏_i M i (σ i)` over all permutations. -/
def permanent (M : Fin n → Fin n → ℕ) : ℕ := ∑ σ : Equiv.Perm (Fin n), ∏ i, M i (σ i)

/-- The matrix has a perfect matching: a permutation hitting only nonzero entries. -/
def HasPerfectMatching (M : Fin n → Fin n → ℕ) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∀ i, M i (σ i) ≠ 0

/-- **Permanent-nonzero ⟺ perfect matching (proved).**  The equivalence the SPDP repo left undefined. -/
theorem permanent_pos_iff (M : Fin n → Fin n → ℕ) :
    0 < permanent M ↔ HasPerfectMatching M := by
  constructor
  · intro h
    simp only [permanent] at h
    by_contra hno
    rw [HasPerfectMatching] at hno
    push_neg at hno
    have hzero : ∑ σ : Equiv.Perm (Fin n), ∏ i, M i (σ i) = 0 := by
      apply Finset.sum_eq_zero
      intro σ _
      obtain ⟨i, hi⟩ := hno σ
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    omega
  · rintro ⟨σ, hσ⟩
    simp only [permanent]
    calc 0 < ∏ i, M i (σ i) := Finset.prod_pos (fun i _ => Nat.pos_of_ne_zero (hσ i))
      _ ≤ ∑ σ' : Equiv.Perm (Fin n), ∏ i, M i (σ' i) :=
          Finset.single_le_sum (f := fun τ => ∏ i, M i (τ i))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ σ)

/-- The NP verifier: check that the certificate permutation `σ` avoids every zero entry.  This is a
local check of exactly `n` entries (see `cert_is_local`). -/
def matchingCert (M : Fin n → Fin n → ℕ) (σ : Equiv.Perm (Fin n)) : Bool :=
  decide (∀ i, M i (σ i) ≠ 0)

/-- **`matching ∈ NP` (proved).**  Membership is equivalent to the existence of a certificate the
verifier accepts — the honest content of the repo's `perm_f_in_NP`. -/
theorem matching_in_NP (M : Fin n → Fin n → ℕ) :
    HasPerfectMatching M ↔ ∃ σ : Equiv.Perm (Fin n), matchingCert M σ = true := by
  constructor
  · rintro ⟨σ, hσ⟩; exact ⟨σ, by simpa [matchingCert] using hσ⟩
  · rintro ⟨σ, hσ⟩; exact ⟨σ, by simpa [matchingCert] using hσ⟩

/-- **The permanent, packaged as an NP predicate (proved).**  Positivity of the permanent is decided by
the same poly-size certificate. -/
theorem permanent_pos_iff_cert (M : Fin n → Fin n → ℕ) :
    0 < permanent M ↔ ∃ σ : Equiv.Perm (Fin n), matchingCert M σ = true :=
  (permanent_pos_iff M).trans (matching_in_NP M)

/-- **The verifier is local (proved).**  Acceptance is exactly a conjunction over `Fin n` — an `O(n)`
check, no search. -/
theorem cert_is_local (M : Fin n → Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    matchingCert M σ = true ↔ ∀ i, M i (σ i) ≠ 0 := by
  simp [matchingCert]

/-- **The certificate space has size `n!` (proved).**  A witness is one of `n!` permutations, hence
`O(n log n)` bits — polynomial. -/
theorem witness_count (n : ℕ) : Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial n := by
  rw [Fintype.card_perm, Fintype.card_fin]

end PallLean.Paper93.DeepMath.PathB.MatchingInNP

#print axioms PallLean.Paper93.DeepMath.PathB.MatchingInNP.permanent_pos_iff_cert
