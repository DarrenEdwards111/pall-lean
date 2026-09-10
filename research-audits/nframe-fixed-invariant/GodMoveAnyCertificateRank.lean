import PallLean.PiStarConcrete

/-!
# Every local accumulator certificate contains the target in a multiplier

Consider any polynomial identity expressing `w_m - Q` as a combination of
the local accumulator equations `w_0 - 1` and `w_(i+1) - w_i * f_i`.
Set all accumulator wires to zero and retain the target variables. Every
step equation then vanishes, while the initial equation becomes `-1`.
Consequently the multiplier of that initial equation projects exactly to
`Q`. This holds for every certificate, including coefficients that depend
on all the accumulator wires; it is not restricted to the known telescope.

The existing concrete zero-substitution gauge is rank monotone. Thus the
initial multiplier must have at least the target's strict blocked SPDP
rank, at the same partition and derivative/shift parameters, and at least
the target's total degree. A rank bound
for the low-degree local generators alone therefore does not bound the
algebraic certificate's cost. This is a necessary condition for this
particular extraction route, not a lower bound for SAT computation or a
refutation of every possible God-Move compiler.
-/

namespace GodMoveAnyCertificateRank

open scoped BigOperators
open MvPolynomial PiStarConcrete MultilinearSPDP

abbrev Poly (N : ℕ) := MvPolynomial (Fin N) ℚ

/-- An arbitrary identity from the actual local initial/step equations. -/
def IsLocalCertificate {N m : ℕ} (wire : Fin (m + 1) → Fin N)
    (f : Fin m → Poly N) (Q A : Poly N) (C : Fin m → Poly N) : Prop :=
  X (wire (Fin.last m)) - Q =
    A * (X (wire 0) - 1) +
      ∑ i : Fin m, C i * (X (wire i.succ) - X (wire i.castSucc) * f i)

/-- The target is derived from the certificate by concrete zero substitution.
No condition on the certificate multipliers or the factor supports is needed. -/
theorem initial_multiplier_extracts_target {N m : ℕ}
    (keep : Fin N → Prop) [DecidablePred keep]
    (wire : Fin (m + 1) → Fin N) (f : Fin m → Poly N)
    (Q A : Poly N) (C : Fin m → Poly N)
    (hwire : ∀ i, ¬ keep (wire i))
    (hQ : ∀ i ∈ Q.vars, keep i)
    (hcert : IsLocalCertificate wire f Q A C) :
    piZero keep A = Q := by
  have hdrop (i : Fin (m + 1)) :
      substAlgHom keep 0 (X (wire i)) = 0 := by
    change piZero keep (X (wire i)) = 0
    rw [piZero_X, if_neg (hwire i)]
  have hfixed : substAlgHom keep 0 Q = Q :=
    piZero_eq_self_of_support_kept keep (support_kept_of_vars_kept keep hQ)
  have h := congrArg (substAlgHom keep 0) hcert
  simp only [map_sub, map_add, map_mul, map_sum, map_one,
    hdrop, hfixed, zero_sub, zero_mul, sub_self, mul_zero,
    Finset.sum_const_zero, add_zero, mul_neg, mul_one] at h
  exact neg_inj.mp h.symm

/-- The unavoidable multiplier inherits every same-parameter strict SPDP
lower bound of the extracted target. -/
theorem target_rank_le_initial_multiplier {N m : ℕ}
    (B : SPDP.BlockPartition N) (kappa ell : ℕ)
    (keep : Fin N → Prop) [DecidablePred keep]
    (wire : Fin (m + 1) → Fin N) (f : Fin m → Poly N)
    (Q A : Poly N) (C : Fin m → Poly N)
    (hwire : ∀ i, ¬ keep (wire i))
    (hQ : ∀ i ∈ Q.vars, keep i)
    (hcert : IsLocalCertificate wire f Q A C) :
    mlBlockedSpdpRank B kappa ell Q ≤ mlBlockedSpdpRank B kappa ell A := by
  have h := piZero_isRankMonotoneGauge keep B kappa ell A
  rwa [initial_multiplier_extracts_target keep wire f Q A C hwire hQ hcert] at h

/-- In particular, no such certificate can have a multiplier below any
already-proved rank lower bound for the target. -/
theorem no_certificate_below_target_rank {N m : ℕ}
    (B : SPDP.BlockPartition N) (kappa ell bound : ℕ)
    (keep : Fin N → Prop) [DecidablePred keep]
    (wire : Fin (m + 1) → Fin N) (f : Fin m → Poly N)
    (Q : Poly N) (hwire : ∀ i, ¬ keep (wire i))
    (hQ : ∀ i ∈ Q.vars, keep i)
    (hlower : bound < mlBlockedSpdpRank B kappa ell Q) :
    ¬ ∃ A C, IsLocalCertificate wire f Q A C ∧
      mlBlockedSpdpRank B kappa ell A ≤ bound := by
  rintro ⟨A, C, hcert, hbound⟩
  have hle := target_rank_le_initial_multiplier B kappa ell keep wire f Q A C
    hwire hQ hcert
  omega

/-- Zero substitution only deletes monomials; it does not change surviving
coefficients. This also accounts for total degree in the certificate. -/
theorem coeff_piZero {N : ℕ} (keep : Fin N → Prop) [DecidablePred keep]
    (p : Poly N) (a : Fin N →₀ ℕ) :
    coeff a (piZero keep p) =
      if ∀ i, ¬ keep i → a i = 0 then coeff a p else 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial b c =>
    by_cases hba : b = a
    · subst b
      rw [piZero_monomial]
      split_ifs <;> simp
    · rw [piZero_monomial]
      split_ifs <;> simp [coeff_monomial, hba]
  | add p q hp hq =>
    rw [map_add, coeff_add, hp, hq, coeff_add]
    split_ifs <;> simp

theorem piZero_support_subset {N : ℕ}
    (keep : Fin N → Prop) [DecidablePred keep] (p : Poly N) :
    (piZero keep p).support ⊆ p.support := by
  intro a ha
  rw [mem_support_iff, coeff_piZero] at ha
  rw [mem_support_iff]
  split_ifs at ha with h
  · exact ha
  · exact False.elim (ha rfl)

theorem piZero_totalDegree_le {N : ℕ}
    (keep : Fin N → Prop) [DecidablePred keep] (p : Poly N) :
    (piZero keep p).totalDegree ≤ p.totalDegree :=
  totalDegree_le_of_support_subset (piZero_support_subset keep p)

/-- Any degree limit on certificate multipliers must accommodate the full
degree of the retained target, even though all local equations may be small. -/
theorem target_degree_le_initial_multiplier {N m : ℕ}
    (keep : Fin N → Prop) [DecidablePred keep]
    (wire : Fin (m + 1) → Fin N) (f : Fin m → Poly N)
    (Q A : Poly N) (C : Fin m → Poly N)
    (hwire : ∀ i, ¬ keep (wire i))
    (hQ : ∀ i ∈ Q.vars, keep i)
    (hcert : IsLocalCertificate wire f Q A C) :
    Q.totalDegree ≤ A.totalDegree := by
  have h := piZero_totalDegree_le keep A
  rwa [initial_multiplier_extracts_target keep wire f Q A C hwire hQ hcert] at h

end GodMoveAnyCertificateRank

#print axioms GodMoveAnyCertificateRank.initial_multiplier_extracts_target
#print axioms GodMoveAnyCertificateRank.target_rank_le_initial_multiplier
#print axioms GodMoveAnyCertificateRank.no_certificate_below_target_rank
#print axioms GodMoveAnyCertificateRank.piZero_support_subset
#print axioms GodMoveAnyCertificateRank.target_degree_le_initial_multiplier
