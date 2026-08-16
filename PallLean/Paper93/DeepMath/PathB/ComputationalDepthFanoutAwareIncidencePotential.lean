import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverRestrictionDecomposition

/-!
# A first fanout-aware restriction potential: live incidences

The output-only observer potential is refuted by parity in
`ComputationalDepthObserverRestrictionDecomposition`.  This file tests the next concrete candidate: charge every
*live gate-variable incidence* while representing gates as a `Finset`, so a shared gate is owned and charged once
rather than duplicated once per downstream use.

The key result is exact, not asymptotic: fixing a live variable decreases incidence potential by precisely its live
gate degree.  Thus a wide parity/`MOD` gate, which defeats output-only and active-gate-count potentials until its last
input is fixed, pays one unit at every restriction step under incidence potential.

This is useful accounting but not the missing circuit theorem.  A dense polynomial-size circuit can begin with
polynomially many incidences, and low incidence is not yet proved to imply low continuation boundary or treewidth.
The next load-bearing lemma must therefore either normalize/route this credit through separators, or prove that a
large remaining incidence potential exposes a restriction with sufficiently large amortized simplification.
-/

namespace PallLean.Paper93.DeepMath.PathB.FanoutAwareIncidencePotential

open Finset

variable {Gate Var : Type} [DecidableEq Gate] [DecidableEq Var]

/-- Live incidences in a shared circuit representation.  `gates` is a set, so downstream fanout does not duplicate
the gate's charge. -/
def incidenceCredit (gates : Finset Gate) (support : Gate → Finset Var) (live : Finset Var) : ℕ :=
  ∑ g ∈ gates, (support g ∩ live).card

/-- Current live degree of variable `v`: the number of represented gates whose live support contains it. -/
def liveDegree (gates : Finset Gate) (support : Gate → Finset Var) (live : Finset Var) (v : Var) : ℕ :=
  ∑ g ∈ gates, if v ∈ support g ∩ live then 1 else 0

/-- Per-gate accounting: deleting `v` from the live variables removes exactly the incidence at `v`, when present. -/
theorem card_inter_erase_add_indicator (S live : Finset Var) (v : Var) :
    (S ∩ live.erase v).card + (if v ∈ S ∩ live then 1 else 0) = (S ∩ live).card := by
  by_cases hv : v ∈ S ∩ live
  · have heq : S ∩ live.erase v = (S ∩ live).erase v := by
      ext x
      simp only [mem_inter, mem_erase]
      constructor
      · rintro ⟨hxS, hxv, hxlive⟩
        exact ⟨hxv, hxS, hxlive⟩
      · rintro ⟨hxv, hxS, hxlive⟩
        exact ⟨hxS, hxv, hxlive⟩
    have hcard : 0 < (S ∩ live).card := card_pos.mpr ⟨v, hv⟩
    rw [heq, card_erase_of_mem hv]
    simp only [if_pos hv]
    omega
  · have hnot : v ∉ S ∩ live := hv
    have heq : S ∩ live.erase v = S ∩ live := by
      ext x
      simp only [mem_inter, mem_erase]
      constructor
      · rintro ⟨hxS, _, hxlive⟩
        exact ⟨hxS, hxlive⟩
      · rintro ⟨hxS, hxlive⟩
        refine ⟨hxS, ?_, hxlive⟩
        intro hxv
        subst x
        have hvbad : v ∈ S ∩ live := Finset.mem_inter.mpr ⟨hxS, hxlive⟩
        exact hnot hvbad
    simp [heq, hv]

/-- **Exact restriction accounting (proved).**  Fixing `v` reduces the fanout-aware incidence credit by exactly
`liveDegree v`. -/
theorem erase_credit_add_degree (gates : Finset Gate) (support : Gate → Finset Var)
    (live : Finset Var) (v : Var) :
    incidenceCredit gates support (live.erase v) + liveDegree gates support live v
      = incidenceCredit gates support live := by
  induction gates using Finset.induction_on with
  | empty => simp [incidenceCredit, liveDegree]
  | @insert g gates hg ih =>
      simp only [incidenceCredit, liveDegree] at ih
      simp only [incidenceCredit, liveDegree, sum_insert, hg, not_false_eq_true]
      rw [Nat.add_add_add_comm, card_inter_erase_add_indicator (support g) live v, ih]

/-- A live occurrence earns at least one unit of potential decrease. -/
theorem erase_credit_strict_of_mem_support (gates : Finset Gate) (support : Gate → Finset Var)
    (live : Finset Var) (v : Var) (g : Gate) (hg : g ∈ gates) (hv : v ∈ support g ∩ live) :
    incidenceCredit gates support (live.erase v) < incidenceCredit gates support live := by
  have hdeg : 1 ≤ liveDegree gates support live v := by
    unfold liveDegree
    have hle := Finset.single_le_sum
      (s := gates) (f := fun h => if v ∈ support h ∩ live then 1 else 0)
      (fun _ _ => Nat.zero_le _) hg
    simpa [hv] using hle
  have hexact := erase_credit_add_degree gates support live v
  omega

/-- **Shared-gate idempotence.**  Listing an already-owned gate again does not change the credit.  This is the basic
fanout-neutrality law: references may multiply, but the shared gate is charged once. -/
theorem insert_owned_gate_neutral (gates : Finset Gate) (support : Gate → Finset Var)
    (live : Finset Var) (g : Gate) (hg : g ∈ gates) :
    incidenceCredit (insert g gates) support live = incidenceCredit gates support live := by
  rw [insert_eq_self.mpr hg]

/-- A single wide gate has incidence credit equal to the number of live variables it reads.  In particular, unlike
output entropy or active-gate count, its potential falls at every input restriction. -/
theorem single_wide_gate_credit (support : Gate → Finset Var) (live : Finset Var) (g : Gate)
    (hwide : live ⊆ support g) :
    incidenceCredit {g} support live = live.card := by
  simp [incidenceCredit, inter_eq_right.mpr hwide]

/-- **Dense-overlap stress test.**  If every represented gate reads every live variable, incidence credit is the
full gate-variable product.  This is the expander/reconvergence warning: exact local payment is not enough when the
potential starts much larger than the `n`-variable branching budget. -/
theorem dense_overlap_credit (gates : Finset Gate) (live : Finset Var) :
    incidenceCredit gates (fun _ => live) live = gates.card * live.card := by
  simp [incidenceCredit]

/-- With at least two dense gates and one live variable, the raw incidence potential already exceeds the number of
live variables.  A completion therefore needs separator ownership/normalization or an amortized high-overlap
simplification theorem; raw incidence credit alone cannot be inserted into the `saving ≤ n` cash-out certificate. -/
theorem dense_overlap_exceeds_variable_budget (gates : Finset Gate) (live : Finset Var)
    (hgates : 2 ≤ gates.card) (hlive : 0 < live.card) :
    live.card < incidenceCredit gates (fun _ => live) live := by
  rw [dense_overlap_credit]
  nlinarith

end PallLean.Paper93.DeepMath.PathB.FanoutAwareIncidencePotential

#print axioms PallLean.Paper93.DeepMath.PathB.FanoutAwareIncidencePotential.erase_credit_add_degree
#print axioms PallLean.Paper93.DeepMath.PathB.FanoutAwareIncidencePotential.erase_credit_strict_of_mem_support
#print axioms PallLean.Paper93.DeepMath.PathB.FanoutAwareIncidencePotential.insert_owned_gate_neutral
#print axioms PallLean.Paper93.DeepMath.PathB.FanoutAwareIncidencePotential.dense_overlap_exceeds_variable_budget
