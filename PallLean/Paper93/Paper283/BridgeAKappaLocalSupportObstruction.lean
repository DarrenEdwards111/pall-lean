import PallLean.Paper93.Paper283.BridgeAKappaGeneralCookLevinLocalBlock

/-!
# Support-size obstruction for arbitrary-kappa local Bridge A

`BridgeAKappaGeneralCookLevinLocalBlock` reduces the arbitrary-`kappa` local
Bridge A theorem to a family of `kappa` independent strict-`kappa` derivative
rows of the real local product `cookLevinLocalBlockQ`.

This file records the corresponding sharp obstruction: with the strict
`mlBlockedSpdpRank` convention, no polynomial whose variable support has
cardinality `< kappa` can have nonzero strict-`kappa` blocked SPDP rank.  Thus
an unconditional paper-scale local theorem must first prove that the selected
compiler-local product genuinely exposes at least `kappa` distinct variables.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open SPDP

attribute [local instance] Classical.dec

/-- If a strict derivative list has length larger than `p.vars.card`, then it
contains a variable outside `p.vars`, hence its iterated derivative of `p`
vanishes. -/
theorem iterDerivList_eq_zero_of_vars_card_lt_length
    {N : Nat} (p : MvPolynomial (Fin N) Rat) (S : List (Fin N))
    (hS : S.Nodup) (hvars : p.vars.card < S.length) :
    iterDerivList S p = 0 := by
  classical
  have hcardS : S.toFinset.card = S.length :=
    List.toFinset_card_of_nodup hS
  have hnot_sub : ¬ S.toFinset ⊆ p.vars := by
    intro hsub
    have hle : S.toFinset.card ≤ p.vars.card :=
      Finset.card_le_card hsub
    omega
  have hex : ∃ v, v ∈ S.toFinset ∧ v ∉ p.vars := by
    by_contra h
    apply hnot_sub
    intro v hvS
    by_contra hvp
    exact h ⟨v, hvS, hvp⟩
  rcases hex with ⟨v, hvS, hvp⟩
  exact
    IterDerivHelpers.iterDerivList_eq_zero_of_mem_notMem_vars
      S v p (by simpa using hvS) hvp

/-- Strict blocked SPDP rank vanishes above the polynomial's actual variable
support size.  This is stronger than the ambient-variable obstruction: it
applies even when the ambient ring is large, but the local product only uses a
small subset of variables. -/
theorem mlBlockedSpdpSubspace_eq_bot_of_vars_card_lt_kappa
    {N : Nat} (B : BlockPartition N) (kappa ell : Nat)
    (p : MvPolynomial (Fin N) Rat) (hvars : p.vars.card < kappa) :
    mlBlockedSpdpSubspace B kappa ell p = ⊥ := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro q ⟨S, m, hlen, _hdeg, _hvars, hadm, hq⟩
    have hzero :
        iterDerivList S p = 0 :=
      iterDerivList_eq_zero_of_vars_card_lt_length p S hadm.1 (by omega)
    rw [hq, hzero, mul_zero, mlProj_zero]
    exact Submodule.zero_mem ⊥
  · exact bot_le

/-- Rank form of `mlBlockedSpdpSubspace_eq_bot_of_vars_card_lt_kappa`. -/
theorem mlBlockedSpdpRank_eq_zero_of_vars_card_lt_kappa
    {N : Nat} (B : BlockPartition N) (kappa ell : Nat)
    (p : MvPolynomial (Fin N) Rat) (hvars : p.vars.card < kappa) :
    mlBlockedSpdpRank B kappa ell p = 0 := by
  unfold mlBlockedSpdpRank
  rw [mlBlockedSpdpSubspace_eq_bot_of_vars_card_lt_kappa B kappa ell p hvars]
  simp

/-- The real Cook-Levin local block product has zero strict-`kappa` rank
whenever its actual variable support has cardinality `< kappa`. -/
theorem cookLevinLocalBlockQ_rank_eq_zero_of_vars_card_lt_kappa
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (kappa ell : Nat)
    (b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks)
    (hvars :
      (cookLevinLocalBlockQ M n hn htb hns b).vars.card < kappa) :
    mlBlockedSpdpRank
        (cook_levin_compilation M n hn htb hns).partition
        kappa ell
        (cookLevinLocalBlockQ M n hn htb hns b) = 0 := by
  exact
    mlBlockedSpdpRank_eq_zero_of_vars_card_lt_kappa
      (cook_levin_compilation M n hn htb hns).partition
      kappa ell
      (cookLevinLocalBlockQ M n hn htb hns b)
      hvars

/-- Consequently, a positive strict-`kappa` lower bound for the real local
block product is impossible below support size `kappa`. -/
theorem not_cookLevinLocalBlockQ_rank_ge_of_vars_card_lt_kappa
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (kappa ell : Nat) (hkappa : 0 < kappa)
    (b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks)
    (hvars :
      (cookLevinLocalBlockQ M n hn htb hns b).vars.card < kappa) :
    ¬ kappa ≤
        mlBlockedSpdpRank
          (cook_levin_compilation M n hn htb hns).partition
          kappa ell
          (cookLevinLocalBlockQ M n hn htb hns b) := by
  intro hrank
  rw [cookLevinLocalBlockQ_rank_eq_zero_of_vars_card_lt_kappa
    M n hn htb hns kappa ell b hvars] at hrank
  omega

/-! ## Axiom audit anchors -/

#print axioms iterDerivList_eq_zero_of_vars_card_lt_length
#print axioms mlBlockedSpdpSubspace_eq_bot_of_vars_card_lt_kappa
#print axioms mlBlockedSpdpRank_eq_zero_of_vars_card_lt_kappa
#print axioms cookLevinLocalBlockQ_rank_eq_zero_of_vars_card_lt_kappa
#print axioms not_cookLevinLocalBlockQ_rank_ge_of_vars_card_lt_kappa

end PallLean.Paper93.Paper283
