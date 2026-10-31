import PallLean

/-! Post-fix axiom check for the main entry theorems of the default target `PallLean`
and for the former dependents of the two removed axioms.  Expected: no custom axiom
(in particular neither `PAC.gadget_spdp_subspace_factoring` nor
`MatrixSPDP.gadget_factoring_linearmap_form`, which no longer exist). -/

#print axioms Step4Compiler.P_ne_NP_Lean
#print axioms PaperFaithfulSeparation.separation_3sat
#print axioms PaperFaithfulSeparation.no_rank_sandwich_at_large_n
#print axioms PaperFaithfulSeparation.rank_sandwich_axiom_iff_no_bounded_sat_decider
#print axioms PaperFaithfulSeparation.isAmplituhedronGauge_uninhabited_for_sat_decider
#print axioms GodMoveReal.compiled_np_lower_bound_any_dtm
#print axioms GodMoveReal.compiledPoly_rank_gt_npow200_at_large_n
#print axioms GlobalGodMoveGauge.theorem207RawSourcePSideUpperBound_not_for_local_compiledPoly
#print axioms GlobalGodMoveGauge.theorem207PaperSource_transport_false
#print axioms Step4Compiler.P_side_rank_concrete_bound
#print axioms Step4Compiler.P_side_rank_concrete_lt_NP_side
#print axioms BinomialBound.binomial_lower_bound_concrete
-- former dependents (now take the refuted statement as an explicit hypothesis)
#print axioms PAC.gadget_multiplication_rank_bound
#print axioms PAC.gadgetMultOp
#print axioms MatrixSPDP.gadget_multiplication_rank_bound_matrix_form
-- the remaining (not refuted, zero-dependent) custom axiom in the closure
#print axioms PAC.gadget_spdp_subspace_factoring_paperFaithful
