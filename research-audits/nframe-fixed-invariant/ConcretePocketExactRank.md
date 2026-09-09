# Following the existing concrete Theorem 207 gadget

This attempt uses the existing `compiledGadget` and `pocketFamily`, without
changing either definition or the analytic N-Frame action.

`compiledGadget alpha n` is alpha I + L(K_n). For alpha > 0 and n >= 1,
the existing Path B positive-definiteness proof makes it invertible, hence
its matrix rank is exactly n. The existing block-diagonal rank theorem then
gives rank(pocketFamily alpha kappa n) = kappa*n.

`ConcretePocketExactRank.lean` verifies these exact identities. The lower bound
kappa <= rank in `DeepMath/CookLevin/Theorem207Statement.lean` is therefore a
lower bound on an already full-rank matrix of dimension kappa*n. Neither its
statement nor these concrete gadget definitions takes a SAT formula, a machine
transition function, or a computation state.

The adjacent `CompiledTM.lean` constructs `compiledTMMatrix` by reindexing this
same gadget using a set of (state,symbol,time) labels. Its inputs are the three
counts and alpha, not a transition table or formula. Thus equal counts produce
the same matrix regardless of computation semantics. This is a statement about
this concrete wrapper, not about every Cook-Levin compiler in the repository.

## Consequence for the intended derivation

Choosing many pockets establishes high rank by increasing the constructed
matrix dimension. It does not show why every correct decider must expose those
pockets or pay to realize them. If represented implicitly, high ambient dimension
still needs a proved operation-cost connection. The exact-rank calculation is
valid, but does not provide that connection or a SAT-specific lower bound.

The analytic minimizer theorem `SNFMinimizerFull.lean` takes its compact domain K
as a supplied set of (phi,A) pairs. This permits coupled domains but does not
construct the particular SAT/machine-dependent coupling. The serious Route B
core in `Paper283/FullChain283.lean` likewise supplies local energy-to-rank and
log-det sandwich hypotheses. Those obligations are not discharged by the
full-rank pocket calculation.

This result neither replaces nor refutes the intended dynamic invariant. It
identifies what the existing concrete gadget theorem proves and what additional
semantic connection is still required. No completed separation is claimed.

Verification:
    lake build PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef PallLean.Paper93.DeepMath.BridgeB.PocketFamilyRank
    lake env lean research-audits/nframe-fixed-invariant/ConcretePocketExactRank.lean
