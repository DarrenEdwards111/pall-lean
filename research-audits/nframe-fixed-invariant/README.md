# Fixed N-Frame invariant: concrete implementation check

For the subsequent desktop-paper God-Move work, see
[GodMoveGapRepairs.md](GodMoveGapRepairs.md). That report separates constructive
product/common-span repairs from the unresolved separation obligations.

2026-09-09. The user requires keeping the N-Frame invariant, not replacing it with surrogate entropies or cut sums.

This check imports FullLagrangianFixed unchanged. With alpha>=0 and beta=gamma=1, the action is alpha times edge energy + r + 1/(1+r). For every r>=0, r+1/(1+r)>=1. The repository's trivialObserverGauge has zero coordinates and zero projection rank, so its action is exactly 1. Hence it is a global minimizer over ObserverGauge N for these allowed positive rank/barrier coefficients.

This contradicts the unconditional explanatory claim in LogDetBarrier.lean that its structural penalty prevents the zero gauge from minimizing the action. It does not refute a genuine logarithmic-determinant barrier on a positive-definite domain, nor an additional admissibility condition that excludes the zero gauge. Those are not supplied by this concrete action/type.

The actual barrier definition is 1/(1+rank), bounded even at zero rank. No production definition is changed by this audit. No substitute invariant is introduced.

DynamicNFrameLagrangianInvariant still takes stateActionRank as a field; StrictDynamicNFrameLagrangianInvariant takes configActionRank. CanonicalDynamicNFrameInvariant instead inserts a binomial scale by SAT semantics and ignores time in its liveBoundaryRank. These interfaces do not construct a machine-selected minimizer of this action.

The next genuine implementation obligation is an admissible gauge domain and machine-to-gauge evolution justified by the intended geometry. Simply deleting the zero gauge or assigning a hard rank would not establish the desired runtime theorem. This check does not construct that evolution or prove SAT hardness.

Reproduce the focused check with:

    /home/darre/.elan/bin/lake env lean research-audits/nframe-fixed-invariant/ZeroGaugeMinimum.lean
