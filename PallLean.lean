-- Core on-chain entrypoint: imports only what `P_ne_NP_unconditional` depends on.
-- Off-path / alternative-route / exploratory files have been moved to
-- `PallLean/Archive/` (see `PallLean.Archive` for the roll-up).

import PallLean.PaperFaithfulSeparation

-- On-chain utility modules also referenced directly by callers:
import PallLean.PACLeibniz
import PallLean.MatrixSPDP
import PallLean.PAC

-- Farkas/KKT soundness-certificate layer for the identity minor
-- (paper §18.1, Remark 43: "Lagrangian / PAC certificate")
import PallLean.IdentityMinorFarkas

-- Rank-monotonicity infrastructure for gauge construction (§40 step 1 lemma)
-- (paper Definition 6 / Lemma 7: Π_Φ rank-monotonicity)
import PallLean.GaugeMonotonicity

-- Concrete variable-substitution gauge (candidate Π⋆ construction)
-- (paper Definition 6(i): restrict tableau blocks to fixed constants)
import PallLean.PiStarConcrete

-- Representation-invariant formulation of the honest remaining lower-bound
-- bridge.  This minimizes CEW/SPDP-style cost over every representation of the
-- same Boolean function and keeps the SAT lower bound as an explicit premise.
import PallLean.SemanticEntanglementBridge

-- Infinite-state dynamic-SPDP graph/minimax formulation and the free-source
-- singleton-path collapse audit.
import PallLean.DynamicGraphEntanglement

-- Path A: paper-faithful u/v variable split for Cook-Levin compilation
-- (paper §§6, 29 Definition 7: distinguishing clause-sheet u from tableau v)
import PallLean.PaperFaithfulCompilation

-- Step 4: paper §40 Theorem 203 compiler pipeline scaffolding
-- (BranchingProgram, CEW, Width⇒Rank interface)
import PallLean.Step4Compiler
