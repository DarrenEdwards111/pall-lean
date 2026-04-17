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
