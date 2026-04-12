# Move 1 Sheet Route (Archived 2026-04-12)

## Why archived

The 3-sheet `latentCompiledPoly = machCopySheet + copyConSheet + selConSheet` structure
cannot support the P-side locality counting argument from the paper (§17).

Products of B gadgets produce exponentially many monomials after Leibniz differentiation,
so the SPDP rank is NOT polynomial for product sheets. The paper uses
`P = 1 - Σ C²` (sum of squared constraints) which has polynomial rank by direct
locality/support counting.

The lane classification (Move 1) attempted to work around this by routing generators
through individual sheets, but the conSlot case proved intractable.

## What was achieved

- Lane routing bridge (uniform slot family → clean menu): PROVED
- ConSlot incompatibility with all 3 clean lanes: PROVED
- ConSlot derivative calculus on all sheets: PROVED
- iterDerivList transport helpers: PROVED
- NP-side identity minor via selConSheet: PROVED (but only for this polynomial)
- 20 build errors in CopyConClosedCoeffDecomp.lean: FIXED

## What was NOT achieved

- Lane classifier (block-admissible + nonzero generator → uniform slot family)
- ConSlot transport theorem (re-expression through copy/sel lanes)
- Removing hUniform precondition from latent_raw_bucket_member_enters_clean_lane

## Route change

Switching to the paper's actual polynomial (§17) with:
- P-side: locality counting (§17.3) → polynomial rank
- NP-side: Ramanujan-Tseitin expander families (§25) + God-Move (§29)
