# Paper-faithfulness check against Desktop `p vs np1.pdf`

Date: 2026-05-13
Source checked: `/mnt/c/Users/darre/Desktop/p vs np1.pdf` (copied to workspace as `p-vs-np1.pdf` and text-extracted to `p-vs-np1.txt`).

## Confirmed paper anchors present in Desktop PDF

- **Route B explicitly marked primary**: text around line 660 (`Route B (primary)` and why primary at lines ~664-671).
- **Canonical windows / normal forms / profiles**: section entry and body at lines ~1967 onward.
- **Bounded normal forms**: Lemma 25 at line ~2011.
- **Profile compression**: Lemma 29 and corollary at lines ~2076 onward.
- **Within-profile subspace theorem**: **Lemma 31** at line ~2148.
- **Width⇒Rank composition over profiles**: Theorem 23 / Lemma 32 discussions at ~1901 and ~2258 onward.

## Route-B Lean alignment status

The active PathB chain now has a direct canonical closure surface:

- `P_ne_NP_canonical_routeB_canonicalInterfaceExpansion_conditional`

and composes through existing checked adapters:

- canonical-interface expansion -> placed quotient/descent -> no bounded SAT decider -> `PeqNP_Paper -> False`.

Axiom audit on this closure remains classical-only:

- `propext`, `Classical.choice`, `Quot.sound`.

## Remaining constructive gap (honest)

To make the closure unconditional, the remaining work is still constructive witness production for the Step247 uniform canonical-interface (or equivalent Route-B seam witness), i.e. proving the witness data object itself rather than assuming it.

This is exactly the paper-faithful frontier corresponding to the profile/subspace constructive obligations around Lemma 31 + compiled canonical-window machinery.
