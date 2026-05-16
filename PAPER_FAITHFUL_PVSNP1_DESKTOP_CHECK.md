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

## 2026-05-16 re-check — best paper-faithful next move

Source: `/mnt/c/Users/darre/Desktop/p vs np1.pdf`, text extracted from workspace copy. Relevant anchors:

- Definition 19 / Lemma 22 around PDF text lines ~1800-1859: profile spaces are tensor/symmetric-power products, not a single slot space. Quote: `V_h := ⊗_{τ∈T} Sym^{h(τ)}(W_τ)` and `RowSpan(R_h) ⊆ V_h`.
- Lemma 31 around lines ~2106-2183: for each profile `h`, each interface contribution lies in the corresponding `W_σ`, and the aggregate lies in the tensor product. Quote: `each interface contribution lies in the corresponding W_σ, and the aggregate over all interfaces lies in the indicated tensor product`.
- Therefore the best Lean move is **not** to force a whole global type segment (all booleanity factors, all adjacency factors, etc.) into one `W_σ`. That is too strong and not paper-faithful. The paper-faithful socket is: assign factors to actual local interfaces / compressed normal-form slots, prove each interface-slot contribution is in `W_σ`, then assemble the profile aggregate via `profileSubspace` / symmetric product constructors.
- Dormant types are handled by profile multiplicity `h(τ)=0`. For the current finite alphabet this means selected profiles used by the three actual Cook-Levin branches need `h transitionRight = 0`, or the construction must provide real transition-right local contributions.

Recommended next Lean move: refactor the current segment-slot attempt into an **interface-slot / normal-form-slot classifier**. Keep the segment lemmas only as branch-shape support. Prove per-slot contributions into `interfaceSpace_compiledBasis`; use existing `profileProduct_mem_profileSubspace` / `profileSlotExpansion_mem_profileSubspace` for the aggregate. Do not pursue the one-whole-segment-per-type `factorSlotFiber` as final Lemma 31 closure.
