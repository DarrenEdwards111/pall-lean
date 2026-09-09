# Single-defect incidence fields beyond cycles

The N-Frame localEnergy and parityViolation definitions are unchanged.

## Construction on every connected odd-order simple graph

Store each undirected edge once in RegularGraphFixed.edges. Give every
vertex charge -1 and choose a root r. The desired vertex field is +1 at r
and -1 everywhere else. For odd N its product is +1.

Choose a rooted spanning tree and set all non-tree edge signs to +1.
Process non-root vertices from leaves upwards. At v choose the sign of
its parent edge to make the product of all incident edge signs equal to
the desired field at v. This fixes v without changing any already fixed
descendant. Afterward all non-root vertices have the desired product.
Every edge sign occurs twice in the product of all induced vertex fields,
so that product is +1. The target also has product +1; therefore the root
is correct automatically. This proves existence and gives a construction
using a traversal and constant work per edge/vertex.

In contrast, the charge product is -1. Thus the original signed parity
constraints cannot all hold, since multiplying vertex equations would
require +1=-1. The construction realizes one violated vertex, not a
satisfying assignment.

## Exact unchanged energy

For this field, parityViolation is 2 at the root and zero elsewhere.
Squared differences are 4 exactly on edges incident to the root and zero
elsewhere. Each stored edge is counted at both endpoints in localEnergy.
Consequently the total local energy is

    8 alpha degree(r) + 2 beta.

For positive alpha,beta, only r and its neighbors have positive energy.
With fixed maximum degree d and fixed coefficients, both total energy
and number of positive-energy sites are bounded independently of N.
For bidirected storage the edge contribution doubles; it is still bounded
at fixed degree. The Lean formula below counts the actual stored edge set
and does not require either convention.

This construction applies to every connected graph of odd order, and hence
also to any such bounded-degree expander. No claim is made that the numerical
circulant test graphs form an expander family. Expansion alone cannot
prevent this construction for the all-negative charge family.

## Verification boundary

Lean verifies, for every RegularGraphFixed graph, root and vertex:
* the squared difference identity for the single-defect field;
* the exact parity penalty;
* localEnergy equals 4 alpha times the number of stored root-crossing edges
  incident to that vertex, plus the root's 2 beta penalty.

The spanning-tree existence proof and the summed degree formula are the
written derivations above, NOT Lean-verified theorems in this commit.
single_defect_tree.py implements the tree construction and checks its induced
field and energy exactly on 614 graph instances: cycles, 4-regular circulants,
complete graphs, and seeded random connected graphs. All passed.

## What this does and does not resolve

This strengthens the previous cycle example: graph expansion does not by
itself force extensive local energy in this explicit charge family, even
after imposing an actual signed-edge incidence map. It is not a counterexample
to every hard charge family, nor to a trajectory-dependent lower bound, nor
to the full analytic action with a coupled gadget matrix. It does not
construct the intended holographic machine map.

An arbitrary SAT decider also need not evolve toward a satisfying field on
an inconsistent instance. A proof that it must pay the proposed dynamic cost
is still required. No universal runtime lower bound or separation is claimed.

Commands:

    lake env lean research-audits/nframe-fixed-invariant/SingleDefectEnergy.lean
    python3 research-audits/nframe-fixed-invariant/single_defect_tree.py

The Lean theorem uses only propext, Classical.choice and Quot.sound.
