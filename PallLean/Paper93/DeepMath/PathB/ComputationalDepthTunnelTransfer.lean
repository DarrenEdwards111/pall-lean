import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTreeClearsWall

/-!
# "Quantum tunnelling is the transfer" — the tunnel *is* the wall, and the Lagrangian tunnel is `L_H`

Darren's idea: the tree→DAG transfer (the wall) is crossed by *tunnelling*, powered by the N-Frame
Lagrangian.  This file takes the metaphor precisely and shows where it lands — honestly.

A **tunnel** is the reverse of the proved obstruction `dagCost ≤ treeCost`: a transfer
`treeCost d ≤ dagCost d` that brings the tree's superpoly bound *down* to the DAG.

* **`tunnel_iff_no_sharing` (proved)** — the decisive one: a tunnel exists **iff** `dagCost = treeCost`
  at every level.  Because `dagCost ≤ treeCost` always holds, a tunnel forces equality — which is exactly
  the **no-sharing hypothesis**, i.e. `cost_super`, the open wall.  **The tunnel is not a way around the
  wall; it *is* the wall.**
* **`tunnel_gives_separation` (proved)** — a tunnel yields the DAG superpoly bound (clears every
  ceiling), i.e. the separation.  So a tunnel is the whole problem, not a shortcut through it.
* **`tunnel_dichotomy` (proved)** — where the N-Frame Lagrangian enters: a tunnel comes either from a
  *standard-model* source — which `tunnel_iff_no_sharing` shows *is* the no-sharing wall (open) — or from
  the Lagrangian's `L_H` term, which by `LagrangianDilemma` (commit `ca7f5764`) is **hypercomputational**,
  outside the standard model where P vs NP is defined.  Neither is a free standard-model crossing.

## The physics, honestly

- **Classical amplitude is zero.**  `dagCost ≤ treeCost` (`TreeClearsWall.dag_no_free_transfer`) points
  the wrong way: there is no classical transfer of the tree bound to the DAG.
- **The quantum amplitude is negligible.**  Tunnelling amplitude is exponentially small — in this
  register, an exp-small amplitude is not a poly-size circuit; it proves no lower bound.
- **The only tunnel the Lagrangian supplies is `L_H`** — hypercomputational by the book's own definition.
  Using it steps *outside* the standard Turing model, so it is not a standard-model proof of P vs NP.

**Honest scope.**  Proved: a tunnel is logically identical to the no-sharing wall, and yields the
separation.  So tunnelling does not go *around* the wall — a standard-model tunnel is the open lemma
`cost_super`, and the Lagrangian tunnel is `L_H`, hypercomputational.  Nothing here crosses the wall in
the standard model, and nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TunnelTransfer

open PallLean.Paper93.DeepMath.PathB.TreeClearsWall

/-- A **tunnel**: the reverse of the proved obstruction — a transfer `treeCost d ≤ dagCost d` bringing
the tree's superpoly bound down to the DAG. -/
def Tunnel (T : Tower) : Prop := ∀ d, T.treeCost d ≤ T.dagCost d

/-- **The tunnel IS the wall (proved).**  Since `dagCost ≤ treeCost` always holds, a tunnel
(`treeCost ≤ dagCost`) forces `dagCost = treeCost` at every level — exactly the no-sharing hypothesis
(`cost_super`).  Tunnelling does not go around the wall; it equals it. -/
theorem tunnel_iff_no_sharing (T : Tower) :
    Tunnel T ↔ ∀ d, T.dagCost d = T.treeCost d := by
  constructor
  · intro htun d
    exact Nat.le_antisymm (T.dag_le_tree d) (htun d)
  · intro htight d
    exact Nat.le_of_eq (htight d).symm

/-- **A tunnel yields the separation (proved).**  Given a tunnel, the DAG cost clears every ceiling —
the DAG superpoly bound, i.e. the separation.  The tunnel is the whole problem, not a shortcut. -/
theorem tunnel_gives_separation (T : Tower) (htun : Tunnel T) (U : ℕ) :
    ∃ d, U < T.dagCost d :=
  dag_clears_ceiling_of_no_sharing T ((tunnel_iff_no_sharing T).mp htun) U

/-- **The tunnel dichotomy (proved).**  A tunnel comes from one of two sources: a **standard-model**
source, which `tunnel_iff_no_sharing` identifies as the no-sharing wall itself (`cost_super`, open); or
the N-Frame Lagrangian's **`L_H`** term, which by `LagrangianDilemma` is hypercomputational — outside the
standard model where P vs NP is defined.  Whichever it is, it is not a free standard-model crossing. -/
theorem tunnel_dichotomy (T : Tower) (Standard Hyper : Prop)
    (source : Standard ∨ Hyper)
    (std_is_nosharing : Standard → (∀ d, T.dagCost d = T.treeCost d))
    (hyper_tunnels : Hyper → Tunnel T) :
    Tunnel T := by
  cases source with
  | inl hs => exact (tunnel_iff_no_sharing T).mpr (std_is_nosharing hs)
  | inr hh => exact hyper_tunnels hh

end PallLean.Paper93.DeepMath.PathB.TunnelTransfer

#print axioms PallLean.Paper93.DeepMath.PathB.TunnelTransfer.tunnel_iff_no_sharing
#print axioms PallLean.Paper93.DeepMath.PathB.TunnelTransfer.tunnel_gives_separation
#print axioms PallLean.Paper93.DeepMath.PathB.TunnelTransfer.tunnel_dichotomy
