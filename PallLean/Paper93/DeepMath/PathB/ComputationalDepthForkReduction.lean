import PallLean.Paper93.DeepMath.PathB.ComputationalDepthForkGame

/-!
# Phase 3, brick 3: the graph wiring of the Fork → `st`-connectivity reduction

`ForkGame` established the reduction's combinatorial core; this brick grinds the **graph wiring** —
instantiating the layered graph and proving `stconn (Alice) = 1` (connected) and `stconn (Bob) = 0`
(disconnected).  Vertices `Vtx` (`s`, `t`, or `node (layer) (value)`) and edges `Edg`
(`src`/`trans`/`snk`) are clean inductive types over `STConnectivity`'s general reachability.

* **`Vtx` / `Edg` / `ends`** — the layered graph;
* **`aliceX a`** — Alice's edge-set: the path `s → node 0 (a 0) → ⋯ → node ℓ (a ℓ) → t`;
* **`bobY b`** — Bob's edge-set: everything except the `b`-cut (`node i (b i) → node (i+1) v` with
  `v ≠ b (i+1)`, and `node ℓ (b ℓ) → t`);
* **`alice_connected` (proved)** — `stconn (ends ℓ) s t (aliceX ℓ a) = true` (the `a`-path);
* **`bobY_reach_inv` (proved)** — Bob's `s`-reachable set is exactly `{s} ∪ {node i (b i)}`;
* **`bob_disconnected` (proved)** — `stconn (ends ℓ) s t (bobY ℓ b) = false`.

Together with `ForkGame.fork_distinguishing_edge` and `STConnectivity.stconn_mkw_solvable`, the graph
side of the reduction is now fully formal.  **What remains: the protocol transfer to `mkwCC` (an
`ε = Fin m` transport) and — the wall — the Fork lower bound `ForkCC = Ω(log²)` (round elimination).**
Nothing here is a lower bound; ceiling is monotone-`P` ⊄ monotone-`NC¹`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ForkReduction

open PallLean.Paper93.DeepMath.PathB.STConnectivity

variable {w : ℕ}

/-- Vertices of the layered graph: source, sink, or a node `(layer i, value v)`. -/
inductive Vtx (w : ℕ)
  | s : Vtx w
  | t : Vtx w
  | node : ℕ → Fin w → Vtx w
  deriving DecidableEq

/-- Edges: source→layer-0, a layer transition, or layer-ℓ→sink. -/
inductive Edg (w : ℕ)
  | src : Fin w → Edg w
  | trans : ℕ → Fin w → Fin w → Edg w
  | snk : Fin w → Edg w
  deriving DecidableEq

/-- Edge endpoints (the sink edges land at layer `ℓ`). -/
def ends (ℓ : ℕ) : Edg w → Vtx w × Vtx w
  | .src v => (Vtx.s, Vtx.node 0 v)
  | .trans i u v => (Vtx.node i u, Vtx.node (i + 1) v)
  | .snk v => (Vtx.node ℓ v, Vtx.t)

/-- Alice's edge-set: exactly the path through `a`. -/
def aliceX (ℓ : ℕ) (a : ℕ → Fin w) : Edg w → Bool
  | .src v => decide (v = a 0)
  | .trans i u v => decide (i < ℓ ∧ u = a i ∧ v = a (i + 1))
  | .snk v => decide (v = a ℓ)

/-- Bob's edge-set: everything except the `b`-cut. -/
def bobY (ℓ : ℕ) (b : ℕ → Fin w) : Edg w → Bool
  | .src v => decide (v = b 0)
  | .trans i u v => decide (¬ (u = b i ∧ v ≠ b (i + 1)))
  | .snk v => decide (v ≠ b ℓ)

/-! ### Alice is connected -/

/-- Alice reaches `node i (a i)` for every layer `i ≤ ℓ`. -/
theorem alice_reach_node (ℓ : ℕ) (a : ℕ → Fin w) :
    ∀ i, i ≤ ℓ → Reach (ends ℓ) (aliceX ℓ a) Vtx.s (Vtx.node i (a i)) := by
  intro i
  induction i with
  | zero =>
    intro _
    have hx : aliceX ℓ a (Edg.src (a 0)) = true := by simp [aliceX]
    exact Reach.step (Edg.src (a 0)) (Reach.refl Vtx.s) hx rfl
  | succ i ih =>
    intro hi
    have hik : i < ℓ := by omega
    have hx : aliceX ℓ a (Edg.trans i (a i) (a (i + 1))) = true := by simp [aliceX, hik]
    exact Reach.step (Edg.trans i (a i) (a (i + 1))) (ih (by omega)) hx rfl

/-- **Alice's edge-set is connected (proved)**: `stconn (aliceX) = 1`. -/
theorem alice_connected (ℓ : ℕ) (a : ℕ → Fin w) :
    stconn (ends ℓ) Vtx.s Vtx.t (aliceX ℓ a) = true := by
  rw [stconn_true_iff]
  have hx : aliceX ℓ a (Edg.snk (a ℓ)) = true := by simp [aliceX]
  exact Reach.step (Edg.snk (a ℓ)) (alice_reach_node ℓ a ℓ (le_refl ℓ)) hx rfl

/-! ### Bob is disconnected -/

/-- Bob's reachable set from `s` is confined to `{s} ∪ {node i (b i)}`. -/
def bReachInv (b : ℕ → Fin w) (v : Vtx w) : Prop :=
  v = Vtx.s ∨ ∃ i, v = Vtx.node i (b i)

/-- **Bob's `s`-reachable set is exactly `{s} ∪ {node i (b i)}` (proved)** — the `b`-track. -/
theorem bobY_reach_inv (ℓ : ℕ) (b : ℕ → Fin w) {v : Vtx w}
    (h : Reach (ends ℓ) (bobY ℓ b) Vtx.s v) : bReachInv b v := by
  induction h with
  | refl => exact Or.inl rfl
  | step e h hx hb ih =>
    cases e with
    | src v0 =>
      have hv0 : v0 = b 0 := by simpa only [bobY, decide_eq_true_eq] using hx
      right; refine ⟨0, ?_⟩
      show Vtx.node 0 v0 = Vtx.node 0 (b 0)
      rw [hv0]
    | trans i u v0 =>
      rw [show (ends ℓ (Edg.trans i u v0)).1 = Vtx.node i u from rfl] at hb
      rw [← hb] at ih
      rcases ih with hh | ⟨j, hj⟩
      · exact absurd hh (by simp)
      · have hji : i = j ∧ u = b j := by injection hj with h1 h2; exact ⟨h1, h2⟩
        have hubi : u = b i := by rw [hji.1]; exact hji.2
        have hxx : ¬ (u = b i ∧ v0 ≠ b (i + 1)) := by
          simpa only [bobY, decide_eq_true_eq] using hx
        have hv : v0 = b (i + 1) := by by_contra hc; exact hxx ⟨hubi, hc⟩
        right; refine ⟨i + 1, ?_⟩
        show Vtx.node (i + 1) v0 = Vtx.node (i + 1) (b (i + 1))
        rw [hv]
    | snk v0 =>
      rw [show (ends ℓ (Edg.snk v0)).1 = Vtx.node ℓ v0 from rfl] at hb
      rw [← hb] at ih
      rcases ih with hh | ⟨j, hj⟩
      · exact absurd hh (by simp)
      · have hji : ℓ = j ∧ v0 = b j := by injection hj with h1 h2; exact ⟨h1, h2⟩
        have hv : v0 = b ℓ := by rw [hji.1]; exact hji.2
        have hxx : v0 ≠ b ℓ := by simpa only [bobY, decide_eq_true_eq] using hx
        exact absurd hv hxx

/-- **Bob's edge-set is disconnected (proved)**: `stconn (bobY) = 0` — `t` is off the `b`-track. -/
theorem bob_disconnected (ℓ : ℕ) (b : ℕ → Fin w) :
    stconn (ends ℓ) Vtx.s Vtx.t (bobY ℓ b) = false := by
  rw [stconn_false_iff]
  intro h
  rcases bobY_reach_inv ℓ b h with h1 | ⟨j, hj⟩
  · exact absurd h1 (by simp)
  · exact absurd hj (by simp)

end PallLean.Paper93.DeepMath.PathB.ForkReduction

#print axioms PallLean.Paper93.DeepMath.PathB.ForkReduction.alice_connected
#print axioms PallLean.Paper93.DeepMath.PathB.ForkReduction.bob_disconnected
