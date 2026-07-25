import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSTConnectivity

/-!
# Phase 3, brick 2: the Fork game and the reduction to `st`-connectivity

The Karchmer–Wigderson `Ω(log²n)` lower bound for `st`-connectivity factors through the **Fork
game**: Alice holds a sequence `a`, Bob holds `b` (length `ℓ+1` over `[w]`), promised to **agree at
position `0`** and **differ at position `ℓ`**; they must output a **fork** — a position `i < ℓ` with
`a i = b i` and `a(i+1) ≠ b(i+1)` (where agreement flips to disagreement).

This brick defines the game, proves it is **well-posed** (a fork always exists — the Fork analogue of
`reach_cut_crossing`), and establishes the **combinatorial core of the reduction**.

## The reduction (worked out)
Layered graph, `ℓ+1` layers of `w` nodes, plus `s, t`.  Alice's edge-set `x` = the path
`s → (0,a₀) → (1,a₁) → ⋯ → (ℓ,a_ℓ) → t` (connected).  Bob's edge-set `y` = every layered edge
**except** the transitions `(i,bᵢ) → (i+1,v)` with `v ≠ b_{i+1}`, and except `(ℓ,b_ℓ) → t`.  Then:
* `y` is **disconnected** — its `s`-reachable set is exactly `{s} ∪ {(i,bᵢ)}`, and `(ℓ,b_ℓ)→t ∉ y`;
* an edge of Alice's path is **absent from `y` iff it is a fork** — the tail `(i, aᵢ)` equals `(i, bᵢ)`
  and the head `(i+1, a_{i+1})` differs from `(i+1, b_{i+1})`.

So the monotone-KW distinguishing edge (guaranteed by `reach_cut_crossing`) *is* a fork, and a
connectivity protocol solves Fork at the same cost — hence `mkwCC(stconn) ≥ ForkCC`.

* **`IsFork`** — the fork predicate; **`fork_exists` (proved)** — well-posedness;
* **`bExcludes`** — Bob's cut on transitions; **`alice_edge_excluded_iff_fork` (proved)** — the core
  correspondence: Alice's transition edge is Bob-excluded ↔ it is a fork.

**Honest scope.**  This is the reduction's combinatorial heart, proved.  What remains: (i) instantiate
the layered graph as concrete `ends : Fin m → Fin V × Fin V` and prove `stconn x = 1`, `stconn y = 0`
via `Reach` (mechanical but substantial); (ii) the protocol transfer `mkwCC(stconn) ≥ ForkCC`; and
(iii) — the research wall — the **Fork lower bound** `ForkCC = Ω(log²)` (round elimination), which no
elementary rectangle/fooling argument reaches.  Nothing here is a lower bound yet.
-/

namespace PallLean.Paper93.DeepMath.PathB.ForkGame

open PallLean.Paper93.DeepMath.PathB.STConnectivity

variable {w : ℕ}

/-- A **fork** of the pair `(a, b)` at length `ℓ`: a position `i < ℓ` where agreement (`a i = b i`)
flips to disagreement (`a (i+1) ≠ b (i+1)`). -/
def IsFork (ℓ : ℕ) (a b : ℕ → Fin w) (i : ℕ) : Prop :=
  i < ℓ ∧ a i = b i ∧ a (i + 1) ≠ b (i + 1)

/-- **The Fork game is well-posed (proved)** — the Fork analogue of `reach_cut_crossing`.  Agreement
at `0` and disagreement at `ℓ` force a fork: take the first disagreement `j`; `j ≥ 1`, and `j-1` is a
fork. -/
theorem fork_exists (ℓ : ℕ) (a b : ℕ → Fin w) (h0 : a 0 = b 0) (hℓ : a ℓ ≠ b ℓ) :
    ∃ i, IsFork ℓ a b i := by
  classical
  have hex : ∃ j, a j ≠ b j := ⟨ℓ, hℓ⟩
  have hj : a (Nat.find hex) ≠ b (Nat.find hex) := Nat.find_spec hex
  have hjle : Nat.find hex ≤ ℓ := Nat.find_le hℓ
  have hj0 : Nat.find hex ≠ 0 := fun h => hj (h ▸ h0)
  refine ⟨Nat.find hex - 1, ?_, ?_, ?_⟩
  · omega
  · have hlt : Nat.find hex - 1 < Nat.find hex := by omega
    exact not_not.mp (Nat.find_min hex hlt)
  · have he : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [he]; exact hj

/-- **Bob's cut** on a transition `(i, u) → (i+1, v)`: excluded exactly when the tail is on the
`b`-track (`u = b i`) but the head leaves it (`v ≠ b (i+1)`). -/
def bExcludes (b : ℕ → Fin w) (i : ℕ) (u v : Fin w) : Prop :=
  u = b i ∧ v ≠ b (i + 1)

/-- **The reduction correspondence (proved)**: Alice's transition edge from `a i` to `a (i+1)` is
excluded by Bob's cut **iff** the pair forks at `i`.  So the monotone-KW distinguishing edge is a
fork. -/
theorem alice_edge_excluded_iff_fork (ℓ : ℕ) (a b : ℕ → Fin w) (i : ℕ) (hi : i < ℓ) :
    bExcludes b i (a i) (a (i + 1)) ↔ IsFork ℓ a b i := by
  unfold bExcludes IsFork
  exact ⟨fun ⟨h1, h2⟩ => ⟨hi, h1, h2⟩, fun ⟨_, h1, h2⟩ => ⟨h1, h2⟩⟩

/-- **The reduction, packaged (proved)**: for a promise-satisfying Fork instance there is a fork whose
Alice-edge Bob excludes — i.e. a distinguishing edge exists and it names a fork.  This is the exact
seed a connectivity protocol would consume; the graph wiring and the Fork lower bound remain. -/
theorem fork_distinguishing_edge (ℓ : ℕ) (a b : ℕ → Fin w) (h0 : a 0 = b 0) (hℓ : a ℓ ≠ b ℓ) :
    ∃ i, IsFork ℓ a b i ∧ bExcludes b i (a i) (a (i + 1)) := by
  obtain ⟨i, hi⟩ := fork_exists ℓ a b h0 hℓ
  exact ⟨i, hi, (alice_edge_excluded_iff_fork ℓ a b i hi.1).mpr hi⟩

end PallLean.Paper93.DeepMath.PathB.ForkGame

#print axioms PallLean.Paper93.DeepMath.PathB.ForkGame.fork_exists
#print axioms PallLean.Paper93.DeepMath.PathB.ForkGame.alice_edge_excluded_iff_fork
#print axioms PallLean.Paper93.DeepMath.PathB.ForkGame.fork_distinguishing_edge
