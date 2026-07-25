import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMonotoneKW

/-!
# Phase 3, brick 1: the `st`-connectivity function and its monotone KW game

The monotone KW machine (`MonotoneKW`) is complete; Phase 3 needs an explicit monotone function whose
KW game has a super-log communication lower bound.  The classical target is **`st`-connectivity**
(Karchmer–Wigderson 1988).  This brick sets it up: reachability, the connectivity function, its
monotonicity, and the **cut-crossing lemma** — the fact that its monotone KW game is always solvable
via an `s`-`t` cut, the seed of the Fork-game lower bound.

Vertices are an arbitrary type `α`, edges an arbitrary type `ε`, with endpoints `ends : ε → α × α`
(edge `e` runs `(ends e).1 → (ends e).2`).  Keeping edges a general type lets the Fork reduction use
clean inductive vertex/edge types; taking `ε = Fin m` recovers the `(Fin m → Bool) → Bool` form that
plugs into `mkwCC` / `mdepth`.

* **`Reach ends x`** — reachability using only edges `e` with `x e = true`;
* **`stconn`** — `stconn ends s t x = 1` iff `t` is reachable from `s`; `stconn_true_iff` / `_false_iff`;
* **`Reach_mono` / `stconn_mono`** — connectivity is monotone in the edge set;
* **`reach_cut_crossing` (proved)** — an `x`-path from `s` to a vertex not `y`-reachable from `s` must
  cross the `y`-reachability frontier: a crossing edge is present in `x`, absent in `y`;
* **`stconn_mkw_solvable` (proved)** — the monotone KW game for `st`-connectivity is solvable.

Nothing here is a lower bound yet — that is Phase 3's Fork-game argument.  Ceiling of the whole
programme: monotone-`P` ⊄ monotone-`NC¹`, not `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.STConnectivity

open PallLean.Paper93.DeepMath.PathB.Khrapchenko
open PallLean.Paper93.DeepMath.PathB.MonotoneKW
open Classical

variable {α ε : Type*}

/-- Reachability in the directed graph on vertices `α` with edges `ε` (endpoints `ends`), using only
edges `e` with `x e = true`. -/
inductive Reach (ends : ε → α × α) (x : ε → Bool) : α → α → Prop
  | refl (a : α) : Reach ends x a a
  | step {a b : α} (e : ε) (h : Reach ends x a b) (hx : x e = true)
      (hb : (ends e).1 = b) : Reach ends x a (ends e).2

/-- **Directed `st`-connectivity** as a Boolean function of the edge-indicator input. -/
noncomputable def stconn (ends : ε → α × α) (s t : α) (x : ε → Bool) : Bool :=
  decide (Reach ends x s t)

theorem stconn_true_iff (ends : ε → α × α) (s t : α) (x : ε → Bool) :
    stconn ends s t x = true ↔ Reach ends x s t := by
  simp only [stconn, decide_eq_true_eq]

theorem stconn_false_iff (ends : ε → α × α) (s t : α) (x : ε → Bool) :
    stconn ends s t x = false ↔ ¬ Reach ends x s t := by
  simp only [stconn, decide_eq_false_iff_not]

/-- **Reachability is monotone in the edge set (proved).** -/
theorem Reach_mono (ends : ε → α × α) {x y : ε → Bool} (hxy : ∀ e, x e ≤ y e)
    {a b : α} (h : Reach ends x a b) : Reach ends y a b := by
  induction h with
  | refl => exact Reach.refl _
  | step e h hx hb ih =>
    have hye : y e = true := by
      have h' := hxy e; rw [hx] at h'; revert h'; cases y e <;> decide
    exact Reach.step e ih hye hb

/-- **`st`-connectivity is monotone (proved).** -/
theorem stconn_mono (ends : ε → α × α) (s t : α) {x y : ε → Bool}
    (hxy : ∀ e, x e ≤ y e) : stconn ends s t x ≤ stconn ends s t y := by
  by_cases h : Reach ends x s t
  · have hy : stconn ends s t y = true := (stconn_true_iff ends s t y).mpr (Reach_mono ends hxy h)
    rw [hy]; exact Bool.le_true _
  · have hx : stconn ends s t x = false := (stconn_false_iff ends s t x).mpr h
    rw [hx]; exact Bool.false_le _

/-- **The cut-crossing lemma (proved)** — the heart of the monotone KW game for `st`-connectivity.
An `x`-path from `s` to a vertex `v` that is not `y`-reachable from `s` must cross the `y`-reachability
frontier: some edge on it is present in `x` but absent in `y`. -/
theorem reach_cut_crossing (ends : ε → α × α) (s : α) {x y : ε → Bool}
    {v : α} (hx : Reach ends x s v) :
    ¬ Reach ends y s v → ∃ e, x e = true ∧ y e = false := by
  induction hx with
  | refl => intro hy; exact absurd (Reach.refl _) hy
  | step e h hxe hb ih =>
    intro hy
    by_cases hyb : Reach ends y s (ends e).1
    · refine ⟨e, hxe, ?_⟩
      by_contra hye
      have hye' : y e = true := by
        cases hh : y e with | false => exact absurd hh hye | true => rfl
      exact hy (Reach.step e hyb hye' rfl)
    · exact ih (hb ▸ hyb)

/-- **The monotone KW game for `st`-connectivity is solvable (proved)**: a connected `x` and a
disconnected `y` always admit a distinguishing edge (present in `x`, absent in `y`) — via an `s`-`t`
cut.  This certifies the game is well-posed and is the seed of the Fork-game lower bound. -/
theorem stconn_mkw_solvable (ends : ε → α × α) (s t : α) {x y : ε → Bool}
    (hx : stconn ends s t x = true) (hy : stconn ends s t y = false) :
    ∃ e, x e = true ∧ y e = false :=
  reach_cut_crossing ends s ((stconn_true_iff ends s t x).mp hx)
    ((stconn_false_iff ends s t y).mp hy)

end PallLean.Paper93.DeepMath.PathB.STConnectivity

#print axioms PallLean.Paper93.DeepMath.PathB.STConnectivity.stconn_mono
#print axioms PallLean.Paper93.DeepMath.PathB.STConnectivity.reach_cut_crossing
#print axioms PallLean.Paper93.DeepMath.PathB.STConnectivity.stconn_mkw_solvable
