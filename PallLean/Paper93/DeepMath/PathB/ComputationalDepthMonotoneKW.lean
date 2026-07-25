import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW11

/-!
# Monotone Karchmer–Wigderson: the framework (Phase 1–2 of the monotone-lifting scope)

The stress-test showed the *general*-depth base socket is circular.  The one place a non-circular
super-log depth lower bound genuinely exists is the **monotone** world (query-to-communication
lifting is unconditional there).  This brick lays the tractable foundation of that programme —
monotone formulas, monotone depth, and the monotone KW game — reusing the repo's `HasProtocol`
machinery with two changes: negation-free formulas and the monotone leaf relation
`x i = 1 ∧ y i = 0` (instead of `x i ≠ y i`).

* **`MTree`** — monotone DeMorgan formulas (`var / and / or`, no negation); `eval`, `dep`;
* **`MTree.eval_mono` (proved)** — monotone formulas compute monotone functions;
* **`mdepth`** — minimal monotone-formula depth;
* **`HasMProtocol`** — a depth-`d` monotone KW protocol (leaf = a coordinate `i` with `x i = 1`,
  `y i = 0` for all pairs); **`HasMProtocol.mono`**;
* **`mformula_gives_mprotocol` (proved)** — a monotone formula gives a monotone KW protocol of its
  depth (`∧` ⇒ Bob splits on the left value, `∨` ⇒ Alice splits) — the EASY direction of the
  monotone KW theorem;
* **`mkwCC`** and **`mkwCC_le_of_mformula` (proved)** — `CC(mKW_f) ≤` any monotone formula depth.

**Scope note.**  This is the non-circular foundation.  What remains (see the scope block below) is
the converse (protocol ⇒ monotone formula), monotone universality, and — the research core — a
**deterministic** communication lower bound for an *explicit* monotone KW game (`st`-connectivity's
`Ω(log²n)` via the Fork game, or Raz–McKenzie lifting).  Nothing here is a lower bound yet; it is the
machine on which one would be proved.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MonotoneKW

open PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-- Monotone DeMorgan formulas: variables, `∧`, `∨` — no negation. -/
inductive MTree (n : ℕ) : Type
  | var : Fin n → MTree n
  | and : MTree n → MTree n → MTree n
  | or : MTree n → MTree n → MTree n

variable {n : ℕ}

/-- Evaluation of a monotone formula. -/
def MTree.eval : MTree n → (Fin n → Bool) → Bool
  | .var i, x => x i
  | .and l r, x => l.eval x && r.eval x
  | .or l r, x => l.eval x || r.eval x

/-- Depth of a monotone formula. -/
def MTree.dep : MTree n → ℕ
  | .var _ => 0
  | .and l r => 1 + max l.dep r.dep
  | .or l r => 1 + max l.dep r.dep

/-- **Monotone formulas compute monotone functions (proved).** -/
theorem MTree.eval_mono (t : MTree n) {x y : Fin n → Bool} (h : ∀ i, x i ≤ y i) :
    t.eval x ≤ t.eval y := by
  induction t with
  | var i => exact h i
  | and l r ihl ihr =>
    simp only [MTree.eval]; revert ihl ihr
    cases l.eval x <;> cases l.eval y <;> cases r.eval x <;> cases r.eval y <;> decide
  | or l r ihl ihr =>
    simp only [MTree.eval]; revert ihl ihr
    cases l.eval x <;> cases l.eval y <;> cases r.eval x <;> cases r.eval y <;> decide

/-- Minimal monotone-formula depth of a function. -/
noncomputable def mdepth (f : (Fin n → Bool) → Bool) : ℕ :=
  sInf {d | ∃ t : MTree n, (∀ x, t.eval x = f x) ∧ t.dep = d}

/-- A depth-`d` **monotone** KW protocol solving `A × B`: a leaf names a coordinate `i` that is `1`
throughout `A` and `0` throughout `B`. -/
inductive HasMProtocol : Finset (Fin n → Bool) → Finset (Fin n → Bool) → ℕ → Prop
  | leaf {A B : Finset (Fin n → Bool)} (d : ℕ) (i : Fin n)
      (h : ∀ x ∈ A, ∀ y ∈ B, x i = true ∧ y i = false) : HasMProtocol A B d
  | bob {A B : Finset (Fin n → Bool)} {d : ℕ} (p : (Fin n → Bool) → Bool)
      (h0 : HasMProtocol A (B.filter (fun y => p y = false)) d)
      (h1 : HasMProtocol A (B.filter (fun y => p y = true)) d) :
      HasMProtocol A B (d + 1)
  | alice {A B : Finset (Fin n → Bool)} {d : ℕ} (p : (Fin n → Bool) → Bool)
      (h0 : HasMProtocol (A.filter (fun x => p x = false)) B d)
      (h1 : HasMProtocol (A.filter (fun x => p x = true)) B d) :
      HasMProtocol A B (d + 1)

/-- Monotone protocol cost is upward closed. -/
theorem HasMProtocol.mono {A B : Finset (Fin n → Bool)} {d d' : ℕ}
    (h : HasMProtocol A B d) (hd : d ≤ d') : HasMProtocol A B d' := by
  induction h generalizing d' with
  | leaf d i hi => exact HasMProtocol.leaf d' i hi
  | bob p h0 h1 ih0 ih1 =>
    obtain ⟨e, rfl⟩ : ∃ e, d' = e + 1 := ⟨d' - 1, by omega⟩
    exact HasMProtocol.bob p (ih0 (by omega)) (ih1 (by omega))
  | alice p h0 h1 ih0 ih1 =>
    obtain ⟨e, rfl⟩ : ∃ e, d' = e + 1 := ⟨d' - 1, by omega⟩
    exact HasMProtocol.alice p (ih0 (by omega)) (ih1 (by omega))

/-- **The monotone KW easy direction (proved)**: a monotone formula gives a monotone KW protocol of
its depth. -/
theorem mformula_gives_mprotocol (t : MTree n) :
    ∀ (A B : Finset (Fin n → Bool)),
      (∀ x ∈ A, t.eval x = true) → (∀ y ∈ B, t.eval y = false) →
      HasMProtocol A B t.dep := by
  induction t with
  | var i =>
    intro A B hA hB
    apply HasMProtocol.leaf 0 i
    intro x hx y hy
    exact ⟨hA x hx, hB y hy⟩
  | and l r ihl ihr =>
    intro A B hA hB
    have hAl : ∀ x ∈ A, l.eval x = true := by
      intro x hx; have hx' := hA x hx; simp only [MTree.eval] at hx'
      revert hx'; cases l.eval x <;> cases r.eval x <;> decide
    have hAr : ∀ x ∈ A, r.eval x = true := by
      intro x hx; have hx' := hA x hx; simp only [MTree.eval] at hx'
      revert hx'; cases l.eval x <;> cases r.eval x <;> decide
    have h0 : HasMProtocol A (B.filter (fun y => l.eval y = false)) l.dep :=
      ihl A _ hAl (fun y hy => (Finset.mem_filter.mp hy).2)
    have h1 : HasMProtocol A (B.filter (fun y => l.eval y = true)) r.dep := by
      apply ihr A _ hAr
      intro y hy
      have hyB := (Finset.mem_filter.mp hy).1
      have hyl := (Finset.mem_filter.mp hy).2
      have hy' := hB y hyB; simp only [MTree.eval] at hy'
      rw [hyl] at hy'; simpa using hy'
    have h0' := h0.mono (le_max_left l.dep r.dep)
    have h1' := h1.mono (le_max_right l.dep r.dep)
    show HasMProtocol A B (1 + max l.dep r.dep)
    rw [Nat.add_comm]
    exact HasMProtocol.bob (fun y => l.eval y) h0' h1'
  | or l r ihl ihr =>
    intro A B hA hB
    have hBl : ∀ y ∈ B, l.eval y = false := by
      intro y hy; have hy' := hB y hy; simp only [MTree.eval] at hy'
      revert hy'; cases l.eval y <;> cases r.eval y <;> decide
    have hBr : ∀ y ∈ B, r.eval y = false := by
      intro y hy; have hy' := hB y hy; simp only [MTree.eval] at hy'
      revert hy'; cases l.eval y <;> cases r.eval y <;> decide
    have h1 : HasMProtocol (A.filter (fun x => l.eval x = true)) B l.dep :=
      ihl _ B (fun x hx => (Finset.mem_filter.mp hx).2) hBl
    have h0 : HasMProtocol (A.filter (fun x => l.eval x = false)) B r.dep := by
      apply ihr _ B
      · intro x hx
        have hxA := (Finset.mem_filter.mp hx).1
        have hxl := (Finset.mem_filter.mp hx).2
        have hx' := hA x hxA; simp only [MTree.eval] at hx'
        rw [hxl] at hx'; simpa using hx'
      · exact hBr
    have h0' := h0.mono (le_max_right l.dep r.dep)
    have h1' := h1.mono (le_max_left l.dep r.dep)
    show HasMProtocol A B (1 + max l.dep r.dep)
    rw [Nat.add_comm]
    exact HasMProtocol.alice (fun x => l.eval x) h0' h1'

/-- Monotone KW communication complexity: the least monotone-protocol depth. -/
noncomputable def mkwCC (f : (Fin n → Bool) → Bool) : ℕ :=
  sInf {d | HasMProtocol (onesOf f) (zerosOf f) d}

/-- **`CC(mKW_f) ≤ (monotone formula depth)` (proved)** — the monotone KW upper bound, per formula. -/
theorem mkwCC_le_of_mformula (f : (Fin n → Bool) → Bool) (t : MTree n)
    (ht : ∀ x, t.eval x = f x) : mkwCC f ≤ t.dep := by
  have hp : HasMProtocol (onesOf f) (zerosOf f) t.dep :=
    mformula_gives_mprotocol t (onesOf f) (zerosOf f)
      (fun x hx => by rw [ht]; exact (Finset.mem_filter.mp hx).2)
      (fun y hy => by rw [ht]; exact (Finset.mem_filter.mp hy).2)
  exact Nat.sInf_le hp

end PallLean.Paper93.DeepMath.PathB.MonotoneKW

#print axioms PallLean.Paper93.DeepMath.PathB.MonotoneKW.MTree.eval_mono
#print axioms PallLean.Paper93.DeepMath.PathB.MonotoneKW.mformula_gives_mprotocol
#print axioms PallLean.Paper93.DeepMath.PathB.MonotoneKW.mkwCC_le_of_mformula
