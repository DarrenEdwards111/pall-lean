import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW11

/-!
# The monotone Karchmer–Wigderson theorem (Phase 1–2 of the monotone-lifting scope)

The one non-circular route to a super-log depth lower bound lives in the **monotone** world.  This
file builds its foundation — monotone formulas, monotone depth, the monotone KW game — and proves the
full **monotone Karchmer–Wigderson theorem** `mkwCC f = mdepth f` (given any monotone formula for
`f`).  It reuses the repo's `HasProtocol` template with two changes: negation-free formulas and the
monotone leaf relation `x i = 1 ∧ y i = 0` (instead of `x i ≠ y i`).

* **`MTree`** — monotone DeMorgan formulas (`var / cst / and / or`, no negation).  Constants are
  needed for the converse's empty sub-rectangles (any negation-free `var/and/or` formula is `false`
  at all-zeros, so cannot be constant `true`); constants are themselves monotone.
* **`MTree.eval_mono`** — monotone formulas compute monotone functions;
* **`mdepth`** — minimal monotone-formula depth;
* **`HasMProtocol`** — monotone KW protocol (leaf = a coordinate `i` with `x i = 1`, `y i = 0`);
* **`mformula_gives_mprotocol`** — formula ⇒ protocol (easy direction);
* **`mprotocol_gives_mformula`** — protocol ⇒ formula (converse; Bob ⇒ `∧`, Alice ⇒ `∨`, leaf ⇒
  `var i`, empty side ⇒ `cst`);
* **`mkw_theorem` (proved)** — `mkwCC f = mdepth f`.  Exact equality (no `+1`: `cst` has depth `0`).

**Scope.**  This completes Phase 2 (the monotone KW theorem) unconditionally.  Phase 3 — the
research core — is a *deterministic* super-log communication lower bound for an explicit monotone KW
game (`st`-connectivity `Ω(log²n)` via the Fork game, or Raz–McKenzie lifting).  Nothing here is a
lower bound yet; it is the exact interface one consumes.  Nothing here is `P ≠ NP`; the programme's
ceiling is monotone-`P` ⊄ monotone-`NC¹`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MonotoneKW

open PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-- Monotone DeMorgan formulas: variables, constants, `∧`, `∨` — no negation. -/
inductive MTree (n : ℕ) : Type
  | var : Fin n → MTree n
  | cst : Bool → MTree n
  | and : MTree n → MTree n → MTree n
  | or : MTree n → MTree n → MTree n

variable {n : ℕ}

/-- Evaluation of a monotone formula. -/
def MTree.eval : MTree n → (Fin n → Bool) → Bool
  | .var i, x => x i
  | .cst b, _ => b
  | .and l r, x => l.eval x && r.eval x
  | .or l r, x => l.eval x || r.eval x

/-- Depth of a monotone formula (constants and variables are depth `0`). -/
def MTree.dep : MTree n → ℕ
  | .var _ => 0
  | .cst _ => 0
  | .and l r => 1 + max l.dep r.dep
  | .or l r => 1 + max l.dep r.dep

/-- **Monotone formulas compute monotone functions (proved).** -/
theorem MTree.eval_mono (t : MTree n) {x y : Fin n → Bool} (h : ∀ i, x i ≤ y i) :
    t.eval x ≤ t.eval y := by
  induction t with
  | var i => exact h i
  | cst b => exact le_refl b
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
its depth.  (`0 < n` only to name a coordinate in the vacuous constant leaf.) -/
theorem mformula_gives_mprotocol (hn : 0 < n) (t : MTree n) :
    ∀ (A B : Finset (Fin n → Bool)),
      (∀ x ∈ A, t.eval x = true) → (∀ y ∈ B, t.eval y = false) →
      HasMProtocol A B t.dep := by
  induction t with
  | var i =>
    intro A B hA hB
    exact HasMProtocol.leaf 0 i (fun x hx y hy => ⟨hA x hx, hB y hy⟩)
  | cst b =>
    intro A B hA hB
    refine HasMProtocol.leaf 0 ⟨0, hn⟩ (fun x hx y hy => ?_)
    have h1 := hA x hx; have h2 := hB y hy; simp only [MTree.eval] at h1 h2
    exact absurd (h1.symm.trans h2) (by decide)
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

/-- **The monotone KW converse (proved)**: a monotone KW protocol of depth `d` gives a monotone
formula of depth `≤ d` that is `1` on `A` and `0` on `B` (Bob ⇒ `∧`, Alice ⇒ `∨`, leaf ⇒ `var i`,
empty side ⇒ a constant). -/
theorem mprotocol_gives_mformula {A B : Finset (Fin n → Bool)} {d : ℕ}
    (h : HasMProtocol A B d) :
    ∃ t : MTree n, t.dep ≤ d
      ∧ (∀ x ∈ A, t.eval x = true) ∧ (∀ y ∈ B, t.eval y = false) := by
  induction h with
  | leaf d i hi =>
    rename_i A B
    by_cases hA : A.Nonempty
    · by_cases hB : B.Nonempty
      · obtain ⟨y₀, hy₀⟩ := hB
        obtain ⟨x₀, hx₀⟩ := hA
        refine ⟨MTree.var i, by simp [MTree.dep], ?_, ?_⟩
        · intro x hx; exact (hi x hx y₀ hy₀).1
        · intro y hy; exact (hi x₀ hx₀ y hy).2
      · refine ⟨MTree.cst true, by simp [MTree.dep], ?_, ?_⟩
        · intro x _; rfl
        · intro y hy; exact absurd ⟨y, hy⟩ hB
    · refine ⟨MTree.cst false, by simp [MTree.dep], ?_, ?_⟩
      · intro x hx; exact absurd ⟨x, hx⟩ hA
      · intro y _; rfl
  | bob p h0 h1 ih0 ih1 =>
    obtain ⟨t0, hd0, ha0, hb0⟩ := ih0
    obtain ⟨t1, hd1, ha1, hb1⟩ := ih1
    refine ⟨MTree.and t0 t1, by simp only [MTree.dep]; omega, ?_, ?_⟩
    · intro x hx; simp [MTree.eval, ha0 x hx, ha1 x hx]
    · intro y hy
      by_cases hpy : p y = false
      · simp [MTree.eval, hb0 y (Finset.mem_filter.mpr ⟨hy, hpy⟩)]
      · have hpy' : p y = true := by
          cases hh : p y with | false => exact absurd hh hpy | true => rfl
        simp [MTree.eval, hb1 y (Finset.mem_filter.mpr ⟨hy, hpy'⟩)]
  | alice p h0 h1 ih0 ih1 =>
    obtain ⟨t0, hd0, ha0, hb0⟩ := ih0
    obtain ⟨t1, hd1, ha1, hb1⟩ := ih1
    refine ⟨MTree.or t0 t1, by simp only [MTree.dep]; omega, ?_, ?_⟩
    · intro x hx
      by_cases hpx : p x = false
      · simp [MTree.eval, ha0 x (Finset.mem_filter.mpr ⟨hx, hpx⟩)]
      · have hpx' : p x = true := by
          cases hh : p x with | false => exact absurd hh hpx | true => rfl
        simp [MTree.eval, ha1 x (Finset.mem_filter.mpr ⟨hx, hpx'⟩)]
    · intro y hy; simp [MTree.eval, hb0 y hy, hb1 y hy]

/-- Monotone KW communication complexity: the least monotone-protocol depth. -/
noncomputable def mkwCC (f : (Fin n → Bool) → Bool) : ℕ :=
  sInf {d | HasMProtocol (onesOf f) (zerosOf f) d}

/-- **`CC(mKW_f) ≤ (monotone formula depth)` (proved)** — per formula. -/
theorem mkwCC_le_of_mformula (hn : 0 < n) (f : (Fin n → Bool) → Bool) (t : MTree n)
    (ht : ∀ x, t.eval x = f x) : mkwCC f ≤ t.dep := by
  have hp : HasMProtocol (onesOf f) (zerosOf f) t.dep :=
    mformula_gives_mprotocol hn t (onesOf f) (zerosOf f)
      (fun x hx => by rw [ht]; exact (Finset.mem_filter.mp hx).2)
      (fun y hy => by rw [ht]; exact (Finset.mem_filter.mp hy).2)
  exact Nat.sInf_le hp

/-- **`mkwCC f ≤ mdepth f` (proved)** — given any monotone formula for `f`. -/
theorem mkwCC_le_mdepth (hn : 0 < n) (f : (Fin n → Bool) → Bool) (t : MTree n)
    (ht : ∀ x, t.eval x = f x) : mkwCC f ≤ mdepth f := by
  have hne : {d | ∃ t' : MTree n, (∀ x, t'.eval x = f x) ∧ t'.dep = d}.Nonempty :=
    ⟨t.dep, t, ht, rfl⟩
  obtain ⟨t', ht', hdep'⟩ := Nat.sInf_mem hne
  calc mkwCC f ≤ t'.dep := mkwCC_le_of_mformula hn f t' ht'
    _ = mdepth f := hdep'

/-- **`mdepth f ≤ mkwCC f` (proved)** — given any monotone formula for `f`. -/
theorem mdepth_le_mkwCC (hn : 0 < n) (f : (Fin n → Bool) → Bool) (t : MTree n)
    (ht : ∀ x, t.eval x = f x) : mdepth f ≤ mkwCC f := by
  have hne : {d | HasMProtocol (onesOf f) (zerosOf f) d}.Nonempty := by
    refine ⟨t.dep, mformula_gives_mprotocol hn t (onesOf f) (zerosOf f) ?_ ?_⟩
    · intro x hx; rw [ht]; exact (Finset.mem_filter.mp hx).2
    · intro y hy; rw [ht]; exact (Finset.mem_filter.mp hy).2
  obtain ⟨s, hd, ha, hb⟩ := mprotocol_gives_mformula (Nat.sInf_mem hne)
  have hcomp : ∀ x, s.eval x = f x := by
    intro x
    cases hfx : f x
    · exact hb x (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hfx⟩)
    · exact ha x (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hfx⟩)
  calc mdepth f ≤ s.dep := Nat.sInf_le ⟨s, hcomp, rfl⟩
    _ ≤ mkwCC f := hd

/-- **THE MONOTONE KARCHMER–WIGDERSON THEOREM (proved)**: `mkwCC f = mdepth f`, given any monotone
formula for `f`.  Exact equality — no `+1`, since `MTree` has depth-`0` constants. -/
theorem mkw_theorem (hn : 0 < n) (f : (Fin n → Bool) → Bool) (t : MTree n)
    (ht : ∀ x, t.eval x = f x) : mkwCC f = mdepth f :=
  le_antisymm (mkwCC_le_mdepth hn f t ht) (mdepth_le_mkwCC hn f t ht)

end PallLean.Paper93.DeepMath.PathB.MonotoneKW

#print axioms PallLean.Paper93.DeepMath.PathB.MonotoneKW.mprotocol_gives_mformula
#print axioms PallLean.Paper93.DeepMath.PathB.MonotoneKW.mkw_theorem
