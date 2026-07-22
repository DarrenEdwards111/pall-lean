import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW10

/-!
# KRW brick 11: the Karchmer–Wigderson connection (formula ⟹ protocol)

The tool the KRW program actually runs on: DeMorgan formula depth is the
communication complexity of the Karchmer–Wigderson game.  For `f`, Alice holds
`x` with `f x = 1`, Bob holds `y` with `f y = 0`, and they must agree on a
coordinate `i` with `x i ≠ y i`.  This brick proves the EASY direction —
`CC(KW_f) ≤ dmdepth f` — by turning a formula into a protocol.

* **`HasProtocol A B d`** — a depth-`d` KW protocol solving the rectangle `A×B`
  (leaf = a coordinate distinguishing all pairs; `bob`/`alice` = one party splits
  their side); **`HasProtocol.mono`** — cost is upward closed;
* **`formula_gives_protocol` (proved)** — a DeMorgan tree `t` with `t = 1` on `A`,
  `t = 0` on `B` gives a protocol of cost `t.dep` (recursion: `∧` ⇒ Bob splits on
  the left subformula's value, `∨` ⇒ Alice splits);
* **`kwCC`** and **`kwCC_le_dmdepth` (proved)** — `CC(KW_f) ≤ dmdepth f`.

This is a genuine, foundational result (not the conjecture): the KW machinery for
attacking depth lower bounds.  The converse `dmdepth f ≤ CC(KW_f)` is a separate
brick.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-- The `1`-set of `f`. -/
def onesOf {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun x => f x = true)

/-- The `0`-set of `f`. -/
def zerosOf {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun x => f x = false)

/-- A depth-`d` Karchmer–Wigderson protocol solving the rectangle `A×B`. -/
inductive HasProtocol {n : ℕ} : Finset (Fin n → Bool) → Finset (Fin n → Bool) → ℕ → Prop
  | leaf {A B : Finset (Fin n → Bool)} (d : ℕ) (i : Fin n)
      (h : ∀ x ∈ A, ∀ y ∈ B, x i ≠ y i) : HasProtocol A B d
  | bob {A B : Finset (Fin n → Bool)} {d : ℕ} (p : (Fin n → Bool) → Bool)
      (h0 : HasProtocol A (B.filter (fun y => p y = false)) d)
      (h1 : HasProtocol A (B.filter (fun y => p y = true)) d) :
      HasProtocol A B (d + 1)
  | alice {A B : Finset (Fin n → Bool)} {d : ℕ} (p : (Fin n → Bool) → Bool)
      (h0 : HasProtocol (A.filter (fun x => p x = false)) B d)
      (h1 : HasProtocol (A.filter (fun x => p x = true)) B d) :
      HasProtocol A B (d + 1)

/-- Protocol cost is upward closed. -/
theorem HasProtocol.mono {n : ℕ} {A B : Finset (Fin n → Bool)} {d d' : ℕ}
    (h : HasProtocol A B d) (hd : d ≤ d') : HasProtocol A B d' := by
  induction h generalizing d' with
  | leaf d i hi => exact HasProtocol.leaf d' i hi
  | bob p h0 h1 ih0 ih1 =>
    obtain ⟨e, rfl⟩ : ∃ e, d' = e + 1 := ⟨d' - 1, by omega⟩
    exact HasProtocol.bob p (ih0 (by omega)) (ih1 (by omega))
  | alice p h0 h1 ih0 ih1 =>
    obtain ⟨e, rfl⟩ : ∃ e, d' = e + 1 := ⟨d' - 1, by omega⟩
    exact HasProtocol.alice p (ih0 (by omega)) (ih1 (by omega))

/-- **The Karchmer–Wigderson easy direction (proved)**: a DeMorgan formula gives a
KW protocol of the same depth. -/
theorem formula_gives_protocol {n : ℕ} (t : DMTree n) :
    ∀ (A B : Finset (Fin n → Bool)),
      (∀ x ∈ A, t.eval x = true) → (∀ y ∈ B, t.eval y = false) →
      HasProtocol A B t.dep := by
  induction t with
  | lit i b =>
    intro A B hA hB
    apply HasProtocol.leaf 0 i
    intro x hx y hy
    have h1 : (x i == b) = true := hA x hx
    have h2 : (y i == b) = false := hB y hy
    intro hxy
    rw [hxy] at h1
    rw [h1] at h2
    exact Bool.noConfusion h2
  | and l r ihl ihr =>
    intro A B hA hB
    have hAl : ∀ x ∈ A, l.eval x = true := by
      intro x hx; have hx' := hA x hx; simp only [DMTree.eval] at hx'
      revert hx'; cases l.eval x <;> cases r.eval x <;> decide
    have hAr : ∀ x ∈ A, r.eval x = true := by
      intro x hx; have hx' := hA x hx; simp only [DMTree.eval] at hx'
      revert hx'; cases l.eval x <;> cases r.eval x <;> decide
    have h0 : HasProtocol A (B.filter (fun y => l.eval y = false)) l.dep := by
      apply ihl
      · exact hAl
      · intro y hy; exact (Finset.mem_filter.mp hy).2
    have h1 : HasProtocol A (B.filter (fun y => l.eval y = true)) r.dep := by
      apply ihr
      · exact hAr
      · intro y hy
        have hyB := (Finset.mem_filter.mp hy).1
        have hyl := (Finset.mem_filter.mp hy).2
        have hy' := hB y hyB; simp only [DMTree.eval] at hy'
        rw [hyl] at hy'; simpa using hy'
    have h0' := h0.mono (le_max_left l.dep r.dep)
    have h1' := h1.mono (le_max_right l.dep r.dep)
    show HasProtocol A B (1 + max l.dep r.dep)
    rw [Nat.add_comm]
    exact HasProtocol.bob (fun y => l.eval y) h0' h1'
  | or l r ihl ihr =>
    intro A B hA hB
    have hBl : ∀ y ∈ B, l.eval y = false := by
      intro y hy; have hy' := hB y hy; simp only [DMTree.eval] at hy'
      revert hy'; cases l.eval y <;> cases r.eval y <;> decide
    have hBr : ∀ y ∈ B, r.eval y = false := by
      intro y hy; have hy' := hB y hy; simp only [DMTree.eval] at hy'
      revert hy'; cases l.eval y <;> cases r.eval y <;> decide
    have h1 : HasProtocol (A.filter (fun x => l.eval x = true)) B l.dep := by
      apply ihl
      · intro x hx; exact (Finset.mem_filter.mp hx).2
      · exact hBl
    have h0 : HasProtocol (A.filter (fun x => l.eval x = false)) B r.dep := by
      apply ihr
      · intro x hx
        have hxA := (Finset.mem_filter.mp hx).1
        have hxl := (Finset.mem_filter.mp hx).2
        have hx' := hA x hxA; simp only [DMTree.eval] at hx'
        rw [hxl] at hx'; simpa using hx'
      · exact hBr
    have h0' := h0.mono (le_max_right l.dep r.dep)
    have h1' := h1.mono (le_max_left l.dep r.dep)
    show HasProtocol A B (1 + max l.dep r.dep)
    rw [Nat.add_comm]
    exact HasProtocol.alice (fun x => l.eval x) h0' h1'

/-- A formula for `f` gives a KW protocol on `(onesOf f, zerosOf f)` of its depth. -/
theorem kw_protocol_of_dmtree {n : ℕ} (f : (Fin n → Bool) → Bool) (t : DMTree n)
    (ht : ∀ x, t.eval x = f x) : HasProtocol (onesOf f) (zerosOf f) t.dep := by
  apply formula_gives_protocol
  · intro x hx; rw [ht]; exact (Finset.mem_filter.mp hx).2
  · intro y hy; rw [ht]; exact (Finset.mem_filter.mp hy).2

/-- Karchmer–Wigderson communication complexity: the least protocol depth. -/
noncomputable def kwCC {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  sInf {d | HasProtocol (onesOf f) (zerosOf f) d}

/-- **`CC(KW_f) ≤ dmdepth f` (proved)** — the Karchmer–Wigderson upper bound. -/
theorem kwCC_le_dmdepth {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool) :
    kwCC f ≤ dmdepth f := by
  obtain ⟨t, hte, htd⟩ := Nat.sInf_mem (dmdepth_set_nonempty hn f)
  have hp : HasProtocol (onesOf f) (zerosOf f) t.dep := kw_protocol_of_dmtree f t hte
  rw [htd] at hp
  exact Nat.sInf_le hp

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.formula_gives_protocol
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.kwCC_le_dmdepth
