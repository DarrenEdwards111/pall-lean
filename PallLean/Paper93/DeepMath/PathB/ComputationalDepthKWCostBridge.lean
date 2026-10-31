import PallLean.Paper93.DeepMath.PathB.ComputationalDepthProtocolModel5
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW12

/-!
# Wiring the concrete protocol cost to the KW / formula-depth theorem

The `CommProtocol` model (`Protocol`, `run`, `cost`) is a concrete transcript tree;
the KW arc (KRW11-12) uses an abstract depth predicate `HasProtocol A B d` and
`kwCC f = sInf {d | HasProtocol (onesOf f) (zerosOf f) d}`, with
`kw_theorem : kwCC f ≤ dmdepth f ≤ kwCC f + 1`.

This file wires the two together.  A concrete protocol `KWComputes` the KW game of
`f` when its output coordinate always separates Alice's `1`-input from Bob's
`0`-input.  Then:

* **`kwComputes_of_hasProtocol` (proved)** — an abstract depth-`d` protocol yields a
  concrete one with `cost ≤ d`;
* **`hasProtocol_of_kwComputes` (proved)** — a concrete KW protocol yields an
  abstract one at depth `cost P`;
* **`kwCC_le_cost` (proved)** — hence `kwCC f ≤ cost P` for every KW protocol, so
  `kwCC f` is the minimum concrete cost;
* **`dmdepth_le_cost_succ` (proved)** — a concrete KW protocol of cost `c` gives a
  DeMorgan formula of depth `≤ c+1`;
* **`exists_kwProtocol_cost_le_dmdepth` (proved)** — conversely a depth-`D` formula
  gives a concrete KW protocol of cost `≤ D`.

So the concrete `cost` measure is exactly KW communication, which is DeMorgan
formula depth up to `+1`.  This is the KW correspondence — ceiling `P ≠ NC¹`, not
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

open PallLean.Paper93.DeepMath.PathB.CommProtocol

variable {n : ℕ}

/-- A concrete protocol solves the KW game on `A × B`: its output coordinate always
separates Alice's input from Bob's. -/
def KWComputes (A B : Finset (Fin n → Bool))
    (P : Protocol (Fin n → Bool) (Fin n → Bool) (Fin n)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, x (run P x y) ≠ y (run P x y)

/-- **Abstract → concrete (proved)**: a depth-`d` KW protocol is realised by a
concrete protocol of `cost ≤ d`. -/
theorem kwComputes_of_hasProtocol {A B : Finset (Fin n → Bool)} {d : ℕ}
    (h : HasProtocol A B d) :
    ∃ P : Protocol (Fin n → Bool) (Fin n → Bool) (Fin n), KWComputes A B P ∧ cost P ≤ d := by
  induction h with
  | leaf d i hsep =>
    refine ⟨Protocol.leaf i, ?_, ?_⟩
    · intro x hx y hy
      simpa only [run] using hsep x hx y hy
    · simp only [cost]; exact Nat.zero_le _
  | bob p h0 h1 ih0 ih1 =>
    obtain ⟨P0, hP0, hc0⟩ := ih0
    obtain ⟨P1, hP1, hc1⟩ := ih1
    refine ⟨Protocol.bob p P0 P1, ?_, ?_⟩
    · intro x hx y hy
      cases hpy : p y with
      | false =>
        simpa only [run, hpy, cond_false] using hP0 x hx y (Finset.mem_filter.mpr ⟨hy, hpy⟩)
      | true =>
        simpa only [run, hpy, cond_true] using hP1 x hx y (Finset.mem_filter.mpr ⟨hy, hpy⟩)
    · simp only [cost]; omega
  | alice p h0 h1 ih0 ih1 =>
    obtain ⟨P0, hP0, hc0⟩ := ih0
    obtain ⟨P1, hP1, hc1⟩ := ih1
    refine ⟨Protocol.alice p P0 P1, ?_, ?_⟩
    · intro x hx y hy
      cases hpx : p x with
      | false =>
        simpa only [run, hpx, cond_false] using hP0 x (Finset.mem_filter.mpr ⟨hx, hpx⟩) y hy
      | true =>
        simpa only [run, hpx, cond_true] using hP1 x (Finset.mem_filter.mpr ⟨hx, hpx⟩) y hy
    · simp only [cost]; omega

/-- **Concrete → abstract (proved)**: a concrete KW protocol gives an abstract one at
depth `cost P`. -/
theorem hasProtocol_of_kwComputes
    (P : Protocol (Fin n → Bool) (Fin n → Bool) (Fin n)) :
    ∀ (A B : Finset (Fin n → Bool)), KWComputes A B P → HasProtocol A B (cost P) := by
  induction P with
  | leaf i =>
    intro A B hkw
    refine HasProtocol.leaf 0 i (fun x hx y hy => ?_)
    simpa only [run] using hkw x hx y hy
  | alice f l r ihl ihr =>
    intro A B hkw
    have hl : HasProtocol (A.filter (fun x => f x = false)) B (cost l) := by
      apply ihl
      intro x hx y hy
      rw [Finset.mem_filter] at hx
      obtain ⟨hxA, hxf⟩ := hx
      simpa only [run, hxf, cond_false] using hkw x hxA y hy
    have hr : HasProtocol (A.filter (fun x => f x = true)) B (cost r) := by
      apply ihr
      intro x hx y hy
      rw [Finset.mem_filter] at hx
      obtain ⟨hxA, hxf⟩ := hx
      simpa only [run, hxf, cond_true] using hkw x hxA y hy
    have hl' := hl.mono (Nat.le_max_left (cost l) (cost r))
    have hr' := hr.mono (Nat.le_max_right (cost l) (cost r))
    have hmain : HasProtocol A B (max (cost l) (cost r) + 1) := HasProtocol.alice f hl' hr'
    simp only [cost]; rw [Nat.add_comm]; exact hmain
  | bob g l r ihl ihr =>
    intro A B hkw
    have hl : HasProtocol A (B.filter (fun y => g y = false)) (cost l) := by
      apply ihl
      intro x hx y hy
      rw [Finset.mem_filter] at hy
      obtain ⟨hyB, hyg⟩ := hy
      simpa only [run, hyg, cond_false] using hkw x hx y hyB
    have hr : HasProtocol A (B.filter (fun y => g y = true)) (cost r) := by
      apply ihr
      intro x hx y hy
      rw [Finset.mem_filter] at hy
      obtain ⟨hyB, hyg⟩ := hy
      simpa only [run, hyg, cond_true] using hkw x hx y hyB
    have hl' := hl.mono (Nat.le_max_left (cost l) (cost r))
    have hr' := hr.mono (Nat.le_max_right (cost l) (cost r))
    have hmain : HasProtocol A B (max (cost l) (cost r) + 1) := HasProtocol.bob g hl' hr'
    simp only [cost]; rw [Nat.add_comm]; exact hmain

/-- **`kwCC f` is the minimum concrete cost (proved)**: `kwCC f ≤ cost P` for every
KW protocol `P`. -/
theorem kwCC_le_cost (f : (Fin n → Bool) → Bool)
    {P : Protocol (Fin n → Bool) (Fin n → Bool) (Fin n)}
    (h : KWComputes (onesOf f) (zerosOf f) P) : kwCC f ≤ cost P :=
  Nat.sInf_le (hasProtocol_of_kwComputes P (onesOf f) (zerosOf f) h)

/-- **Concrete cost bounds formula depth (proved)**: a KW protocol of cost `c` gives a
DeMorgan formula of depth `≤ c+1`. -/
theorem dmdepth_le_cost_succ (hn : 0 < n) (f : (Fin n → Bool) → Bool)
    {P : Protocol (Fin n → Bool) (Fin n → Bool) (Fin n)}
    (h : KWComputes (onesOf f) (zerosOf f) P) : dmdepth f ≤ cost P + 1 := by
  have h1 := dmdepth_le_kwCC_succ hn f
  have h2 := kwCC_le_cost f h
  omega

/-- **Formula depth bounds concrete cost (proved)**: a depth-`D` formula for `f` gives a
concrete KW protocol of cost `≤ D`. -/
theorem exists_kwProtocol_cost_le_dmdepth (hn : 0 < n) (f : (Fin n → Bool) → Bool) :
    ∃ P : Protocol (Fin n → Bool) (Fin n → Bool) (Fin n),
      KWComputes (onesOf f) (zerosOf f) P ∧ cost P ≤ dmdepth f := by
  have hne : {d | HasProtocol (onesOf f) (zerosOf f) d}.Nonempty := by
    obtain ⟨t, ht⟩ := exists_dmtree hn f
    exact ⟨t.dep, kw_protocol_of_dmtree f t ht⟩
  obtain ⟨P, hP, hc⟩ := kwComputes_of_hasProtocol (Nat.sInf_mem hne)
  exact ⟨P, hP, le_trans hc (kwCC_le_dmdepth hn f)⟩

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.kwCC_le_cost
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.dmdepth_le_cost_succ
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.exists_kwProtocol_cost_le_dmdepth
