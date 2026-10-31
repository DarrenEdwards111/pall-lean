import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW11

/-!
# KRW brick 12: the Karchmer–Wigderson converse and theorem

The other direction — a KW protocol gives a formula — completing
`kwCC f ≤ dmdepth f ≤ kwCC f + 1`.  The `+1` is an artifact of `DMTree` having no
depth-`0` constant (a constant needs depth `1`, via `constTree`).

* **`protocol_gives_formula` (proved)** — a depth-`d` protocol on `A×B` gives a
  DeMorgan formula of depth `≤ d+1` that is `1` on `A` and `0` on `B` (recursion:
  Bob's split ⇒ `∧`, Alice's split ⇒ `∨`; a leaf ⇒ a literal, or a constant when a
  side is empty);
* **`dmdepth_le_kwCC_succ` (proved)** — `dmdepth f ≤ kwCC f + 1`;
* **`kw_theorem` (proved)** — `kwCC f ≤ dmdepth f ≤ kwCC f + 1`: the
  Karchmer–Wigderson theorem for this formula model.

So formula depth and KW communication coincide up to `+1` — the honest,
machine-checked KW characterisation.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-- **The Karchmer–Wigderson converse (proved)**: a protocol gives a separating
formula of depth `≤ d+1`. -/
theorem protocol_gives_formula {n : ℕ} {A B : Finset (Fin n → Bool)} {d : ℕ}
    (h : HasProtocol A B d) :
    ∃ t : DMTree n, t.dep ≤ d + 1
      ∧ (∀ x ∈ A, t.eval x = true) ∧ (∀ y ∈ B, t.eval y = false) := by
  induction h with
  | leaf d i hi =>
    rename_i A B
    have hn : 0 < n := by have := i.isLt; omega
    by_cases hA : A.Nonempty
    · by_cases hB : B.Nonempty
      · obtain ⟨x₀, hx₀⟩ := hA
        obtain ⟨y₀, hy₀⟩ := hB
        refine ⟨DMTree.lit i (x₀ i), by simp [DMTree.dep], ?_, ?_⟩
        · intro x hx
          show (x i == x₀ i) = true
          have h1 := hi x hx y₀ hy₀
          have h2 := hi x₀ hx₀ y₀ hy₀
          revert h1 h2; cases x i <;> cases x₀ i <;> cases y₀ i <;> decide
        · intro y hy
          show (y i == x₀ i) = false
          have h3 := hi x₀ hx₀ y hy
          revert h3; cases y i <;> cases x₀ i <;> decide
      · refine ⟨constTree n hn true, by simp only [constTree, DMTree.dep]; omega, ?_, ?_⟩
        · intro x _; exact constTree_eval n hn true x
        · intro y hy; exact absurd ⟨y, hy⟩ hB
    · refine ⟨constTree n hn false, by simp only [constTree, DMTree.dep]; omega, ?_, ?_⟩
      · intro x hx; exact absurd ⟨x, hx⟩ hA
      · intro y _; exact constTree_eval n hn false y
  | bob p h0 h1 ih0 ih1 =>
    obtain ⟨t0, hd0, ha0, hb0⟩ := ih0
    obtain ⟨t1, hd1, ha1, hb1⟩ := ih1
    refine ⟨DMTree.and t0 t1, by simp only [DMTree.dep]; omega, ?_, ?_⟩
    · intro x hx; simp [DMTree.eval, ha0 x hx, ha1 x hx]
    · intro y hy
      by_cases hpy : p y = false
      · simp [DMTree.eval, hb0 y (Finset.mem_filter.mpr ⟨hy, hpy⟩)]
      · have hpy' : p y = true := by
          cases hh : p y with | false => exact absurd hh hpy | true => rfl
        simp [DMTree.eval, hb1 y (Finset.mem_filter.mpr ⟨hy, hpy'⟩)]
  | alice p h0 h1 ih0 ih1 =>
    obtain ⟨t0, hd0, ha0, hb0⟩ := ih0
    obtain ⟨t1, hd1, ha1, hb1⟩ := ih1
    refine ⟨DMTree.or t0 t1, by simp only [DMTree.dep]; omega, ?_, ?_⟩
    · intro x hx
      by_cases hpx : p x = false
      · simp [DMTree.eval, ha0 x (Finset.mem_filter.mpr ⟨hx, hpx⟩)]
      · have hpx' : p x = true := by
          cases hh : p x with | false => exact absurd hh hpx | true => rfl
        simp [DMTree.eval, ha1 x (Finset.mem_filter.mpr ⟨hx, hpx'⟩)]
    · intro y hy; simp [DMTree.eval, hb0 y hy, hb1 y hy]

/-- **`dmdepth f ≤ kwCC f + 1` (proved)** — the Karchmer–Wigderson lower bound
(with the `+1` constant artifact). -/
theorem dmdepth_le_kwCC_succ {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool) :
    dmdepth f ≤ kwCC f + 1 := by
  have hne : {d | HasProtocol (onesOf f) (zerosOf f) d}.Nonempty := by
    obtain ⟨t, ht⟩ := exists_dmtree hn f
    exact ⟨t.dep, kw_protocol_of_dmtree f t ht⟩
  obtain ⟨t, hd, ha, hb⟩ := protocol_gives_formula (Nat.sInf_mem hne)
  have hcomp : ∀ x, t.eval x = f x := by
    intro x
    cases hfx : f x
    · exact hb x (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hfx⟩)
    · exact ha x (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hfx⟩)
  calc dmdepth f ≤ t.dep := Nat.sInf_le ⟨t, hcomp, rfl⟩
    _ ≤ kwCC f + 1 := hd

/-- **THE KARCHMER–WIGDERSON THEOREM (proved)**: `kwCC f ≤ dmdepth f ≤ kwCC f + 1`. -/
theorem kw_theorem {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool) :
    kwCC f ≤ dmdepth f ∧ dmdepth f ≤ kwCC f + 1 :=
  ⟨kwCC_le_dmdepth hn f, dmdepth_le_kwCC_succ hn f⟩

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.protocol_gives_formula
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.kw_theorem
