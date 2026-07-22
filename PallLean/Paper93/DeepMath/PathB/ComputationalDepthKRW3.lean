import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW2

/-!
# KRW brick 3: universality of DeMorgan formulas

Every Boolean function on `Fin n` (`n ≥ 1`) is computed by some DeMorgan formula
(Shannon expansion on the last coordinate, bottoming out at constant gadgets).
This makes `dmsize` and `dmdepth` total measures and discharges the
formula-existence hypotheses carried by KRW1/KRW2's composition bounds.

* **`constTree`** — a constant formula (`x₀ ∨ ¬x₀` / `x₀ ∧ ¬x₀`); `constTree_eval`;
* **`shannon_eval`** — the branch identity for `(x_L ∧ a) ∨ (¬x_L ∧ b)`;
* **`exists_dmtree` (proved)** — every `f` on `Fin n`, `n ≥ 1`, has a formula;
* **`dmsize_comp_le'` / `dmdepth_comp_le'` (proved)** — the composition size/depth
  upper bounds, now UNCONDITIONAL;
* **`krw_exact'` (from the conjecture)** — exact depth additivity, hypothesis-free
  save the KRW socket and nonconstancy.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-! ### Constant formulas -/

/-- A constant DeMorgan formula on `n ≥ 1` variables. -/
def constTree (n : ℕ) (hn : 0 < n) : Bool → DMTree n
  | true => .or (.lit ⟨0, hn⟩ true) (.lit ⟨0, hn⟩ false)
  | false => .and (.lit ⟨0, hn⟩ true) (.lit ⟨0, hn⟩ false)

theorem constTree_eval (n : ℕ) (hn : 0 < n) (b : Bool) (x : Fin n → Bool) :
    (constTree n hn b).eval x = b := by
  cases b
  · show ((x ⟨0, hn⟩ == true) && (x ⟨0, hn⟩ == false)) = false
    cases x ⟨0, hn⟩ <;> rfl
  · show ((x ⟨0, hn⟩ == true) || (x ⟨0, hn⟩ == false)) = true
    cases x ⟨0, hn⟩ <;> rfl

/-! ### The Shannon branch -/

/-- `(x_L ∧ a) ∨ (¬x_L ∧ b)` selects `a` or `b` on the value of `x_L`. -/
theorem shannon_eval {n : ℕ} (L : Fin n) (a b : DMTree n) (x : Fin n → Bool) :
    (DMTree.or (.and (.lit L true) a) (.and (.lit L false) b)).eval x
      = (if x L = true then a.eval x else b.eval x) := by
  show (((x L == true) && a.eval x) || ((x L == false) && b.eval x))
    = (if x L = true then a.eval x else b.eval x)
  cases x L <;> simp

/-! ### Universality -/

/-- **Universality (proved)**: every function on `Fin (n+1)` has a DeMorgan
formula.  Shannon expansion on the last coordinate. -/
theorem exists_dmtree_succ (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) :
    ∃ t : DMTree (n + 1), ∀ x, t.eval x = f x := by
  induction n with
  | zero =>
    refine ⟨.or (.and (.lit (Fin.last 0) true) (constTree 1 Nat.one_pos (f (fun _ => true))))
               (.and (.lit (Fin.last 0) false) (constTree 1 Nat.one_pos (f (fun _ => false)))),
           fun x => ?_⟩
    rw [shannon_eval, constTree_eval, constTree_eval]
    by_cases hxl : x (Fin.last 0) = true
    · rw [if_pos hxl]
      congr 1
      funext i
      fin_cases i
      exact hxl.symm
    · rw [if_neg hxl]
      have hxf : x (Fin.last 0) = false := by
        cases h : x (Fin.last 0) <;> simp_all
      congr 1
      funext i
      fin_cases i
      exact hxf.symm
  | succ n ih =>
    obtain ⟨t1, ht1⟩ := ih (fun y => f (Fin.snoc y true))
    obtain ⟨t0, ht0⟩ := ih (fun y => f (Fin.snoc y false))
    refine ⟨.or (.and (.lit (Fin.last (n + 1)) true) (t1.relabel Fin.castSucc))
               (.and (.lit (Fin.last (n + 1)) false) (t0.relabel Fin.castSucc)),
           fun x => ?_⟩
    rw [shannon_eval, relabel_eval, relabel_eval, ht1, ht0]
    by_cases hxl : x (Fin.last (n + 1)) = true
    · rw [if_pos hxl]
      show f (Fin.snoc (fun i => x (Fin.castSucc i)) true) = f x
      congr 1
      rw [← hxl]; exact Fin.snoc_init_self x
    · rw [if_neg hxl]
      have hxf : x (Fin.last (n + 1)) = false := by
        cases h : x (Fin.last (n + 1)) <;> simp_all
      show f (Fin.snoc (fun i => x (Fin.castSucc i)) false) = f x
      congr 1
      rw [← hxf]; exact Fin.snoc_init_self x

/-- **Universality (proved)**: every function on `Fin n`, `n ≥ 1`, has a formula. -/
theorem exists_dmtree {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool) :
    ∃ t : DMTree n, ∀ x, t.eval x = f x := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact exists_dmtree_succ m f

/-! ### The dmsize / dmdepth sets are nonempty -/

theorem dmsize_set_nonempty {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool) :
    {L | ∃ t : DMTree n, (∀ x, t.eval x = f x) ∧ t.lsize = L}.Nonempty := by
  obtain ⟨t, ht⟩ := exists_dmtree hn f
  exact ⟨t.lsize, t, ht, rfl⟩

theorem dmdepth_set_nonempty {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool) :
    {D | ∃ t : DMTree n, (∀ x, t.eval x = f x) ∧ t.dep = D}.Nonempty := by
  obtain ⟨t, ht⟩ := exists_dmtree hn f
  exact ⟨t.dep, t, ht, rfl⟩

/-! ### Unconditional composition bounds -/

/-- **The composition size bound, unconditional (proved)**: `L(f ⋄ g) ≤ L(f)·L(g)`. -/
theorem dmsize_comp_le' {m b : ℕ} (hm : 0 < m) (hb : 0 < b)
    (f : (Fin m → Bool) → Bool) (g : (Fin b → Bool) → Bool) :
    dmsize (comp hb f g) ≤ dmsize f * dmsize g :=
  dmsize_comp_le hb f g (dmsize_set_nonempty hm f) (dmsize_set_nonempty hb g)

/-- **The composition depth bound, unconditional (proved)**: `D(f ⋄ g) ≤ D(f)+D(g)`. -/
theorem dmdepth_comp_le' {m b : ℕ} (hm : 0 < m) (hb : 0 < b)
    (f : (Fin m → Bool) → Bool) (g : (Fin b → Bool) → Bool) :
    dmdepth (comp hb f g) ≤ dmdepth f + dmdepth g :=
  dmdepth_comp_le hb f g (dmdepth_set_nonempty hm f) (dmdepth_set_nonempty hb g)

/-- **Exact depth additivity under KRW (proved from the conjecture)**, now needing
only nonconstancy. -/
theorem krw_exact' (H : KRWConjectureDepth) {m b : ℕ} (hm : 0 < m) (hb : 0 < b)
    (f : (Fin m → Bool) → Bool) (g : (Fin b → Bool) → Bool)
    (hfc : ∃ y y', f y ≠ f y') (hgc : ∃ u u', g u ≠ g u') :
    dmdepth (comp hb f g) = dmdepth f + dmdepth g :=
  krw_exact H hb f g hfc hgc (dmdepth_set_nonempty hm f) (dmdepth_set_nonempty hb g)

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.exists_dmtree
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.dmsize_comp_le'
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.dmdepth_comp_le'
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.krw_exact'
