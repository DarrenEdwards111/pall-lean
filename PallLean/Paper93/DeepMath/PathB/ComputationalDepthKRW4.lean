import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW3

/-!
# KRW brick 4: iterated composition and the depth-growth lower bound

The lever of the KRW program: iterate the block composition `d` times and the
depth grows LINEARLY in `d` (under the conjecture).  With a hard `≈ log n`-bit
gadget this yields `ω(log n)` depth and hence `P ⊄ NC¹` (the arity bookkeeping is
a later brick).

* **`nonconst_witness`** — a nonconstant function attains both `true` and `false`;
* **`comp_nonconstant` (proved)** — the composition of nonconstant functions is
  nonconstant (build the two witnessing inputs block-by-block);
* **`iterComp`** — `g^{⋄(d+1)}` as a `Σ`-value (arity `b^{d+1}`, avoiding the
  `b^1 = 1·b` defeq trap); **`iterComp_arity`** — the arity is `b^{d+1}`;
* **`iterComp_nonconstant` (proved)** — every iterate is nonconstant;
* **`krw_iter_lb` (from the conjecture)** — `(d+1)·D(g) ≤ D(g^{⋄(d+1)})`;
* **`krw_iter_lb_of_ge`** — with a gadget of depth `≥ D`,
  `(d+1)·D ≤ D(g^{⋄(d+1)})`.

Everything is unconditional except uses of `KRWConjectureDepth`, which stays an
explicit hypothesis.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-! ### Nonconstancy -/

/-- A nonconstant function attains both `true` and `false`. -/
theorem nonconst_witness {n : ℕ} (g : (Fin n → Bool) → Bool) (h : ∃ u u', g u ≠ g u') :
    ∃ ut uf, g ut = true ∧ g uf = false := by
  obtain ⟨u, u', huu⟩ := h
  by_cases hu : g u = true
  · refine ⟨u, u', hu, ?_⟩
    cases hc : g u' with
    | false => rfl
    | true => exact absurd (hu.trans hc.symm) huu
  · have hf : g u = false := by cases hh : g u with | false => rfl | true => exact absurd hh hu
    refine ⟨u', u, ?_, hf⟩
    cases hc : g u' with
    | true => rfl
    | false => exact absurd (hf.trans hc.symm) huu

/-- **Composition preserves nonconstancy (proved)**: build inputs whose block
vectors realise the outer witnesses. -/
theorem comp_nonconstant {m b : ℕ} (hb : 0 < b) (f : (Fin m → Bool) → Bool)
    (g : (Fin b → Bool) → Bool) (hfc : ∃ y y', f y ≠ f y') (hgc : ∃ u u', g u ≠ g u') :
    ∃ z z', comp hb f g z ≠ comp hb f g z' := by
  obtain ⟨ut, uf, hut, huf⟩ := nonconst_witness g hgc
  obtain ⟨yt, yf, hyt, hyf⟩ := nonconst_witness f hfc
  have hblock : ∀ (Y : Fin m → Bool) (j : Fin m),
      g (fun i => (cond (Y (blkOf hb (emb hb j i))) ut uf) (offOf hb (emb hb j i))) = Y j := by
    intro Y j
    have hin : (fun i => (cond (Y (blkOf hb (emb hb j i))) ut uf) (offOf hb (emb hb j i)))
        = cond (Y j) ut uf := by
      funext i; rw [blk_emb, off_emb]
    rw [hin]
    cases hyj : Y j
    · exact huf
    · exact hut
  have comp_lift : ∀ Y : Fin m → Bool,
      comp hb f g (fun i => (cond (Y (blkOf hb i)) ut uf) (offOf hb i)) = f Y := by
    intro Y
    show f (fun j => g (fun i =>
      (cond (Y (blkOf hb (emb hb j i))) ut uf) (offOf hb (emb hb j i)))) = f Y
    congr 1
    funext j
    exact hblock Y j
  refine ⟨(fun i => (cond (yt (blkOf hb i)) ut uf) (offOf hb i)),
          (fun i => (cond (yf (blkOf hb i)) ut uf) (offOf hb i)), ?_⟩
  rw [comp_lift, comp_lift, hyt, hyf]
  decide

/-! ### Iterated composition -/

/-- `d`-fold self-composition of `g`, as a `Σ`-value carrying its arity (`b^{d+1}`).
Sigma-valued to sidestep the `b^1 = 1·b` non-defeq trap. -/
def iterComp {b : ℕ} (hb : 0 < b) (g : (Fin b → Bool) → Bool) :
    ℕ → Σ N : ℕ, (Fin N → Bool) → Bool
  | 0 => ⟨b, g⟩
  | (d + 1) => ⟨(iterComp hb g d).1 * b, comp hb (iterComp hb g d).2 g⟩

theorem iterComp_arity {b : ℕ} (hb : 0 < b) (g : (Fin b → Bool) → Bool) (d : ℕ) :
    (iterComp hb g d).1 = b ^ (d + 1) := by
  induction d with
  | zero => simp [iterComp]
  | succ d ih =>
    show (iterComp hb g d).1 * b = b ^ (d + 1 + 1)
    rw [ih]; exact (pow_succ b (d + 1)).symm

theorem iterComp_nonconstant {b : ℕ} (hb : 0 < b) (g : (Fin b → Bool) → Bool)
    (hg : ∃ u u', g u ≠ g u') (d : ℕ) :
    ∃ y y', (iterComp hb g d).2 y ≠ (iterComp hb g d).2 y' := by
  induction d with
  | zero => exact hg
  | succ d ih => exact comp_nonconstant hb (iterComp hb g d).2 g ih hg

/-! ### The depth-growth lower bound -/

/-- **KRW ⟹ depth grows linearly in the number of compositions (proved from the
conjecture)**: `(d+1)·D(g) ≤ D(g^{⋄(d+1)})`. -/
theorem krw_iter_lb (H : KRWConjectureDepth) {b : ℕ} (hb : 0 < b)
    (g : (Fin b → Bool) → Bool) (hg : ∃ u u', g u ≠ g u') (d : ℕ) :
    (d + 1) * dmdepth g ≤ dmdepth (iterComp hb g d).2 := by
  induction d with
  | zero => simp [iterComp]
  | succ d ih =>
    have hnc : ∃ y y', (iterComp hb g d).2 y ≠ (iterComp hb g d).2 y' :=
      iterComp_nonconstant hb g hg d
    have hlb := H (iterComp hb g d).1 b hb (iterComp hb g d).2 g hnc hg
    show (d + 1 + 1) * dmdepth g ≤ dmdepth (comp hb (iterComp hb g d).2 g)
    calc (d + 1 + 1) * dmdepth g
        = (d + 1) * dmdepth g + dmdepth g := by ring
      _ ≤ dmdepth (iterComp hb g d).2 + dmdepth g := Nat.add_le_add_right ih _
      _ ≤ dmdepth (comp hb (iterComp hb g d).2 g) := hlb

/-- **KRW ⟹ a depth-`≥ D` gadget iterates to depth `≥ (d+1)·D`** (proved from the
conjecture).  With `D ≈ b` (a hard gadget) and `d+1` compositions this is the
super-logarithmic depth that would separate `P` from `NC¹`. -/
theorem krw_iter_lb_of_ge (H : KRWConjectureDepth) {b : ℕ} (hb : 0 < b)
    (g : (Fin b → Bool) → Bool) (hg : ∃ u u', g u ≠ g u') (D : ℕ) (hD : D ≤ dmdepth g)
    (d : ℕ) :
    (d + 1) * D ≤ dmdepth (iterComp hb g d).2 :=
  le_trans (Nat.mul_le_mul_left _ hD) (krw_iter_lb H hb g hg d)

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.comp_nonconstant
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.iterComp_nonconstant
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.krw_iter_lb
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.krw_iter_lb_of_ge
