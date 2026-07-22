import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKhrK3b

/-!
# KRW brick 1: the composition upper bound

The Karchmer–Raz–Wigderson program studies the DeMorgan formula complexity of the
block composition `f ⋄ g` (here `comp`, `m·b` variables).  Two halves frame it:

* the **lower** half — `khr_comp_mul` (K3) — proves the *Khrapchenko-measure*
  shadow `Q(f)·Q(g) ≤ L(f ⋄ g)`, but Khrapchenko caps at `n²`
  (`khr_value_le`), so it cannot reach the true KRW regime;
* the **upper** half — proved here — `L(f ⋄ g) ≤ L(f)·L(g)`, obtained by
  substituting a relabelled copy of a formula for `g` into each leaf of a
  formula for `f` (negated at the `false` leaves, DeMorgan-style).

The KRW conjecture is that the upper bound is essentially tight
(`L(f ⋄ g) ≥ L(f)·L(g)^{1−o(1)}`, equivalently near-additive depth) — the OPEN
problem whose resolution would lift Andreev's `n^{5/2}` to super-polynomial and
hence separate `P` from `NC¹`.  Nothing here is that conjecture, and nothing here
is `P ≠ NP`.

* **`DMTree.neg`** — DeMorgan negation (flip leaves, swap `∧`/`∨`); `neg_eval`,
  `neg_lsize`;
* **`compTree`** — the leaf-substitution of `tg` into `tf`; `compTree_eval`,
  `compTree_lsize` (`= lsize tf · lsize tg`, exactly);
* **`comp_tree_upper` (proved)** — any formulas for `f`, `g` yield a formula for
  `f ⋄ g` of size `lsize tf · lsize tg`;
* **`dmsize_comp_le` (proved)** — `L(f ⋄ g) ≤ L(f)·L(g)` (given that `f`, `g`
  have formulas at all).
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-! ### DeMorgan negation -/

/-- DeMorgan negation: flip the literals, swap `∧`/`∨`. -/
def DMTree.neg {n : ℕ} : DMTree n → DMTree n
  | .lit i b => .lit i (!b)
  | .and l r => .or l.neg r.neg
  | .or l r => .and l.neg r.neg

theorem neg_eval {n : ℕ} (t : DMTree n) (x : Fin n → Bool) :
    t.neg.eval x = !(t.eval x) := by
  induction t with
  | lit i b =>
    show (x i == !b) = !(x i == b)
    cases x i <;> cases b <;> rfl
  | and l r ihl ihr =>
    show ((l.neg).eval x || (r.neg).eval x) = !(l.eval x && r.eval x)
    rw [ihl, ihr, Bool.not_and]
  | or l r ihl ihr =>
    show ((l.neg).eval x && (r.neg).eval x) = !(l.eval x || r.eval x)
    rw [ihl, ihr, Bool.not_or]

theorem neg_lsize {n : ℕ} (t : DMTree n) : t.neg.lsize = t.lsize := by
  induction t with
  | lit i b => rfl
  | and l r ihl ihr => simp only [DMTree.neg, DMTree.lsize, ihl, ihr]
  | or l r ihl ihr => simp only [DMTree.neg, DMTree.lsize, ihl, ihr]

/-! ### The leaf substitution -/

/-- Substitute a relabelled copy of `tg` into each leaf of `tf`: leaf `lit j b`
becomes the block-`j` copy of `tg`, negated when `b = false`.  The result
computes `f ⋄ g` whenever `tf`, `tg` compute `f`, `g`. -/
def compTree {m b : ℕ} (hb : 0 < b) (tg : DMTree b) : DMTree m → DMTree (m * b)
  | .lit j true => tg.relabel (emb hb j)
  | .lit j false => (tg.relabel (emb hb j)).neg
  | .and l r => .and (compTree hb tg l) (compTree hb tg r)
  | .or l r => .or (compTree hb tg l) (compTree hb tg r)

theorem compTree_eval {m b : ℕ} (hb : 0 < b) (tg : DMTree b) (tf : DMTree m)
    (z : Fin (m * b) → Bool) :
    (compTree hb tg tf).eval z
      = tf.eval (fun j => tg.eval (fun i => z (emb hb j i))) := by
  induction tf with
  | lit j c =>
    cases c
    · simp only [compTree, DMTree.eval, neg_eval, relabel_eval]
      cases tg.eval (fun i => z (emb hb j i)) <;> rfl
    · simp only [compTree, DMTree.eval, relabel_eval]
      cases tg.eval (fun i => z (emb hb j i)) <;> rfl
  | and l r ihl ihr => simp only [compTree, DMTree.eval, ihl, ihr]
  | or l r ihl ihr => simp only [compTree, DMTree.eval, ihl, ihr]

theorem compTree_lsize {m b : ℕ} (hb : 0 < b) (tg : DMTree b) (tf : DMTree m) :
    (compTree hb tg tf).lsize = tf.lsize * tg.lsize := by
  induction tf with
  | lit j c =>
    cases c
    · show (tg.relabel (emb hb j)).neg.lsize = 1 * tg.lsize
      rw [neg_lsize, relabel_lsize, Nat.one_mul]
    · show (tg.relabel (emb hb j)).lsize = 1 * tg.lsize
      rw [relabel_lsize, Nat.one_mul]
  | and l r ihl ihr =>
    show (compTree hb tg l).lsize + (compTree hb tg r).lsize = (l.lsize + r.lsize) * tg.lsize
    rw [ihl, ihr, Nat.add_mul]
  | or l r ihl ihr =>
    show (compTree hb tg l).lsize + (compTree hb tg r).lsize = (l.lsize + r.lsize) * tg.lsize
    rw [ihl, ihr, Nat.add_mul]

/-! ### The composition upper bound -/

/-- **The composition upper bound, tree level (proved)**: formulas for `f` and
`g` compose into a formula for `f ⋄ g` of size exactly `lsize tf · lsize tg`. -/
theorem comp_tree_upper {m b : ℕ} (hb : 0 < b)
    (f : (Fin m → Bool) → Bool) (g : (Fin b → Bool) → Bool)
    (tf : DMTree m) (tg : DMTree b)
    (hf : ∀ y, tf.eval y = f y) (hg : ∀ u, tg.eval u = g u) :
    ∃ t : DMTree (m * b),
      (∀ z, t.eval z = comp hb f g z) ∧ t.lsize = tf.lsize * tg.lsize := by
  refine ⟨compTree hb tg tf, fun z => ?_, compTree_lsize hb tg tf⟩
  rw [compTree_eval, hf]
  show f (fun j => tg.eval (fun i => z (emb hb j i))) = comp hb f g z
  simp only [comp]
  congr 1
  funext j
  exact hg _

/-- **The composition upper bound, `L(f ⋄ g) ≤ L(f)·L(g)` (proved)** — assuming
`f` and `g` have DeMorgan formulas at all (always true; the discharge is
universality of DeMorgan formulas). -/
theorem dmsize_comp_le {m b : ℕ} (hb : 0 < b)
    (f : (Fin m → Bool) → Bool) (g : (Fin b → Bool) → Bool)
    (hfne : {L | ∃ t : DMTree m, (∀ x, t.eval x = f x) ∧ t.lsize = L}.Nonempty)
    (hgne : {L | ∃ t : DMTree b, (∀ x, t.eval x = g x) ∧ t.lsize = L}.Nonempty) :
    dmsize (comp hb f g) ≤ dmsize f * dmsize g := by
  obtain ⟨tf, hfe, hfl⟩ := Nat.sInf_mem hfne
  obtain ⟨tg, hge, hgl⟩ := Nat.sInf_mem hgne
  have hfl' : tf.lsize = dmsize f := hfl
  have hgl' : tg.lsize = dmsize g := hgl
  obtain ⟨t, hte, htl⟩ := comp_tree_upper hb f g tf tg hfe hge
  calc dmsize (comp hb f g) ≤ t.lsize := Nat.sInf_le ⟨t, hte, rfl⟩
    _ = tf.lsize * tg.lsize := htl
    _ = dmsize f * dmsize g := by rw [hfl', hgl']

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.comp_tree_upper
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.dmsize_comp_le
