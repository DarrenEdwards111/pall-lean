import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW1

/-!
# KRW brick 2: formula depth and the composition-depth conjecture

KRW lives most cleanly in DEPTH (the `NC¹ = O(log n)`-depth class is a depth
class, and composition is depth-ADDITIVE).  Here we add the depth measure and the
depth companion of KRW1's size bound.

* **`DMTree.dep`** — formula depth (leaves `0`, `∧`/`∨` add one over the deeper
  child); `neg_dep`, `relabel_dep` (both preserve depth);
* **`compTree_dep` (proved)** — `dep (compTree tg tf) = dep tf + dep tg`, EXACTLY:
  the leaf substitution stacks the depths;
* **`dmdepth`** — minimal formula depth of a function;
* **`dmdepth_comp_le` (proved)** — `D(f ⋄ g) ≤ D(f) + D(g)` (the upper half);
* **`KRWConjectureDepth`** — the OPEN conjecture: the matching lower bound
  `D(f) + D(g) ≤ D(f ⋄ g)` for nonconstant `f`, `g`, i.e. composition is
  depth-additive.  This is the Karchmer–Raz–Wigderson conjecture (idealized exact
  form; the real conjecture allows an `o(depth)` loss).  It is NOT proved here.
* **`krw_exact` (proved from the conjecture)** — under `KRWConjectureDepth`,
  `D(f ⋄ g) = D(f) + D(g)` exactly.

KRW ⟹ `P ⊄ NC¹` (via iterating the composition on a hard `≈ log n`-bit gadget) is
the cash-out; that iteration is a later brick.  Nothing here is that separation,
and nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-! ### Formula depth -/

/-- Formula depth: leaves have depth `0`; `∧`/`∨` add one over the deeper child. -/
def DMTree.dep {n : ℕ} : DMTree n → ℕ
  | .lit _ _ => 0
  | .and l r => 1 + max l.dep r.dep
  | .or l r => 1 + max l.dep r.dep

theorem neg_dep {n : ℕ} (t : DMTree n) : t.neg.dep = t.dep := by
  induction t with
  | lit i b => rfl
  | and l r ihl ihr => simp only [DMTree.neg, DMTree.dep, ihl, ihr]
  | or l r ihl ihr => simp only [DMTree.neg, DMTree.dep, ihl, ihr]

theorem relabel_dep {n m : ℕ} (f : Fin n → Fin m) (t : DMTree n) :
    (t.relabel f).dep = t.dep := by
  induction t with
  | lit i b => rfl
  | and l r ihl ihr => simp only [DMTree.relabel, DMTree.dep, ihl, ihr]
  | or l r ihl ihr => simp only [DMTree.relabel, DMTree.dep, ihl, ihr]

/-- **The composition stacks depths (proved)**: `dep (compTree tg tf) = dep tf + dep tg`. -/
theorem compTree_dep {m b : ℕ} (hb : 0 < b) (tg : DMTree b) (tf : DMTree m) :
    (compTree hb tg tf).dep = tf.dep + tg.dep := by
  induction tf with
  | lit j c =>
    cases c
    · show (tg.relabel (emb hb j)).neg.dep = 0 + tg.dep
      rw [neg_dep, relabel_dep, Nat.zero_add]
    · show (tg.relabel (emb hb j)).dep = 0 + tg.dep
      rw [relabel_dep, Nat.zero_add]
  | and l r ihl ihr =>
    show 1 + max (compTree hb tg l).dep (compTree hb tg r).dep
      = 1 + max l.dep r.dep + tg.dep
    rw [ihl, ihr]; omega
  | or l r ihl ihr =>
    show 1 + max (compTree hb tg l).dep (compTree hb tg r).dep
      = 1 + max l.dep r.dep + tg.dep
    rw [ihl, ihr]; omega

/-! ### The depth measure of a function -/

/-- Minimal DeMorgan formula depth of a function. -/
noncomputable def dmdepth {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  sInf {D | ∃ t : DMTree n, (∀ x, t.eval x = f x) ∧ t.dep = D}

/-- **The composition depth upper bound (proved)**: `D(f ⋄ g) ≤ D(f) + D(g)` —
assuming `f`, `g` have formulas at all (discharged later by universality). -/
theorem dmdepth_comp_le {m b : ℕ} (hb : 0 < b)
    (f : (Fin m → Bool) → Bool) (g : (Fin b → Bool) → Bool)
    (hfne : {D | ∃ t : DMTree m, (∀ x, t.eval x = f x) ∧ t.dep = D}.Nonempty)
    (hgne : {D | ∃ t : DMTree b, (∀ x, t.eval x = g x) ∧ t.dep = D}.Nonempty) :
    dmdepth (comp hb f g) ≤ dmdepth f + dmdepth g := by
  obtain ⟨tf, hfe, hfl⟩ := Nat.sInf_mem hfne
  obtain ⟨tg, hge, hgl⟩ := Nat.sInf_mem hgne
  have hfl' : tf.dep = dmdepth f := hfl
  have hgl' : tg.dep = dmdepth g := hgl
  have hte : ∀ z, (compTree hb tg tf).eval z = comp hb f g z := by
    intro z
    rw [compTree_eval, hfe]
    show f (fun j => tg.eval (fun i => z (emb hb j i))) = comp hb f g z
    simp only [comp]
    congr 1
    funext j
    exact hge _
  calc dmdepth (comp hb f g) ≤ (compTree hb tg tf).dep := Nat.sInf_le ⟨_, hte, rfl⟩
    _ = tf.dep + tg.dep := compTree_dep hb tg tf
    _ = dmdepth f + dmdepth g := by rw [hfl', hgl']

/-! ### The KRW conjecture -/

/-- The **Karchmer–Raz–Wigderson composition conjecture** (depth form, idealized
exact version).  The upper bound `dmdepth (f ⋄ g) ≤ dmdepth f + dmdepth g` is
proved (`dmdepth_comp_le`); KRW is the matching LOWER bound for nonconstant
functions — i.e. block composition is depth-additive.

This is the famous OPEN problem.  `khr_comp_mul` (K3) proves only the
Khrapchenko-measure shadow, which caps at `n²`; this conjecture is what would lift
Andreev's `n^{5/2}` to super-polynomial and hence give `P ⊄ NC¹`.  It is a named
socket, NOT proved. -/
def KRWConjectureDepth : Prop :=
  ∀ (m b : ℕ) (hb : 0 < b) (f : (Fin m → Bool) → Bool) (g : (Fin b → Bool) → Bool),
    (∃ y y', f y ≠ f y') → (∃ u u', g u ≠ g u') →
    dmdepth f + dmdepth g ≤ dmdepth (comp hb f g)

/-- **Exact additivity under the conjecture (proved from `KRWConjectureDepth`)**:
`D(f ⋄ g) = D(f) + D(g)`. -/
theorem krw_exact (H : KRWConjectureDepth) {m b : ℕ} (hb : 0 < b)
    (f : (Fin m → Bool) → Bool) (g : (Fin b → Bool) → Bool)
    (hfc : ∃ y y', f y ≠ f y') (hgc : ∃ u u', g u ≠ g u')
    (hfne : {D | ∃ t : DMTree m, (∀ x, t.eval x = f x) ∧ t.dep = D}.Nonempty)
    (hgne : {D | ∃ t : DMTree b, (∀ x, t.eval x = g x) ∧ t.dep = D}.Nonempty) :
    dmdepth (comp hb f g) = dmdepth f + dmdepth g :=
  le_antisymm (dmdepth_comp_le hb f g hfne hgne) (H m b hb f g hfc hgc)

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.compTree_dep
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.dmdepth_comp_le
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.krw_exact
