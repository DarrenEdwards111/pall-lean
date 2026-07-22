import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA6b

/-!
# Shrinkage brick A7a: relabeling and negation invariance

Formula size is invariant under the two symmetries that a shrinkage argument
uses to normalise a restricted function back to the hard function it contains:

* `relabelC`/`flipVar` — coordinate re-indexing and single-variable negation
  at the tree level (evaluation- and `lsize0`-transparent);
* **`dmsizeC_relabel_eq` (proved)** — `dmsizeC` is invariant under any
  coordinate permutation;
* **`dmsizeC_flip_eq` (proved)** — `dmsizeC` is invariant under negating a
  single input coordinate.

These are the moves that turn "the restricted function is `φ` up to
renaming/negation" into "the restricted formula is as large as `φ`".
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-! ### Relabeling -/

def relabelC {n m : ℕ} (g : Fin n → Fin m) : DMTreeC n → DMTreeC m
  | .lit i b => .lit (g i) b
  | .cst b => .cst b
  | .and l r => .and (relabelC g l) (relabelC g r)
  | .or l r => .or (relabelC g l) (relabelC g r)

theorem relabelC_eval {n m : ℕ} (g : Fin n → Fin m) (t : DMTreeC n)
    (x : Fin m → Bool) : (relabelC g t).eval x = t.eval (fun i => x (g i)) := by
  induction t with
  | lit i b => rfl
  | cst b => rfl
  | and l r ihl ihr => simp only [relabelC, DMTreeC.eval, ihl, ihr]
  | or l r ihl ihr => simp only [relabelC, DMTreeC.eval, ihl, ihr]

theorem relabelC_lsize0 {n m : ℕ} (g : Fin n → Fin m) (t : DMTreeC n) :
    (relabelC g t).lsize0 = t.lsize0 := by
  induction t with
  | lit i b => rfl
  | cst b => rfl
  | and l r ihl ihr => simp only [relabelC, DMTreeC.lsize0, ihl, ihr]
  | or l r ihl ihr => simp only [relabelC, DMTreeC.lsize0, ihl, ihr]

theorem dmsizeC_comp_le {n : ℕ} (g : Fin n → Fin n)
    (f : (Fin n → Bool) → Bool) :
    dmsizeC (fun x => f (fun i => x (g i))) ≤ dmsizeC f := by
  obtain ⟨t, hte, htl⟩ := Nat.sInf_mem (dmsizeC_set_nonempty f)
  refine Nat.sInf_le ⟨relabelC g t, ?_, ?_⟩
  · intro x
    rw [relabelC_eval]
    exact hte (fun i => x (g i))
  · rw [relabelC_lsize0]
    exact htl

/-- **Permutation invariance of `dmsizeC` (proved).** -/
theorem dmsizeC_relabel_eq {n : ℕ} (e : Equiv.Perm (Fin n))
    (f : (Fin n → Bool) → Bool) :
    dmsizeC (fun x => f (fun i => x (e i))) = dmsizeC f := by
  refine le_antisymm (dmsizeC_comp_le e f) ?_
  have h := dmsizeC_comp_le e.symm (fun x => f (fun i => x (e i)))
  have hf : (fun x : Fin n → Bool =>
      (fun y : Fin n → Bool => f (fun i => y (e i))) (fun i => x (e.symm i)))
      = f := by
    funext x
    show f (fun i => x (e.symm (e i))) = f x
    congr 1
    funext i
    rw [Equiv.symm_apply_apply]
  rw [hf] at h
  exact h

/-! ### Single-variable negation -/

def flipVar {n : ℕ} (j : Fin n) : DMTreeC n → DMTreeC n
  | .lit i b => if i = j then .lit i (!b) else .lit i b
  | .cst b => .cst b
  | .and l r => .and (flipVar j l) (flipVar j r)
  | .or l r => .or (flipVar j l) (flipVar j r)

theorem flipVar_eval {n : ℕ} (j : Fin n) (t : DMTreeC n) (x : Fin n → Bool) :
    (flipVar j t).eval x = t.eval (Function.update x j (!(x j))) := by
  induction t with
  | lit i b =>
    by_cases hij : i = j
    · subst hij
      have h1 : flipVar i (DMTreeC.lit i b) = DMTreeC.lit i (!b) := by
        show (if i = i then (DMTreeC.lit i (!b) : DMTreeC n) else .lit i b)
          = .lit i (!b)
        rw [if_pos rfl]
      rw [h1]
      simp only [DMTreeC.eval, Function.update_self]
      cases x i <;> cases b <;> rfl
    · have h1 : flipVar j (DMTreeC.lit i b) = DMTreeC.lit i b := by
        show (if i = j then (DMTreeC.lit i (!b) : DMTreeC n) else .lit i b)
          = .lit i b
        rw [if_neg hij]
      rw [h1]
      simp only [DMTreeC.eval, Function.update_of_ne hij]
  | cst b => rfl
  | and l r ihl ihr => simp only [flipVar, DMTreeC.eval, ihl, ihr]
  | or l r ihl ihr => simp only [flipVar, DMTreeC.eval, ihl, ihr]

theorem flipVar_lsize0 {n : ℕ} (j : Fin n) (t : DMTreeC n) :
    (flipVar j t).lsize0 = t.lsize0 := by
  induction t with
  | lit i b =>
    by_cases hij : i = j
    · have h1 : flipVar j (DMTreeC.lit i b) = DMTreeC.lit i (!b) := by
        show (if i = j then (DMTreeC.lit i (!b) : DMTreeC n) else .lit i b)
          = .lit i (!b)
        rw [if_pos hij]
      rw [h1]
      rfl
    · have h1 : flipVar j (DMTreeC.lit i b) = DMTreeC.lit i b := by
        show (if i = j then (DMTreeC.lit i (!b) : DMTreeC n) else .lit i b)
          = .lit i b
        rw [if_neg hij]
      rw [h1]
  | cst b => rfl
  | and l r ihl ihr => simp only [flipVar, DMTreeC.lsize0, ihl, ihr]
  | or l r ihl ihr => simp only [flipVar, DMTreeC.lsize0, ihl, ihr]

theorem dmsizeC_flip_le {n : ℕ} (j : Fin n) (f : (Fin n → Bool) → Bool) :
    dmsizeC (fun x => f (Function.update x j (!(x j)))) ≤ dmsizeC f := by
  obtain ⟨t, hte, htl⟩ := Nat.sInf_mem (dmsizeC_set_nonempty f)
  refine Nat.sInf_le ⟨flipVar j t, ?_, ?_⟩
  · intro x
    rw [flipVar_eval]
    exact hte (Function.update x j (!(x j)))
  · rw [flipVar_lsize0]
    exact htl

/-- **Single-coordinate negation invariance of `dmsizeC` (proved).** -/
theorem dmsizeC_flip_eq {n : ℕ} (j : Fin n) (f : (Fin n → Bool) → Bool) :
    dmsizeC (fun x => f (Function.update x j (!(x j)))) = dmsizeC f := by
  refine le_antisymm (dmsizeC_flip_le j f) ?_
  have h := dmsizeC_flip_le j (fun x => f (Function.update x j (!(x j))))
  have hf : (fun x : Fin n → Bool =>
      (fun y : Fin n → Bool => f (Function.update y j (!(y j))))
        (Function.update x j (!(x j)))) = f := by
    funext x
    show f (Function.update (Function.update x j (!(x j))) j
      (!(Function.update x j (!(x j)) j))) = f x
    rw [flip_flip]
  rw [hf] at h
  exact h

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.dmsizeC_relabel_eq
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.dmsizeC_flip_eq
