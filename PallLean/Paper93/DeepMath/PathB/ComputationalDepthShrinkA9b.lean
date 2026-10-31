import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA9a

/-!
# Shrinkage brick A9b (core): projection and negation invariance

The two dimension-and-symmetry tools the block-hitting reduction needs:

* **`dmsizeC_proj_ge` (proved)** — if `h : (Fin N → Bool) → Bool` factors
  through an injection `ι : Fin k → Fin N` as `h y = g (y ∘ ι)`, then
  `dmsizeC g ≤ dmsizeC h`.  (Relabel the min tree of `h` by a left inverse of
  `ι` — the leaves land on `Fin k` and compute `g`.)  This is how the hardness
  of a `k`-bit block function transfers to the `k·m`-variable Andreev function.
* `flipSet` / `negSet` / **`dmsizeC_negSet` (proved)** — negating any set of
  input coordinates preserves `dmsizeC`.  This absorbs the block-parity
  constants `c_i` that appear when a block is restricted to one survivor.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-! ### Coordinate-projection lower bound -/

/-- **Projection lower bound (proved)**: a function factoring through an
injective coordinate map is at least as hard as its factor. -/
theorem dmsizeC_proj_ge {N k : ℕ} (hk : 0 < k) (ι : Fin k → Fin N)
    (hι : Function.Injective ι) (g : (Fin k → Bool) → Bool)
    (h : (Fin N → Bool) → Bool) (hfac : ∀ y, h y = g (fun i => y (ι i))) :
    dmsizeC g ≤ dmsizeC h := by
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨t, hte, htl⟩ := Nat.sInf_mem (dmsizeC_set_nonempty h)
  have htl2 : t.lsize0 = dmsizeC h := htl
  have hρι : ∀ i, Function.invFun ι (ι i) = i := Function.leftInverse_invFun hι
  have hmem : (relabelC (Function.invFun ι) t).lsize0
      ∈ {L | ∃ t' : DMTreeC k, (∀ z, t'.eval z = g z) ∧ t'.lsize0 = L} := by
    refine ⟨relabelC (Function.invFun ι) t, ?_, rfl⟩
    intro z
    rw [relabelC_eval, hte, hfac]
    congr 1
    funext i
    rw [hρι]
  have h1 : dmsizeC g ≤ (relabelC (Function.invFun ι) t).lsize0 :=
    Nat.sInf_le hmem
  rw [relabelC_lsize0, htl2] at h1
  exact h1

/-! ### Negation-set invariance -/

/-- Negate the literals sitting at the coordinates where `c` is true. -/
def flipSet {k : ℕ} (c : Fin k → Bool) : DMTreeC k → DMTreeC k
  | .lit i b => .lit i (xor (c i) b)
  | .cst b => .cst b
  | .and l r => .and (flipSet c l) (flipSet c r)
  | .or l r => .or (flipSet c l) (flipSet c r)

theorem flipSet_eval {k : ℕ} (c : Fin k → Bool) (t : DMTreeC k)
    (z : Fin k → Bool) :
    (flipSet c t).eval z = t.eval (fun i => xor (z i) (c i)) := by
  induction t with
  | lit i b =>
    show (z i == xor (c i) b) = (xor (z i) (c i) == b)
    cases z i <;> cases c i <;> cases b <;> rfl
  | cst b => rfl
  | and l r ihl ihr => simp only [flipSet, DMTreeC.eval, ihl, ihr]
  | or l r ihl ihr => simp only [flipSet, DMTreeC.eval, ihl, ihr]

theorem flipSet_lsize0 {k : ℕ} (c : Fin k → Bool) (t : DMTreeC k) :
    (flipSet c t).lsize0 = t.lsize0 := by
  induction t with
  | lit i b => rfl
  | cst b => rfl
  | and l r ihl ihr => simp only [flipSet, DMTreeC.lsize0, ihl, ihr]
  | or l r ihl ihr => simp only [flipSet, DMTreeC.lsize0, ihl, ihr]

/-- Negate a set of input coordinates of a function. -/
def negSet {k : ℕ} (c : Fin k → Bool) (f : (Fin k → Bool) → Bool) :
    (Fin k → Bool) → Bool :=
  fun z => f (fun i => xor (z i) (c i))

theorem dmsizeC_negSet_le {k : ℕ} (c : Fin k → Bool)
    (f : (Fin k → Bool) → Bool) : dmsizeC (negSet c f) ≤ dmsizeC f := by
  obtain ⟨t, hte, htl⟩ := Nat.sInf_mem (dmsizeC_set_nonempty f)
  have htl2 : t.lsize0 = dmsizeC f := htl
  have hmem : (flipSet c t).lsize0
      ∈ {L | ∃ t' : DMTreeC k, (∀ z, t'.eval z = negSet c f z) ∧ t'.lsize0 = L} := by
    refine ⟨flipSet c t, ?_, rfl⟩
    intro z
    rw [flipSet_eval]
    exact hte (fun i => xor (z i) (c i))
  have h1 : dmsizeC (negSet c f) ≤ (flipSet c t).lsize0 := Nat.sInf_le hmem
  rw [flipSet_lsize0, htl2] at h1
  exact h1

/-- **Negation-set invariance (proved)**: negating any coordinate set
preserves `dmsizeC`. -/
theorem dmsizeC_negSet {k : ℕ} (c : Fin k → Bool)
    (f : (Fin k → Bool) → Bool) : dmsizeC (negSet c f) = dmsizeC f := by
  refine le_antisymm (dmsizeC_negSet_le c f) ?_
  have hinv : negSet c (negSet c f) = f := by
    funext z
    show f (fun i => xor (xor (z i) (c i)) (c i)) = f z
    congr 1
    funext i
    cases z i <;> cases c i <;> rfl
  have h := dmsizeC_negSet_le c (negSet c f)
  rw [hinv] at h
  exact h

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.dmsizeC_proj_ge
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.dmsizeC_negSet
