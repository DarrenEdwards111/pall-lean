import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA9b

/-!
# Shrinkage brick A9c: THE BLOCK-HITTING REDUCTION

The reduction that makes "≥ 1 free variable per block" (not the exponentially
rare "exactly one") suffice for Andreev:

* **`andreev_hit_ge` (proved)** — if a restriction's free set hits every block
  (each block has some free variable) and `B ≤ dmsizeC f`, then
  `B ≤ dmsizeC (restrF T v (andreevStar hm f))`.

Proof: pick a survivor per block; further-restrict all non-survivors.  The
block parity becomes `xor(survivor, cᵢ)` — a single-coordinate flip, so
`blockXor = oddF` on the block and `oddF_flip` (K2) computes it.  The result
factors through the survivor injection as `negSet c f ∘ π`, so `dmsizeC_proj_ge`
and `dmsizeC_negSet` (A9b) give `dmsizeC f ≤ dmsizeC(further restriction)`, and
restriction monotonicity (A9a) transfers it back up.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

theorem restrF_restrF_of_subset {n : ℕ} {T S : Finset (Fin n)} (hTS : T ⊆ S)
    {w' v : Fin n → Bool} (hagree : ∀ w ∈ T, w' w = v w)
    (g : (Fin n → Bool) → Bool) :
    restrF S w' (restrF T v g) = restrF S w' g := by
  funext y
  show g (fun i => if i ∈ T then v i else (if i ∈ S then w' i else y i))
    = g (fun i => if i ∈ S then w' i else y i)
  congr 1
  funext i
  by_cases hiT : i ∈ T
  · rw [if_pos hiT, if_pos (hTS hiT)]
    exact (hagree i hiT).symm
  · rw [if_neg hiT]

theorem blockXor_eq_oddF {k m : ℕ} (hm : 0 < m) (y : Fin (k * m) → Bool)
    (i : Fin k) : blockXor hm y i = oddF m (fun j => y (emb hm i j)) := by
  simp only [blockXor, oddF, Nat.odd_iff]

/-- **THE BLOCK-HITTING REDUCTION (proved).** -/
theorem andreev_hit_ge {k m : ℕ} (hm : 0 < m) (hk : 0 < k)
    (f : (Fin k → Bool) → Bool) (B : ℕ) (hB : B ≤ dmsizeC f)
    (T : Finset (Fin (k * m))) (v : Fin (k * m) → Bool)
    (hit : ∀ i : Fin k, ∃ j : Fin m, emb hm i j ∉ T) :
    B ≤ dmsizeC (restrF T v (andreevStar hm f)) := by
  classical
  choose p hp using hit
  set ι : Fin k → Fin (k * m) := fun i => emb hm i (p i) with hιdef
  set S : Finset (Fin (k * m)) :=
    Finset.univ.filter (fun w => ∀ i, ι i ≠ w) with hSdef
  set w' : Fin (k * m) → Bool := fun w => if w ∈ T then v w else false with hw'def
  set x0 : Fin k → Fin m → Bool :=
    fun i => fun j => if j = p i then false else w' (emb hm i j) with hx0def
  have hι_inj : Function.Injective ι := by
    intro i i' hii
    have h : blkOf hm (emb hm i (p i)) = blkOf hm (emb hm i' (p i')) :=
      congrArg (blkOf hm) hii
    rw [blk_emb, blk_emb] at h
    exact h
  -- membership: emb i j ∈ S ↔ j ≠ p i
  have hmemS : ∀ (i : Fin k) (j : Fin m), emb hm i j ∈ S ↔ j ≠ p i := by
    intro i j
    rw [hSdef, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    constructor
    · intro h hj
      subst hj
      exact h i rfl
    · intro hj i' hcon
      rw [hιdef] at hcon
      have hb := congrArg (blkOf hm) hcon
      rw [blk_emb, blk_emb] at hb
      subst hb
      have ho := congrArg (offOf hm) hcon
      rw [off_emb, off_emb] at ho
      exact hj ho.symm
  -- the factoring
  have hfac : ∀ y, restrF S w' (andreevStar hm f) y
      = negSet (fun i => oddF m (x0 i)) f (fun i => y (ι i)) := by
    intro y
    show f (fun i => blockXor hm (fun w => if w ∈ S then w' w else y w) i)
      = f (fun i => xor (y (ι i)) (oddF m (x0 i)))
    congr 1
    funext i
    rw [blockXor_eq_oddF]
    have hx0pi : (x0 i) (p i) = false := by
      simp only [hx0def, if_pos]
    have hblockfn : (fun j : Fin m =>
        (fun w => if w ∈ S then w' w else y w) (emb hm i j))
        = Function.update (x0 i) (p i) (y (ι i)) := by
      funext j
      by_cases hj : j = p i
      · subst hj
        show (if emb hm i (p i) ∈ S then w' (emb hm i (p i)) else y (emb hm i (p i)))
          = Function.update (x0 i) (p i) (y (ι i)) (p i)
        have hnotin : emb hm i (p i) ∉ S := by
          rw [hmemS i (p i)]; exact fun h => h rfl
        rw [Function.update_self, if_neg hnotin]
      · rw [Function.update_of_ne hj]
        show (if emb hm i j ∈ S then w' (emb hm i j) else y (emb hm i j))
          = x0 i j
        rw [if_pos ((hmemS i j).mpr hj)]
        show w' (emb hm i j) = (if j = p i then false else w' (emb hm i j))
        rw [if_neg hj]
    rw [hblockfn]
    cases hyi : y (ι i)
    · have hself : Function.update (x0 i) (p i) false = x0 i := by
        rw [← hx0pi]
        exact Function.update_eq_self (p i) (x0 i)
      rw [hself]
      cases oddF m (x0 i) <;> rfl
    · have hflip : Function.update (x0 i) (p i) true
          = Function.update (x0 i) (p i) (!((x0 i) (p i))) := by
        rw [hx0pi, Bool.not_false]
      rw [hflip, oddF_flip]
      cases oddF m (x0 i) <;> rfl
  -- projection lower bound
  have h1 : dmsizeC (negSet (fun i => oddF m (x0 i)) f)
      ≤ dmsizeC (restrF S w' (andreevStar hm f)) :=
    dmsizeC_proj_ge hk ι hι_inj (negSet (fun i => oddF m (x0 i)) f) _ hfac
  rw [dmsizeC_negSet] at h1
  -- monotonicity down from the T-restriction
  have hTS : T ⊆ S := by
    intro w hw
    rw [hSdef, Finset.mem_filter]
    refine ⟨Finset.mem_univ w, ?_⟩
    intro i' hcon
    rw [← hcon] at hw
    exact hp i' hw
  have hagree : ∀ w ∈ T, w' w = v w := by
    intro w hw
    rw [hw'def]
    show (if w ∈ T then v w else false) = v w
    rw [if_pos hw]
  have hid : restrF S w' (restrF T v (andreevStar hm f))
      = restrF S w' (andreevStar hm f) :=
    restrF_restrF_of_subset hTS hagree (andreevStar hm f)
  have h2 : dmsizeC (restrF S w' (andreevStar hm f))
      ≤ dmsizeC (restrF T v (andreevStar hm f)) := by
    rw [← hid]
    exact dmsizeC_restrF_le S w' (restrF T v (andreevStar hm f))
  omega

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.andreev_hit_ge
