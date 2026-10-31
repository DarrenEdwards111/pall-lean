import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTripleEngine

/-!
# N-Frame: the mixed triple engine — patterns from three different pairs kill one split

Pattern production for selector pairs begins with a structural finding, recorded honestly: **no single
selector pair carries all three patterns**.  Two selectors of the same clause interact only disjunctively
(`f = s ∨ t ∨ r` shapes: the sat/sat/unsat L-triple and the OR-shaped odd square exist, the
unsat/unsat/sat triple is impossible); selectors of different clauses interact only conjunctively
(`f = (s ∨ a) ∧ (t ∨ b) ∧ C` shapes: V0 and the AND-shaped odd square exist, V1 is impossible).  The
single-pair `triples_kill_split` therefore kills no selector pair directly.

The resolution is in the engine, not the patterns: the split's `op` is **global** — one op-matrix for the
whole circuit of the argument — so the odd square and the two L-triples may be sourced from **three
different separated pairs**.

  `triples_kill_split_mixed` — **PROVED**: a proper split dies from an odd square at one separated pair,
        a sat/sat/unsat L-triple at a second, and an unsat/unsat/sat L-triple at a third — ten canonical
        evaluations across up to three pairs, no XOR-square, core (`odd_matrix_triples_kill`) reused
        verbatim.

## Honest scope

Production now splits by interaction type: same-block selector pairs supply V1 + odd squares (the `ZBase`
family — `f(ZBase) = 0`, single flips `= 1`, needing only the double-flip eval); cross-block pairs supply
V0 + odd squares (needing a two-designated-block context construction, which the current single-block
`sat3Patch` machinery does not yet provide); sign pairs are already covered by the two-squares route.
The spanning argument assembles these into a kill for every fully-sign-aligned proper cut.  All named,
none claimed.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **THE MIXED ENGINE (proved)**: odd square, V1-triple, and V0-triple at three (possibly different)
separated pairs kill the split — the op-matrix is global. -/
theorem triples_kill_split_mixed {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n))
    (op : Bool → Bool → Bool) (g h : (Fin n → Bool) → Bool)
    (hg : ∀ x y : Fin n → Bool, (∀ i, i ∈ S → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin n → Bool, (∀ i, i ∉ S → x i = y i) → h x = h y)
    (hf : ∀ x, f x = op (g x) (h x))
    (s₁ t₁ s₂ t₂ s₃ t₃ : Fin n)
    (hs₁ : s₁ ∈ S) (ht₁ : t₁ ∉ S) (hst₁ : s₁ ≠ t₁)
    (hs₂ : s₂ ∈ S) (ht₂ : t₂ ∉ S) (hst₂ : s₂ ≠ t₂)
    (hs₃ : s₃ ∈ S) (ht₃ : t₃ ∉ S) (hst₃ : s₃ ≠ t₃)
    (w u₁ u₀ : Fin n → Bool)
    (hodd : xor (xor (f w) (f (Function.update w s₁ (!(w s₁)))))
        (xor (f (Function.update w t₁ (!(w t₁))))
          (f (Function.update (Function.update w s₁ (!(w s₁))) t₁ (!(w t₁))))) = true)
    (h11 : f u₁ = true)
    (h12 : f (Function.update (Function.update u₁ s₂ (!(u₁ s₂))) t₂ (!(u₁ t₂))) = true)
    (h13 : f (Function.update u₁ t₂ (!(u₁ t₂))) = false)
    (h01 : f u₀ = false)
    (h02 : f (Function.update (Function.update u₀ s₃ (!(u₀ s₃))) t₃ (!(u₀ t₃))) = false)
    (h03 : f (Function.update u₀ t₃ (!(u₀ t₃))) = true) : False := by
  classical
  have hhsP : ∀ (s : Fin n), s ∈ S → ∀ (z : Fin n → Bool) (v : Bool),
      h (Function.update z s v) = h z := by
    intro s hs z v
    apply hh
    intro i hi
    exact Function.update_of_ne (fun hcon => hi (by rw [hcon]; exact hs)) _ _
  have hgtP : ∀ (t : Fin n), t ∉ S → ∀ (z : Fin n → Bool) (v : Bool),
      g (Function.update z t v) = g z := by
    intro t ht z v
    apply hg
    intro i hi
    exact Function.update_of_ne (fun hcon => ht (by rw [← hcon]; exact hi)) _ _
  have hhdw : h (Function.update (Function.update w s₁ (!(w s₁))) t₁ (!(w t₁)))
      = h (Function.update w t₁ (!(w t₁))) := by
    rw [show Function.update (Function.update w s₁ (!(w s₁))) t₁ (!(w t₁))
        = Function.update (Function.update w t₁ (!(w t₁))) s₁ (!(w s₁)) from
      Function.update_comm hst₁ _ _ _]
    exact hhsP s₁ hs₁ _ _
  have hhd1 : h (Function.update (Function.update u₁ s₂ (!(u₁ s₂))) t₂ (!(u₁ t₂)))
      = h (Function.update u₁ t₂ (!(u₁ t₂))) := by
    rw [show Function.update (Function.update u₁ s₂ (!(u₁ s₂))) t₂ (!(u₁ t₂))
        = Function.update (Function.update u₁ t₂ (!(u₁ t₂))) s₂ (!(u₁ s₂)) from
      Function.update_comm hst₂ _ _ _]
    exact hhsP s₂ hs₂ _ _
  have hhd0 : h (Function.update (Function.update u₀ s₃ (!(u₀ s₃))) t₃ (!(u₀ t₃)))
      = h (Function.update u₀ t₃ (!(u₀ t₃))) := by
    rw [show Function.update (Function.update u₀ s₃ (!(u₀ s₃))) t₃ (!(u₀ t₃))
        = Function.update (Function.update u₀ t₃ (!(u₀ t₃))) s₃ (!(u₀ s₃)) from
      Function.update_comm hst₃ _ _ _]
    exact hhsP s₃ hs₃ _ _
  rw [hf, hf, hf, hf] at hodd
  rw [hf] at h11 h12 h13 h01 h02 h03
  rw [hhdw] at hodd
  rw [hhd1] at h12
  rw [hhd0] at h02
  simp only [hgtP t₁ ht₁, hhsP s₁ hs₁] at hodd
  simp only [hgtP t₂ ht₂, hhsP s₂ hs₂] at h12 h13
  simp only [hgtP t₃ ht₃, hhsP s₃ hs₃] at h02 h03
  exact odd_matrix_triples_kill op
    (g w) (h w) (g (Function.update w s₁ (!(w s₁))))
    (h (Function.update w t₁ (!(w t₁))))
    (g u₁) (h u₁) (g (Function.update u₁ s₂ (!(u₁ s₂))))
    (h (Function.update u₁ t₂ (!(u₁ t₂))))
    (g u₀) (h u₀) (g (Function.update u₀ s₃ (!(u₀ s₃))))
    (h (Function.update u₀ t₃ (!(u₀ t₃))))
    hodd h11 h12 h13 h01 h02 h03

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.triples_kill_split_mixed
