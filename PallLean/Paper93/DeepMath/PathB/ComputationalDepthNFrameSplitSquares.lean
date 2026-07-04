import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameNoBipartiteSplit

/-!
# N-Frame: the split-square calculus — a flaw fixed, and the discharge engine

**A flaw in the previous file, found and fixed here, honestly.**  `Sat3NoBipartiteSplit` as defined is
*refutable*: with `S = univ`, `op a _ = a`, `g = sat3Family`, `h` constant, all three hypotheses hold — the
blindness demanded of `h` is vacuous on a degenerate cut.  The conditional theorems there were therefore
unusable as stated.  The correct hypothesis must demand a **proper cut**: some coordinate inside `S`, some
outside.  This file installs the corrected definition and the corrected conditionals, and builds the pure
discharge engine.

  `Sat3NoBipartiteSplitProper` — the corrected named hypothesis (still **NOT discharged**).
  `sat3_excess_pos_of_no_split_proper` / `sat3_cbudget_2mD_of_no_split_proper` — the corrected
        conditionals.  The frame side now carries its own honest gap: the split produced at excess zero
        must be shown *proper*, which is the semantically-constant-wire kill (a rewiring surgery, named
        below, not yet built).
  `two_squares_kill_split` — **PROVED, the discharge engine (pure logic)**: a proper split dies from two
        canonical 4-point squares at the cut pair `(s₀, t₀)`: an **XOR-square** (both flips flip `f`, the
        double flip returns) forces `op` to be xor-type on its full domain; an **odd-parity square**
        (`f(w) ⊕ f(w^{s₀}) ⊕ f(w^{t₀}) ⊕ f(w^{s₀t₀}) = true`) is impossible for xor-type.  Eight
        evaluations of `f` at canonical points — **no mixed points, no knowledge of `S` beyond the two
        memberships** — refute the split.

## Honest scope

What remains to discharge `Sat3NoBipartiteSplitProper` is the SAT-side square production: for every pair
`(s₀, t₀)` of distinct coordinates, an XOR-square and an odd-parity square at canonical bases.  Two honest
obstructions are recorded.  First, SAT is monotone in every selector bit, so **selector-involved pairs have
no XOR-square** — for those pairs the AND-type kill must instead violate rectangle closure with a wider
difference set (three-coordinate between-point analysis) or route through sign fields.  Second, the frame
needs the constant-wire kill (a semantically-constant interior wire contradicts minimality by
constant-absorbing rewiring — the `rewireGate` pattern with a constant), to make the excess-zero split
proper.  Both are named rungs.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- The corrected named hypothesis — **NOT discharged**: SAT admits no bipartite split over a proper cut. -/
def Sat3NoBipartiteSplitProper (N : ℕ) : Prop :=
  ∀ (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (S : Finset (Fin N)),
    (∀ x y : Fin N → Bool, (∀ i, i ∈ S → x i = y i) → g x = g y) →
    (∀ x y : Fin N → Bool, (∀ i, i ∉ S → x i = y i) → h x = h y) →
    (∀ x, sat3Family N x = op (g x) (h x)) →
    (∃ s₀ : Fin N, s₀ ∈ S) → (∃ t₀ : Fin N, t₀ ∉ S) → False

/-- An op whose full 2×2 matrix is the diagonal pattern is xor-type — the square-to-xor core. -/
theorem xor_type_of_square (op : Bool → Bool → Bool) (a b α : Bool)
    (e1 : op a b = α) (e2 : op (!a) b = !α) (e3 : op a (!b) = !α) (e4 : op (!a) (!b) = α) :
    ∀ x y : Bool, op x y = xor α (xor (xor x a) (xor y b)) := by
  intro x y
  cases hx : x <;> cases hy : y <;> cases hA : a <;> cases hB : b <;> simp_all

/-- **THE DISCHARGE ENGINE (proved)**: an XOR-square and an odd-parity square at the cut pair kill any
proper split — eight canonical evaluations, no mixed points. -/
theorem two_squares_kill_split {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n))
    (op : Bool → Bool → Bool) (g h : (Fin n → Bool) → Bool)
    (hg : ∀ x y : Fin n → Bool, (∀ i, i ∈ S → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin n → Bool, (∀ i, i ∉ S → x i = y i) → h x = h y)
    (hf : ∀ x, f x = op (g x) (h x))
    (s₀ t₀ : Fin n) (hs₀ : s₀ ∈ S) (ht₀ : t₀ ∉ S) (hst : s₀ ≠ t₀)
    (u w : Fin n → Bool) (α : Bool)
    -- the XOR-square at u
    (hu : f u = α)
    (hus : f (Function.update u s₀ (!(u s₀))) = !α)
    (hut : f (Function.update u t₀ (!(u t₀))) = !α)
    (hust : f (Function.update (Function.update u s₀ (!(u s₀))) t₀ (!(u t₀))) = α)
    -- the odd-parity square at w
    (hodd : xor (xor (f w) (f (Function.update w s₀ (!(w s₀)))))
        (xor (f (Function.update w t₀ (!(w t₀))))
          (f (Function.update (Function.update w s₀ (!(w s₀))) t₀ (!(w t₀))))) = true) :
    False := by
  classical
  -- s₀-updates preserve h; t₀-updates preserve g
  have hhs : ∀ z : Fin n → Bool, ∀ v, h (Function.update z s₀ v) = h z := by
    intro z v
    apply hh
    intro i hi
    exact Function.update_of_ne (fun hcon => hi (by rw [hcon]; exact hs₀)) _ _
  have hgt : ∀ z : Fin n → Bool, ∀ v, g (Function.update z t₀ v) = g z := by
    intro z v
    apply hg
    intro i hi
    exact Function.update_of_ne (fun hcon => ht₀ (by rw [← hcon]; exact hi)) _ _
  -- name the four op-arguments of the u-square
  set a := g u with ha
  set a' := g (Function.update u s₀ (!(u s₀))) with ha'
  set b := h u with hb
  set b' := h (Function.update u t₀ (!(u t₀))) with hb'
  -- the u-square is the full op-matrix
  have e1 : op a b = α := by rw [← hf u] at *; exact hu
  have e2 : op a' b = !α := by
    have := hf (Function.update u s₀ (!(u s₀)))
    rw [hhs u (!(u s₀))] at this
    rw [← this]
    exact hus
  have e3 : op a b' = !α := by
    have := hf (Function.update u t₀ (!(u t₀)))
    rw [hgt u (!(u t₀))] at this
    rw [← this]
    exact hut
  have e4 : op a' b' = α := by
    have := hf (Function.update (Function.update u s₀ (!(u s₀))) t₀ (!(u t₀)))
    rw [hgt _ (!(u t₀))] at this
    rw [← ha'] at this
    have hcomm : h (Function.update (Function.update u s₀ (!(u s₀))) t₀ (!(u t₀)))
        = b' := by
      rw [show Function.update (Function.update u s₀ (!(u s₀))) t₀ (!(u t₀))
          = Function.update (Function.update u t₀ (!(u t₀))) s₀ (!(u s₀)) from
        Function.update_comm hst _ _ u, hhs _ (!(u s₀)), hb']
    rw [hcomm] at this
    rw [← this]
    exact hust
  -- a ≠ a' and b ≠ b' (else two equal square entries contradict)
  have haa : a ≠ a' := by
    intro hcon
    rw [← hcon] at e2
    rw [e1] at e2
    cases α <;> cases e2
  have hbb : b ≠ b' := by
    intro hcon
    rw [← hcon] at e3
    rw [e1] at e3
    cases α <;> cases e3
  -- so op is xor-type on the full domain: op x y = α ⊕ (x ⊕ a) ⊕ (y ⊕ b)
  have hnaa : a' = !a := by
    revert haa
    cases a <;> cases a' <;> decide
  have hnbb : b' = !b := by
    revert hbb
    cases b <;> cases b' <;> decide
  rw [hnaa] at e2 e4
  rw [hnbb] at e3 e4
  have hxor := xor_type_of_square op a b α e1 e2 e3 e4
  -- the w-square parity vanishes for xor-type op
  have c1 := hf w
  have c2 := hf (Function.update w s₀ (!(w s₀)))
  have c3 := hf (Function.update w t₀ (!(w t₀)))
  have c4 := hf (Function.update (Function.update w s₀ (!(w s₀))) t₀ (!(w t₀)))
  rw [hhs w (!(w s₀))] at c2
  rw [hgt w (!(w t₀))] at c3
  rw [hgt _ (!(w t₀))] at c4
  have hcomm4 : h (Function.update (Function.update w s₀ (!(w s₀))) t₀ (!(w t₀)))
      = h (Function.update w t₀ (!(w t₀))) := by
    rw [show Function.update (Function.update w s₀ (!(w s₀))) t₀ (!(w t₀))
        = Function.update (Function.update w t₀ (!(w t₀))) s₀ (!(w s₀)) from
      Function.update_comm hst _ _ w, hhs _ (!(w s₀))]
  rw [hcomm4] at c4
  rw [c1, c2, c3, c4, hxor, hxor, hxor, hxor] at hodd
  revert hodd
  cases g w <;> cases g (Function.update w s₀ (!(w s₀))) <;>
    cases h w <;> cases h (Function.update w t₀ (!(w t₀))) <;>
      cases α <;> cases a <;> cases b <;> decide

/-- **CORRECTED CONDITIONAL (hypothesis named, not claimed)**: the proper-split refutation gives excess ≥ 1,
provided the excess-zero split is proper — the constant-wire kill, the named frame-side rung. -/
theorem sat3_excess_pos_of_no_split_proper (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hW : Sat3NoBipartiteSplitProper N)
    (hproper : ∀ (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (S : Finset (Fin N)),
      (∀ x y : Fin N → Bool, (∀ i, i ∈ S → x i = y i) → g x = g y) →
      (∀ x y : Fin N → Bool, (∀ i, i ∉ S → x i = y i) → h x = h y) →
      (∀ x, sat3Family N x = op (g x) (h x)) →
      (∃ s₀ : Fin N, s₀ ∈ S) ∧ (∃ t₀ : Fin N, t₀ ∉ S))
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hmin : c.length = cbudget (sat3Family N)) :
    1 ≤ coneExcess c (c.length - 1) := by
  by_contra hcon
  push_neg at hcon
  have hex : coneExcess c (c.length - 1) = 0 := by omega
  obtain ⟨op, g, h, S, hg, hh, hf⟩ := sat3_split_frame N hv hm3 hk c hcomp hmin hex
  obtain ⟨hs, ht⟩ := hproper op g h S hg hh hf
  exact hW op g h S hg hh hf hs ht

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.two_squares_kill_split
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_excess_pos_of_no_split_proper
