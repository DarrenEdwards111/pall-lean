import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResLinLiftedTseitinInterface

/-!
# The depth-reduction frontier: both hard targets are the open bound (and what comes free)

`ResLinLiftedTseitinInterface` proved `unrestricted_iff_no_deep_small`: eliminating deep-small
refutations *is* the unrestricted `Res(⊕)` size lower bound (target 2 ≡ the open problem).  This
file does two things.

**#1 — Target 1 is also a route to the open bound.**  We formalize `HasDepthReduction` (every
refutation has a shallow equivalent, up to a size blowup) and prove that size-preserving depth
reduction plus the bounded-depth lower bound yields the full unrestricted bound
(`unrestricted_of_depthReduction`).  So proving depth reduction is *at least as hard* as the open
problem — it is not a shortcut.  With a monotone size blowup the floor still transfers
(`depthReduction_excludes_small`), so even realistic (e.g. polynomial) blowups keep the route intact.

**#2 — What the bounded-depth bound already gives for free, unconditionally.**  Because dependency
depth never exceeds dag size (`depth_le_size` — parents are backward, each rule adds one level), the
bounded-depth lower bound forces *every* refutation to have size at least
`min (sizeFloor m) (depthCap m + 1)`, with **no** depth restriction and **no** extra hypothesis
(`unconditional_size_lb_of_boundedDepth`).  In the TR25-106 regime (`depthCap ∼ N^{2-ε}`,
`sizeFloor ∼ exp(N^ε)`) this is exactly `depthCap m + 1`: an unconditional but only *polynomial*
unrestricted lower bound (`unconditional_size_lb_eq_depthCap`).  Closing the gap from this polynomial
bound up to the exponential `sizeFloor` is precisely the deep-small elimination that
`unrestricted_iff_no_deep_small` shows is the open problem.

This is honest: nothing here proves the exponential unrestricted bound.  It machine-checks that both
proposed targets are the open problem, and extracts the (polynomial) unrestricted content that comes
for free.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  This file proves no unrestricted `Res(⊕)` size bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.ResLinParity

/-! ## Dependency depth never exceeds dag size -/

/-- Levels never exceed the line index: parent pointers are backward and each rule adds one. -/
theorem level_le {n : ℕ} {Γ : Finset (Clause n)} (P : DAGRefutation n Γ) :
    ∀ i, i < P.steps.length → P.level i ≤ i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hv := P.valid i hi
    have hsi : P.steps[i]? = some (P.steps[i]) := List.getElem?_eq_getElem hi
    unfold ValidAt at hv
    rw [hsi] at hv
    dsimp only at hv
    cases hw : (P.steps[i]).why with
    | premise => rw [hw] at hv; have := hv.2; omega
    | boolean v => rw [hw] at hv; have := hv.2; omega
    | weaken p e =>
        rw [hw] at hv; obtain ⟨hpi, _, _, _, hlvl⟩ := hv
        have := ih p hpi (by omega); omega
    | simplify p b =>
        rw [hw] at hv; obtain ⟨hpi, _, _, _, _, hlvl⟩ := hv
        have := ih p hpi (by omega); omega
    | linearResolve p q e f =>
        rw [hw] at hv; obtain ⟨hpi, hqi, _, _, _, _, _, hlvl⟩ := hv
        have := ih p hpi (by omega); have := ih q hqi (by omega); omega

/-- Dependency depth is bounded by dag size. -/
theorem depth_le_size {n : ℕ} {Γ : Finset (Clause n)} (P : DAGRefutation n Γ) :
    P.depth ≤ P.size := by
  have hpos : 0 < P.steps.length := by simpa [DAGRefutation.size] using P.size_pos
  have hl := level_le P (P.steps.length - 1) (by omega)
  unfold DAGRefutation.depth DAGRefutation.size
  omega

/-! ## #1 — Depth reduction is a route to (hence at least as hard as) the open bound -/

/-- Depth reduction: every refutation has a shallow (depth `≤ depthCap`) equivalent, at size blowup
`blow`. -/
def HasDepthReduction (F : LiftedTseitinFamily) (depthCap blow : ℕ → ℕ) : Prop :=
  ∀ m (P : FamilyRefutation F m),
    ∃ Q : FamilyRefutation F m, Q.depth ≤ depthCap m ∧ Q.size ≤ blow P.size

/-- **Target 1 ⟹ the open bound.**  Size-preserving depth reduction plus the bounded-depth lower
bound yields the full unrestricted lower bound. -/
theorem unrestricted_of_depthReduction
    {F : LiftedTseitinFamily} {depthCap sizeFloor : ℕ → ℕ}
    (hdr : HasDepthReduction F depthCap (fun n => n))
    (hbound : HasDepthSizeLowerBound F depthCap sizeFloor) :
    HasUnrestrictedSizeLowerBound F sizeFloor := by
  intro m P
  obtain ⟨Q, hQd, hQs⟩ := hdr m P
  exact le_trans (hbound m Q hQd) hQs

/-- With a size blowup, the bounded-depth floor transfers to `sizeFloor m ≤ blow (P.size)`. -/
theorem depthReduction_blown_bound
    {F : LiftedTseitinFamily} {depthCap sizeFloor blow : ℕ → ℕ}
    (hdr : HasDepthReduction F depthCap blow)
    (hbound : HasDepthSizeLowerBound F depthCap sizeFloor)
    (m : ℕ) (P : FamilyRefutation F m) :
    sizeFloor m ≤ blow P.size := by
  obtain ⟨Q, hQd, hQs⟩ := hdr m P
  exact le_trans (hbound m Q hQd) hQs

/-- Monotone-blowup form: a size `S` too small for the blowup to reach the floor is impossible, so a
polynomial blowup against an exponential floor still yields a superpolynomial bound. -/
theorem depthReduction_excludes_small
    {F : LiftedTseitinFamily} {depthCap sizeFloor blow : ℕ → ℕ}
    (hmono : Monotone blow)
    (hdr : HasDepthReduction F depthCap blow)
    (hbound : HasDepthSizeLowerBound F depthCap sizeFloor)
    {m S : ℕ} (hgap : blow S < sizeFloor m)
    (P : FamilyRefutation F m) : S < P.size := by
  by_contra h
  push_neg at h
  have hb := depthReduction_blown_bound hdr hbound m P
  have := hmono h
  omega

/-! ## #2 — The free unconditional (polynomial) unrestricted bound -/

/-- **The free unconditional bound.**  Since dependency depth never exceeds dag size, the
bounded-depth lower bound forces *every* refutation to have size at least
`min (sizeFloor m) (depthCap m + 1)` — no depth restriction, no extra hypothesis. -/
theorem unconditional_size_lb_of_boundedDepth
    {F : LiftedTseitinFamily} {depthCap sizeFloor : ℕ → ℕ}
    (hbound : HasDepthSizeLowerBound F depthCap sizeFloor)
    (m : ℕ) (P : FamilyRefutation F m) :
    min (sizeFloor m) (depthCap m + 1) ≤ P.size := by
  rcases Nat.lt_or_ge (depthCap m) P.depth with hd | hd
  · have hds := depth_le_size P; omega
  · have := hbound m P hd; omega

/-- In the TR25-106 regime (`depthCap m + 1 ≤ sizeFloor m`) the free bound is exactly `depthCap m +
1`: an unconditional but only *polynomial* unrestricted lower bound.  Lifting it to the exponential
`sizeFloor` is the open deep-small elimination of `unrestricted_iff_no_deep_small`. -/
theorem unconditional_size_lb_eq_depthCap
    {F : LiftedTseitinFamily} {depthCap sizeFloor : ℕ → ℕ}
    (hbound : HasDepthSizeLowerBound F depthCap sizeFloor)
    (m : ℕ) (hreg : depthCap m + 1 ≤ sizeFloor m)
    (P : FamilyRefutation F m) :
    depthCap m + 1 ≤ P.size := by
  have := unconditional_size_lb_of_boundedDepth hbound m P
  omega

#print axioms unrestricted_of_depthReduction
#print axioms depth_le_size
#print axioms unconditional_size_lb_of_boundedDepth

end PallLean.Paper93.DeepMath.PathB.ResLinParity
