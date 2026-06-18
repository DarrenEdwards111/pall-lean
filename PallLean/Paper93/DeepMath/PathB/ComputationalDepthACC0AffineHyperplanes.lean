import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0AlgebraicExpansion

/-!
# Affine hyperplane indicators — a genuine non-trivial algebraically-expanding family (proved)

The focused program's next concrete family (beyond the point/dictator gates of entry 257): **affine hyperplane
indicators**.  Over `F_p^{n+1}`, the parallel hyperplanes `{x : ∑ⱼ xⱼ = b}` (the all-ones direction, `b ∈ F_p`)
partition the cube, so each input lies on *exactly one* — giving each gate a **private witness**.  Private witnesses
force the indicators to be linearly independent, i.e. **`AlgExpander`** (full indicator rank, entry 257).

This supplies a genuine non-trivial algebraic-expander family (affine, not just the trivial dictator family), and a
reusable tool (`private_witness_indep`) for proving `AlgExpander` from a combinatorial witness structure.

⚠️ **No crossing.**  This proves the *family is algebraically expanding* (full rank).  The count *lower bound* on it —
that the mod-`q` fire-count of these affine gates needs superpoly resources — is the entry-256/257
`AlgExpanderCountObstruction` socket, Smolensky-strength, **not** proved here.

## What is proved (clean axioms, no `sorry`)

* **`private_witness_indep`** (PROVED) — the reusable tool: if each gate `i` fires on a *private witness* `wit i`
  (`gates i (wit i) = true`, and `gates j (wit i) = false` for `j ≠ i`), then the gate indicators are linearly
  independent over `F` — `AlgExpander`.  (Evaluate the linear dependence at each witness; `Fintype.linearIndependent_iff`
  + `Finset.sum_eq_single`.)
* **`affineHyperplane_algExpander`** (PROVED) — for any injective `targets : Fin s → F_p`, the affine hyperplane family
  `fun i x => decide (∑ⱼ xⱼ = targets i)` over `F_p^{n+1}` is `AlgExpander`: the private witness for gate `i` is the
  point `Pi.single 0 (targets i)` (coordinate-`0` set to `targets i`, rest `0`), which lies on hyperplane `i` only
  (distinct targets).

## Honest scope

This proves a concrete non-trivial *affine* algebraic-expander family (full indicator rank), via the general
private-witness tool.  It does **not** prove the count lower bound on it — that is the Smolensky-strength socket.  Next
families (random low-degree `F_p` polynomials, Reed–Muller) and the restricted lower bound remain.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0AffineHyperplanes

open PallLean.Paper93.DeepMath.PathB.ACC0AlgebraicExpansion

variable {F : Type} [Field F]

/-- **Private witnesses ⇒ `AlgExpander` (PROVED, reusable tool).**  If each gate `i` fires on a private witness `wit i`
that no other gate fires on (`gates i (wit i) = true`, `gates j (wit i) = false` for `j ≠ i`), the gate indicators are
linearly independent over `F`.  Proof: a linear dependence `∑ⱼ cⱼ · gateInd j = 0`, evaluated at `wit i`, collapses to
`c i = 0` (only gate `i` fires there). -/
theorem private_witness_indep {X : Type} {s : ℕ} (gates : Fin s → (X → Bool)) (wit : Fin s → X)
    (hself : ∀ i, gates i (wit i) = true)
    (hother : ∀ i j, j ≠ i → gates j (wit i) = false) :
    AlgExpander (F := F) gates := by
  rw [AlgExpander, Fintype.linearIndependent_iff]
  intro c hc i
  have hev := congrFun hc (wit i)
  simp only [Finset.sum_apply, Pi.smul_apply, gateInd, smul_eq_mul, Pi.zero_apply] at hev
  rw [Finset.sum_eq_single i] at hev
  · simpa [hself i] using hev
  · intro j _ hji; rw [hother i j hji]; simp
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- **Affine hyperplane indicators are `AlgExpander` (PROVED).**  For injective `targets : Fin s → F_p`, the parallel
affine hyperplanes `{x : ∑ⱼ xⱼ = targets i}` over `F_p^{n+1}` have linearly independent indicators: the private witness
for gate `i` is `Pi.single 0 (targets i)` (which has coordinate-sum `targets i`, lying on hyperplane `i` and — by
injectivity of `targets` — on no other).  A genuine non-trivial algebraic-expander family (full rank `s`, entry 257). -/
theorem affineHyperplane_algExpander {p n s : ℕ} (targets : Fin s → ZMod p)
    (hinj : Function.Injective targets) :
    AlgExpander (F := F)
      (fun (i : Fin s) (x : Fin (n + 1) → ZMod p) => decide ((∑ j, x j) = targets i)) := by
  apply private_witness_indep _ (fun i => Pi.single (0 : Fin (n + 1)) (targets i))
  · intro i
    have hsum : (∑ j', Pi.single (0 : Fin (n + 1)) (targets i) j') = targets i := by
      simp [Finset.sum_pi_single]
    simp [hsum]
  · intro i j hji
    have hsum : (∑ j', Pi.single (0 : Fin (n + 1)) (targets i) j') = targets i := by
      simp [Finset.sum_pi_single]
    simp only [hsum, decide_eq_false_iff_not]
    intro h
    exact hji (hinj h).symm

end PallLean.Paper93.DeepMath.PathB.ACC0AffineHyperplanes

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AffineHyperplanes.private_witness_indep
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AffineHyperplanes.affineHyperplane_algExpander
