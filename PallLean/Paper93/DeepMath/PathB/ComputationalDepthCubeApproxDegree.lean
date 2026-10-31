import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCubeSymNoGo

/-!
# The approximation / low-degree measure: the tool the `SYM`/`ACC⁰` no-go called for

The no-go (`…CubeSymNoGo`) proved `globalCubeRank` cannot separate from `ACC⁰` — because it is *large* on the `MOD` gates
that live *inside* `ACC⁰`.  The fix it pointed to is Razborov–Smolensky: a measure that is **bounded on the easy class**,
which forces **approximation** — agreement with a *low-degree* polynomial on a large set of inputs.  This file builds that
cube-native measure and proves its two defining properties: it is *bounded* (few low-degree functions), and it therefore
*forces the existence of hard functions* (the RS counting core).

  `cubeMonomial S x = ∏_{i∈S} [xᵢ]` — a multilinear monomial; `lowDegSubsets d` = subsets of size `≤ d`.
  `lowDegSpan d = span {cubeMonomial S : |S| ≤ d}` — the degree-`≤ d` cube-polynomials.
  **`finrank_lowDegSpan_le`** — `finrank (lowDegSpan d) ≤ (lowDegSubsets d).card` ( `= ∑_{k≤d} C(n,k)` ): the measure is
        *bounded* — the RS "few low-degree polynomials" fact.  This is exactly what `globalCubeRank` lacked.
  `LowApproxDeg d G f` — `f` agrees with some degree-`≤ d` polynomial on the input set `G` (large `G` = good approximation).
  **`exists_not_lowApproxDeg`** — if `(lowDegSubsets d).card < |G|` then **some function has no degree-`≤ d` approximation
        on `G`**: low-degree functions restricted to `G` span a proper subspace (dimension `≤ card < |G|`), so a
        counting/dimension argument produces a hard function.  This is the Razborov–Smolensky dimension argument.

## Honest scope — what this is, and what still needs the repo's RS core

This is the *framework* the no-go demanded: a bounded, approximation-based measure, with the RS counting proved (hard
functions exist).  The **specific** `ACC⁰[p]` separation needs the two quantitative RS ingredients, which are **not**
re-derived here:
* **easy side** — every `ACC⁰[p]` circuit has a *probabilistic* degree `polylog(n)` (so `LowApproxDeg` holds with small
  `d` and large `G`).  The repo's polynomial-method layer carries this (`…NFrameSeparation`, `NFrameComplexity`).
* **hard side** — `MOD_q` (`q` coprime to `p`) has approximate degree `Ω(√n)` over `F_p`.  The repo already proves the
  matching exact bound (`nframeComplexity_omegaFn_univ_ge`, `parity_function_lower_bound`); those are cited, not rebuilt.

So this file supplies the missing *conceptual* piece the cube arc reached for — the bounded approximation measure — and
locates the remaining work in the repo's existing RS bounds.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

variable {n : ℕ} {F : Type*} [Field F]

/-- A multilinear monomial as a cube function: `∏_{i∈S} [xᵢ]`. -/
def cubeMonomial (S : Finset (Fin n)) : (Fin n → Bool) → F :=
  fun x => ∏ i ∈ S, (if x i then (1 : F) else 0)

/-- The subsets of size `≤ d` — indexing the degree-`≤ d` multilinear monomials. -/
def lowDegSubsets (d : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.powerset.filter (fun S => S.card ≤ d)

/-- The degree-`≤ d` cube-polynomial space. -/
noncomputable def lowDegSpan (d : ℕ) : Submodule F ((Fin n → Bool) → F) :=
  Submodule.span F (Set.range
    (fun S : {S : Finset (Fin n) // S ∈ lowDegSubsets (n := n) d} => cubeMonomial (F := F) S.val))

/-- **The measure is bounded (proved)**: `finrank (lowDegSpan d) ≤ (lowDegSubsets d).card` — the RS "few low-degree
polynomials" fact, exactly the boundedness `globalCubeRank` lacked. -/
theorem finrank_lowDegSpan_le (d : ℕ) :
    Module.finrank F (lowDegSpan (n := n) (F := F) d) ≤ (lowDegSubsets (n := n) d).card := by
  rw [lowDegSpan, ← Finsupp.range_linearCombination]
  refine le_trans (LinearMap.finrank_range_le _) (le_of_eq ?_)
  rw [Module.finrank_finsupp_self, Fintype.card_coe]

/-- `f` has low approximate degree `d` on the input set `G`: it agrees with some degree-`≤ d` polynomial on all of `G`
(large `G` = good approximation). -/
def LowApproxDeg (d : ℕ) (G : Finset (Fin n → Bool)) (f : (Fin n → Bool) → F) : Prop :=
  ∃ g ∈ lowDegSpan (F := F) d, ∀ x ∈ G, f x = g x

/-- Restriction of a cube function to the input set `G`. -/
def restrictToFinset (G : Finset (Fin n → Bool)) :
    ((Fin n → Bool) → F) →ₗ[F] (↥G → F) :=
  LinearMap.funLeft F F (Subtype.val : ↥G → (Fin n → Bool))

/-- **The RS dimension argument (proved)**: if there are fewer low-degree monomials than inputs in `G`, then some function
has *no* degree-`≤ d` approximation on `G`.  Low-degree functions restricted to `G` span a subspace of dimension
`≤ (lowDegSubsets d).card < |G| = dim(G → F)`, so it is proper — a counting/dimension argument yields a hard function. -/
theorem exists_not_lowApproxDeg (d : ℕ) (G : Finset (Fin n → Bool))
    (hcard : (lowDegSubsets (n := n) d).card < G.card) :
    ∃ f : (Fin n → Bool) → F, ¬ LowApproxDeg (F := F) d G f := by
  classical
  set img := (lowDegSpan (F := F) d).map (restrictToFinset G) with himg
  -- the restricted low-degree functions have dimension < |G|
  have hrank : Module.finrank F img < Module.finrank F (↥G → F) := by
    have h1 : Module.finrank F img ≤ (lowDegSubsets (n := n) d).card :=
      le_trans (Submodule.finrank_map_le _ _) (finrank_lowDegSpan_le d)
    have h2 : Module.finrank F (↥G → F) = G.card := by
      rw [Module.finrank_pi, Fintype.card_coe]
    omega
  -- hence `img` is not everything; pick `v` outside it
  have hne : img ≠ ⊤ := by
    intro h
    rw [h, finrank_top] at hrank
    exact lt_irrefl _ hrank
  obtain ⟨v, hv⟩ : ∃ v : ↥G → F, v ∉ img := by
    by_contra hcon
    push_neg at hcon
    exact hne (Submodule.eq_top_iff'.mpr hcon)
  -- extend `v` to the whole cube; its restriction is exactly `v`, so it has no low-degree approximation on `G`
  refine ⟨fun x => if h : x ∈ G then v ⟨x, h⟩ else 0, ?_⟩
  rintro ⟨g, hg, hagree⟩
  apply hv
  have hrestr : restrictToFinset G (fun x => if h : x ∈ G then v ⟨x, h⟩ else 0) = v := by
    funext i
    simp only [restrictToFinset, LinearMap.funLeft_apply, dif_pos i.2, Subtype.coe_eta]
  rw [← hrestr]
  have : restrictToFinset G (fun x => if h : x ∈ G then v ⟨x, h⟩ else 0)
      = restrictToFinset G g := by
    funext i
    simp only [restrictToFinset, LinearMap.funLeft_apply]
    exact hagree i.val i.2
  rw [this]
  exact Submodule.mem_map_of_mem hg

end PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.finrank_lowDegSpan_le
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.exists_not_lowApproxDeg
