import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCubeModQSeparation
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PolyToSymAnd

/-!
# The `SYM`/`ACC⁰` no-go: `globalCubeRank` cannot separate from `SYM∘∑∏`

The `MOD_q` rung discharged `GlobalRobust` for `MOD_q` (`globalCubeRank ≥ n`) and firing the *plain* `∑∏` separation.
The obvious next move is to lift the criterion to `SYM∘∑∏` (= `ACC⁰`, Beigel–Tarui).  This file proves that move is
**impossible for `globalCubeRank`** — a real no-go, not a wall to be pushed on.

The reason is structural: `MOD_q` **is itself** a `SYM∘∑∏` (a symmetric top gate `[·≡0 mod q]` over the trivial `∑∏` of
single-variable `AND`s), because `ACC⁰ ⊇ MOD_q`.  But `MOD_q` *also* has `globalCubeRank ≥ n`.  So `SYM∘∑∏` **contains**
globally-robust functions, and no `globalCubeRank`-threshold criterion can certify "`f ∉ SYM∘∑∏`".

  `symCountFn h S x = h (∑ⱼ [monoAND (Sⱼ) x])` — the general `SYM∘∑∏` cube function (`h` = symmetric top gate on the count
        of accepting `AND`s); `IsSymCount f` — membership in the `SYM∘∑∏` class (`= ACC⁰` up to the top gate).
  `monoAND_singleton`, `modQFn_eq_symCountFn`, `modQFn_isSymCount` — `MOD_q ∈ SYM∘∑∏` (singleton gates, `h = [·≡0 mod q]`).
  **`globalRank_cannot_certify_not_symCount`** — for every `bound < n` there is a `SYM∘∑∏` function (`MOD_q`) with
        `globalCubeRank > bound`.  Hence:
  **`no_globalRank_criterion_for_symCount`** — the criterion "`high globalCubeRank ⟹ ¬ IsSymCount`" is **false**.

## Why this is the right (honest) conclusion

Exact rank measures are large on `MOD` gates, which already live in `ACC⁰`.  A measure that separates from `ACC⁰` must be
*bounded on all of `ACC⁰`* — which forces **approximation** (low-degree polynomials that only ε-agree), the
Razborov–Smolensky route, not exact cube-derivative rank.  This no-go is the cube-native formalisation of exactly that
lesson: it explains, with a proof, why the exact-rank arc tops out at plain `∑∏` and cannot reach `ACC⁰`.  The genuine
`MOD_q ∉ ACC⁰` separation needs the approximation/composite-field machinery (the `F_2`/`F_3` wall), which is **not** here
and is `P≠NP`-adjacent.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd (monoAND)

variable {n : ℕ} {F : Type*} [Field F]

/-- The general `SYM∘∑∏` cube function: a symmetric top gate `h` on the count of accepting `AND` gates. -/
def symCountFn {m : ℕ} (h : ℕ → F) (S : Fin m → Finset (Fin n)) : (Fin n → Bool) → F :=
  fun x => h (∑ j, if monoAND (S j) x then 1 else 0)

/-- Membership in the `SYM∘∑∏` class (`= ACC⁰` via Beigel–Tarui, up to the symmetric top gate). -/
def IsSymCount (f : (Fin n → Bool) → F) : Prop :=
  ∃ (m : ℕ) (h : ℕ → F) (S : Fin m → Finset (Fin n)), f = symCountFn h S

/-- The single-variable `AND` gates. -/
def singletonGates : Fin n → Finset (Fin n) := fun i => {i}

/-- A singleton `AND` gate is just the variable. -/
theorem monoAND_singleton (i : Fin n) (x : Fin n → Bool) :
    monoAND ({i} : Finset (Fin n)) x = x i := by
  cases h : x i <;> simp [monoAND, h]

/-- **`MOD_q` is a `SYM∘∑∏` (proved)**: the symmetric top gate `[·≡0 mod q]` over the trivial `∑∏` of single-variable
`AND`s. -/
theorem modQFn_eq_symCountFn {q : ℕ} :
    (modQFn q : (Fin n → Bool) → F)
      = symCountFn (fun c => if c % q = 0 then (1 : F) else 0) singletonGates := by
  funext x
  have hc : cubeCount x = ∑ j, if monoAND (singletonGates j) x then (1 : ℕ) else 0 := by
    rw [cubeCount]
    exact Finset.sum_congr rfl (fun j _ => by rw [singletonGates, monoAND_singleton])
  simp only [modQFn, symCountFn, hc]

/-- **`MOD_q ∈ SYM∘∑∏` (proved)**. -/
theorem modQFn_isSymCount {q : ℕ} : IsSymCount (modQFn q : (Fin n → Bool) → F) :=
  ⟨n, (fun c => if c % q = 0 then (1 : F) else 0), singletonGates, modQFn_eq_symCountFn⟩

/-- **The no-go (proved)**: for every threshold `bound < n` there is a `SYM∘∑∏` function — namely `MOD_q` — with
`globalCubeRank > bound`.  So no `globalCubeRank`-threshold can certify non-membership in `SYM∘∑∏`. -/
theorem globalRank_cannot_certify_not_symCount {q : ℕ} (hq : 2 ≤ q) (h2 : (2 : F) ≠ 0)
    (bound : ℕ) (hb : bound < n) :
    ∃ f : (Fin n → Bool) → F, IsSymCount f ∧ bound < globalCubeRank dictatorFamily 1 f :=
  ⟨modQFn q, modQFn_isSymCount, lt_of_lt_of_le hb (n_le_globalCubeRank_modQFn hq h2)⟩

/-- **The criterion is impossible (proved)**: "`high globalCubeRank ⟹ ¬ IsSymCount`" is **false** — `MOD_q` has high
global rank yet *is* a `SYM∘∑∏`.  `globalCubeRank` cannot separate from `ACC⁰`; a bounded-on-`ACC⁰` measure (approximation,
Razborov–Smolensky) is required. -/
theorem no_globalRank_criterion_for_symCount {q : ℕ} (hq : 2 ≤ q) (h2 : (2 : F) ≠ 0) (hn : 1 ≤ n) :
    ¬ ∀ f : (Fin n → Bool) → F,
        (n - 1 < globalCubeRank dictatorFamily 1 f) → ¬ IsSymCount f := by
  intro hcrit
  have hrank : n - 1 < globalCubeRank dictatorFamily 1 (modQFn q : (Fin n → Bool) → F) := by
    have := n_le_globalCubeRank_modQFn (F := F) (n := n) hq h2
    omega
  exact hcrit (modQFn q) hrank modQFn_isSymCount

end PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP

#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.modQFn_isSymCount
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundarySPDP.no_globalRank_criterion_for_symCount
