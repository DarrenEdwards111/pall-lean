import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModGateComposition

/-!
# Cross-layer MOD composition — into the blow-up (PROVED)

The first step into the Beigel–Tarui blow-up.  `ACC0ModGateComposition` closed the `MOD` gate over a
**shared** bottom layer (one count, no blow-up).  Real ACC⁰ gates read **distinct** bottom layers;
composing a `MOD` gate over them raises the count dimension by one per distinct layer.  This is the
honest cost of cross-layer composition, made precise.

* **Binary** (`hasBinarySymRep_modGate2`): a `MOD_m` gate over two subcircuits on two layers is a
  *joint two-count* function — mirrors the existing `hasBinarySymRep_and/or`.
* **General** (`hasMultiSymRep_modGate_crossLayer`): a `MOD_m` gate over `k` subcircuits on `k` distinct
  layers is a joint **`k`-count** function (`HasMultiSymRep`).  The count dimension is exactly the
  number of distinct bottom layers — the SAT search is over `≤ (n+1)^k` count-tuples.

So composition is still **exact**, but the cost is explicit: each distinct bottom layer adds one count
coordinate.  Iterated to constant depth with distinct layers, this `k`-count tuple is what the
Beigel–Tarui construction must collapse to *one* count (CRT-decoded) at *quasipolynomial* size — the
exact-vs-quasipoly wall of `ACC0ExactCompose`.

## What is proved (clean axioms, no `sorry`)

* `hasBinarySymRep_modGate2` — cross-layer `MOD` of two subcircuits is jointly two-count symmetric.
* `HasMultiSymRep` / `hasMultiSymRep_modGate_crossLayer` — cross-layer `MOD` of `k` subcircuits is
  jointly `k`-count symmetric (count dimension = #distinct layers).
* `hasMultiSymRep_of_hasSymAndRep` — a single-layer rep is trivially a 1-count multi-rep (the base of
  the dimension ladder).

## Honest scope

Exact cross-layer `MOD` composition, with the count dimension growing one-per-layer — the precise,
honest blow-up.  Collapsing the `k`-count tuple back to a single quasipoly-size count is the
Beigel–Tarui exact-vs-quasipoly wall (`ACC0ExactCompose`), still open.  Nothing here is `NEXP ⊄ ACC⁰`
or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModGateCrossLayer

open PallLean.Paper93.DeepMath.PathB.ACC0SymAndComposition
open PallLean.Paper93.DeepMath.PathB.ACC0Mod6SymAndDepth2 (satCount)

variable {n : ℕ}

/-- **Cross-layer binary `MOD` (proved): two subcircuits, two layers, joint two-count.**  A `MOD_m`
gate at residue `r` over two `SYM∘AND` subcircuits `F, G` (each on its own bottom layer) is a joint
function of the two counts. -/
theorem hasBinarySymRep_modGate2 {F G : (Fin n → Bool) → Bool} {m r : ℕ}
    (hF : HasSymAndRep F) (hG : HasSymAndRep G) :
    HasBinarySymRep (fun x => decide (((F x).toNat + (G x).toNat) % m = r)) := by
  obtain ⟨tF, sF, symF, hFx⟩ := hF
  obtain ⟨tG, sG, symG, hGx⟩ := hG
  exact ⟨tF, tG, sF, sG,
    fun a b => decide (((symF a).toNat + (symG b).toNat) % m = r),
    fun x => by simp only [hFx, hGx]⟩

/-- **`F` has a `k`-count joint representation**: it is a joint function of the satisfied-`AND` counts
over `k` distinct bottom layers. -/
def HasMultiSymRep (F : (Fin n → Bool) → Bool) : Prop :=
  ∃ (k : ℕ) (t : Fin k → ℕ) (supp : (i : Fin k) → Fin (t i) → Finset (Fin n))
    (j : ((i : Fin k) → ℕ) → Bool),
    ∀ x, F x = j (fun i => satCount (supp i) x)

/-- **A single-layer rep is a 1-count multi-rep (proved): the base of the dimension ladder.** -/
theorem hasMultiSymRep_of_hasSymAndRep {F : (Fin n → Bool) → Bool} (h : HasSymAndRep F) :
    HasMultiSymRep F := by
  obtain ⟨t, supp, sym, hF⟩ := h
  exact ⟨1, fun _ => t, fun _ => supp, fun c => sym (c 0), fun x => by simp only [hF]⟩

/-- **Cross-layer `MOD` of `k` subcircuits is jointly `k`-count symmetric (proved).**  A `MOD_m` gate
at residue `r` over `k` subcircuits, where subcircuit `i` reads its own bottom layer `supp i` (each
`g i = sym i ∘ satCount (supp i)`), is a joint function of the `k` counts.  The count dimension is the
number of distinct bottom layers — the explicit cross-layer blow-up. -/
theorem hasMultiSymRep_modGate_crossLayer {k m r : ℕ} {t : Fin k → ℕ}
    {supp : (i : Fin k) → Fin (t i) → Finset (Fin n)}
    {g : Fin k → (Fin n → Bool) → Bool} {sym : Fin k → ℕ → Bool}
    (hg : ∀ i x, g i x = sym i (satCount (supp i) x)) :
    HasMultiSymRep (fun x => decide ((∑ i, (g i x).toNat) % m = r)) :=
  ⟨k, t, supp, fun c => decide ((∑ i, (sym i (c i)).toNat) % m = r),
    fun x => by simp only [hg]⟩

/-!
**Cross-layer MOD composition proved.**  Binary (two-count) and general (`k`-count, dimension =
#distinct layers) — exact, with the count dimension rising one per distinct bottom layer.  Collapsing
the `k`-count tuple to a single quasipoly-size count (the Beigel–Tarui CRT construction) is the
exact-vs-quasipoly wall (`ACC0ExactCompose`), still open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ModGateCrossLayer

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModGateCrossLayer.hasBinarySymRep_modGate2
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModGateCrossLayer.hasMultiSymRep_modGate_crossLayer
