import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0OracleRestrictionRealization
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0OracleControl

/-!
# The disjoint-fragment `x`-level speedup: an exact reduction to the `k`-variable control

For an `AC⁰` control `C` over `k` `MOD`-gate oracles, `…ACC0OracleControl` already gives an `x`-level searchable bound
(`oracle_control_over_mod_searchable`, `< 2^n` when `2^k < 2^n`) — for *any* gates.  This file proves the stronger
disjoint-specific statement: when the gate supports are **pairwise disjoint** and each gate can output both values, the
gate-output vector `x ↦ (g₁(x),…,g_k(x))` is **surjective** onto `{0,1}^k` (disjoint blocks ⇒ independently
realizable, via `realizable_of_disjoint`).  Hence the `n`-variable circuit's satisfiability collapses **exactly** to the
`k`-variable control's satisfiability:

```
Satisfiable (x ↦ C(g₁(x),…,g_k(x)))  ↔  Satisfiable C       (over Fin k → Bool)
```

so the `n`-variable problem carries no more content than the `k`-variable one — a genuine `x`-level speedup
(`2^k < 2^n`).  This is exactly what the no-go `position_restriction_not_always_realizable` breaks for *overlapping*
gates: there the output vector is **not** surjective (constraints conflict), so the reduction fails — which is why the
fragment restriction (disjointness) is essential, not cosmetic.

## What is proved (clean axioms, no `sorry`)

* `gate_vector_realizable` — disjoint supports + per-gate both-achievable ⇒ every output vector `y` is realized by some
  input `x` (`∀ y, ∃ x, ∀ j, (gⱼ).eval x = y j`).
* `disjoint_fragment_sat_iff` — the exact reduction `Satisfiable (x ↦ C(g(x))) ↔ Satisfiable C`.
* `disjoint_fragment_speedup` — the `x`-level speedup: `f`-SAT decided by searching `Fin k → Bool` (card `2^k < 2^n`).

## Honest scope

Disjointness is load-bearing: it makes the gate outputs *independently* realizable, which is exactly what fails for
overlapping gates (the no-go).  The reduction is exact, and the resulting `k`-variable search is `2^k` (the disjoint
case is the *worst* case for the output-cell count — the image is the full `2^k` — so this is tight, not improvable by
the observer alone).  The switching refinement (`< 2^s`) would need the control `C` itself to be shallow, which is not
generic.  Still the cell/observer model; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0DisjointFragmentSpeedup

open scoped Classical
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0OracleControl
open PallLean.Paper93.DeepMath.PathB.ACC0OracleRestrictionRealization

variable {n k : ℕ}

/-- **The gate-output vector is surjective on disjoint supports (proved): every `y : Fin k → Bool` is realized by some
input `x`** (each gate set independently on its disjoint block via `realizable_of_disjoint`). -/
theorem gate_vector_realizable (gate : Fin k → ModGate n)
    (hdisj : ∀ j j', j ≠ j' → Disjoint (gate j).support (gate j').support)
    (hach : ∀ j b, ∃ a : Fin n → Bool, (gate j).eval a = b) (y : Fin k → Bool) :
    ∃ x : Fin n → Bool, ∀ j, (gate j).eval x = y j := by
  obtain ⟨σ, hσ⟩ := realizable_of_disjoint (fun j => some (y j)) gate hdisj
    (fun j b _ => hach j b)
  have hext : Extends (fun i => (σ i).getD false) σ := by intro i v hv; simp [hv]
  exact ⟨fun i => (σ i).getD false, fun j => hσ j (y j) rfl _ hext⟩

/-- **Exact reduction (proved): on disjoint supports with both-achievable gates, the `n`-variable circuit is
satisfiable iff the `k`-variable control is.** -/
theorem disjoint_fragment_sat_iff (C : OracleControl k) (gate : Fin k → ModGate n)
    (hdisj : ∀ j j', j ≠ j' → Disjoint (gate j).support (gate j').support)
    (hach : ∀ j b, ∃ a : Fin n → Bool, (gate j).eval a = b) :
    Satisfiable (fun x => controlEval C (fun j => (gate j).eval x)) ↔ Satisfiable (controlEval C) := by
  unfold Satisfiable
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨fun j => (gate j).eval x, hx⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, hgx⟩ := gate_vector_realizable gate hdisj hach y
    refine ⟨x, ?_⟩
    show controlEval C (fun j => (gate j).eval x) = true
    rw [funext hgx]; exact hy

/-- **The disjoint-fragment `x`-level speedup (proved): `f`-SAT over `Fin n` is decided by searching `Fin k → Bool`,
whose `2^k` elements are `< 2^n`.** -/
theorem disjoint_fragment_speedup (C : OracleControl k) (gate : Fin k → ModGate n)
    (hdisj : ∀ j j', j ≠ j' → Disjoint (gate j).support (gate j').support)
    (hach : ∀ j b, ∃ a : Fin n → Bool, (gate j).eval a = b) (hkn : 2 ^ k < 2 ^ n) :
    (Satisfiable (fun x => controlEval C (fun j => (gate j).eval x)) ↔
        ∃ y ∈ (Finset.univ : Finset (Fin k → Bool)), controlEval C y = true)
      ∧ (Finset.univ : Finset (Fin k → Bool)).card < 2 ^ n := by
  refine ⟨?_, ?_⟩
  · rw [disjoint_fragment_sat_iff C gate hdisj hach]
    unfold Satisfiable
    simp only [Finset.mem_univ, true_and]
  · simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    exact hkn

end PallLean.Paper93.DeepMath.PathB.ACC0DisjointFragmentSpeedup

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DisjointFragmentSpeedup.gate_vector_realizable
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DisjointFragmentSpeedup.disjoint_fragment_sat_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DisjointFragmentSpeedup.disjoint_fragment_speedup
