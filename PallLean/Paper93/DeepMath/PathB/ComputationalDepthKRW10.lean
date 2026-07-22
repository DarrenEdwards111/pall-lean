import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW9

/-!
# KRW brick 10: the separation socket is TIGHT (an honesty audit)

KRW9 proved one direction — an explicit-in-`P` depth-hard family gives `P ⊄ NC¹`.
This brick proves the CONVERSE, so the named socket is *equivalent* to the
separation: it is not a hidden strengthening.

* **`PowNC1 L`** — the `NC¹`-depth condition restricted to power-of-two lengths
  (`∃ c, ∀ k, dmdepth (langSlice L (2^k)) ≤ c·(k+1)`); **`nc1_imp_powNC1`** —
  `NC1Depth L → PowNC1 L` (so `¬PowNC1 ⟹ ¬NC1Depth`, connecting to KRW9);
* **`krw_socket_iff_separation` (proved)** —
  `(∃ F L, InP L ∧ Realizes L F ∧ ¬DepthLogBounded F) ↔ (∃ L, InP L ∧ ¬PowNC1 L)`.

So the KRW9 socket is EXACTLY `P ⊄ (power-of-two) NC¹-depth` — necessary and
sufficient, no smuggled-in extra strength.  This audits the reduction; it does NOT
fill the socket (that is the open problem — an explicit `ω(log n)`-depth family in
`P`).  Nothing here is `P ≠ NP`, and nothing closes KRW.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

open scoped Classical

/-- The `NC¹`-depth condition on power-of-two lengths. -/
def PowNC1 (L : List Bool → Bool) : Prop :=
  ∃ c, ∀ k, dmdepth (langSlice L (2 ^ k)) ≤ c * (k + 1)

/-- `NC1Depth` (all lengths) implies `PowNC1` (powers of two). -/
theorem nc1_imp_powNC1 (L : List Bool → Bool) (h : NC1Depth L) : PowNC1 L := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun k => ?_⟩
  have hb := hc (2 ^ k)
  rwa [Nat.log_pow (by norm_num) k] at hb

/-- **The socket is tight (proved)**: the KRW9 separation socket is EQUIVALENT to
`∃ L ∈ InP, ¬ PowNC1 L` — necessary and sufficient, no hidden strengthening. -/
theorem krw_socket_iff_separation :
    (∃ (F : (k : ℕ) → (Fin (2 ^ k) → Bool) → Bool) (L : List Bool → Bool),
        ComposableMachine.InP L ∧ Realizes L F ∧ ¬ DepthLogBounded F)
      ↔ (∃ L, ComposableMachine.InP L ∧ ¬ PowNC1 L) := by
  constructor
  · rintro ⟨F, L, hInP, hR, hHard⟩
    refine ⟨L, hInP, fun hPow => hHard ?_⟩
    obtain ⟨c, hc⟩ := hPow
    refine ⟨c, fun k => ?_⟩
    have hs := realizes_slice L F hR k
    have hb := hc k
    rwa [hs] at hb
  · rintro ⟨L, hInP, hHard⟩
    refine ⟨fun k => langSlice L (2 ^ k), L, hInP, fun k x => rfl, fun hDLB => hHard ?_⟩
    obtain ⟨c, hc⟩ := hDLB
    exact ⟨c, hc⟩

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.nc1_imp_powNC1
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.krw_socket_iff_separation
