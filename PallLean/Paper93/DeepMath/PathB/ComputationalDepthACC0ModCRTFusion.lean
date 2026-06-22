import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModGateComposition

/-!
# CRT count-fusion: composite moduli cost no count dimension (PROVED)

The count-collapse, on the modulus axis.  The cross-layer blow-up (`ACC0ModGateCrossLayer`) showed the
count dimension rises one-per-distinct-**layer**.  The natural question for the Beigel–Tarui collapse:
does a *composite modulus* also cost a dimension?  **No** — this brick proves a composite-modulus MOD
gate fuses over the **single shared count** via CRT into prime-modulus gates, staying single-count with
no blow-up.

  `mod_crt_fuse` — for coprime `p, q`: `decide (p*q ∣ s) = decide (p ∣ s) && decide (q ∣ s)` — the
  CRT fusion at the level of the **one** integer count `s`.

  `hasSymAndRep_modpq_sharedLayer` — `MOD_{pq}∘AND` over a layer *is* `SYM∘AND` over the **same** layer
  (single count) and equals `(MOD_p∘AND) ∧ (MOD_q∘AND)` over it.

So the count-dimension cost of the SYM∘AND form is driven **only by distinct bottom layers**, never by
the modulus: every composite `MOD_m` (squarefree, by iterating coprime CRT) reads the single shared
count, decoded by the residue tuple.  This sharpens the wall — the Beigel–Tarui collapse target is the
**layer** count-tuple, not the modulus.

## What is proved (clean axioms, no `sorry`)

* `mod_crt_fuse` — coprime CRT fusion of a single count's divisibility observers.
* `hasSymAndRep_modpq_sharedLayer` — composite-modulus MOD over a shared layer is single-count SYM∘AND,
  = AND of the prime-modulus gates.

## Honest scope

Composite moduli are free (single count, CRT-fused); the genuine blow-up is the cross-**layer**
count-tuple, whose collapse to one quasipoly-size count is the open Beigel–Tarui exact-vs-quasipoly wall
(`ACC0ExactCompose`).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModCRTFusion

open PallLean.Paper93.DeepMath.PathB.ACC0SymAndComposition
open PallLean.Paper93.DeepMath.PathB.ACC0Mod6SymAndDepth2 (satCount)

variable {n : ℕ}

/-- **CRT count-fusion (proved): a single count's `MOD_{pq}` observer is the conjunction of its `MOD_p`
and `MOD_q` observers, for coprime `p, q`.**  One integer count `s` carries both residues; no separate
count is needed for each modulus. -/
theorem mod_crt_fuse {p q : ℕ} (hpq : Nat.Coprime p q) (s : ℕ) :
    decide (p * q ∣ s) = (decide (p ∣ s) && decide (q ∣ s)) := by
  rw [← Bool.decide_and]
  exact decide_eq_decide.mpr (residue_observer_compose_coprime hpq s)

/-- **Composite-modulus MOD over a shared layer is single-count `SYM∘AND` (proved).**  `MOD_{pq}∘AND`
over the bottom layer `supp` is a `SYM∘AND` over the *same* layer (one count) and decomposes as
`(MOD_p∘AND) ∧ (MOD_q∘AND)` over `supp`.  The composite modulus costs **no** count dimension. -/
theorem hasSymAndRep_modpq_sharedLayer {t p q : ℕ} (hpq : Nat.Coprime p q)
    (supp : Fin t → Finset (Fin n)) :
    HasSymAndRep (fun x => decide (p * q ∣ satCount supp x))
      ∧ (∀ x, decide (p * q ∣ satCount supp x)
          = (decide (p ∣ satCount supp x) && decide (q ∣ satCount supp x))) :=
  ⟨⟨t, supp, fun s => decide (p * q ∣ s), fun _ => rfl⟩,
    fun x => mod_crt_fuse hpq (satCount supp x)⟩

/-!
**CRT count-fusion proved.**  A composite (coprime) modulus reads the *single* shared count — fused via
CRT into the prime-modulus observers — so it costs no count dimension; `MOD_{pq}∘AND` over a layer is
single-count `SYM∘AND` equal to the AND of the prime gates.  The genuine SYM∘AND blow-up is therefore
purely the cross-**layer** count-tuple, whose quasipoly-size collapse is the open Beigel–Tarui wall
(`ACC0ExactCompose`).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ModCRTFusion

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModCRTFusion.mod_crt_fuse
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModCRTFusion.hasSymAndRep_modpq_sharedLayer
