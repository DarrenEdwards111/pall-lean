import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0LayeredCarryDegree

/-!
# The multi-sorted product-field observer — the construction works; feeding fast-SAT is the open socket

Entry 244 refuted the *single-field* route: `MOD_q` is not low-degree over `F_p` for `q ≠ p` (Smolensky), so the
cross-field combination cannot collapse to one field.  The only remaining escape (roadmap step 4) is a **multi-sorted /
product-field observer** living in `∏_p F_p`, with separate low-degree components per prime and a symmetric combiner.
This file does that analysis honestly.

The finding (the honest middle):

* **The product-field observer exists and works *as an observer* (PROVED).**  For squarefree `m = p·q` (coprime),
  `MOD_m = MOD_p ∧ MOD_q` (CRT), the count is read faithfully via the residue tuple `ZMod (p·q) ≃+* ZMod p × ZMod q`,
  and each component `MOD_{pᵢ}` is low-degree over its *own* field `F_{pᵢ}` (entry-242 `modpIndicator`).  So the
  multi-sorted observer is a genuine faithful reader of `MOD_m` with per-field low-degree components.
* **Feeding fast-SAT is the open socket.**  The combiner is a Boolean `AND` of tests in *different-characteristic*
  fields.  Realising it as a *single* low-degree polynomial over a common field would be the collapse — **blocked by
  Smolensky** (entry 244).  So the observer must stay genuinely product-sorted; whether the Williams/BT fast-SAT
  machinery (which consumes a single `SYM∘AND` over one field / one integer count) can be fed a *multi-sorted*
  observer without collapsing is the **genuinely open** step-5 question.  Not settled here.

⚠️ **No crossing.**  The proved part is the product-observer *construction* (it faithfully decomposes `MOD_m`).  Whether
it yields a quasipoly `SYM∘AND` for fast-SAT is open; the single-field collapse is refuted (244), and a multi-sorted
fast-SAT is not constructed here.

## What is proved (clean axioms, no `sorry`)

* **`modm_iff_modp_and_modq`** (PROVED) — for coprime `p, q`: `(p·q) ∣ k ↔ p ∣ k ∧ q ∣ k`.  `MOD_{pq} = MOD_p ∧ MOD_q` —
  the product-field combiner is the `AND` of the per-prime residue-zero tests.
* **`prod_field_iso`** (PROVED) — `ZMod (p·q) ≃+* ZMod p × ZMod q` (CRT): the product-field structure `∏ F_{pᵢ}`.
* **`prodObs_bijective`** (PROVED) — the CRT residue tuple is a bijection: the product observer reads the count mod
  `p·q` faithfully (no information loss, unlike a single small field — entry 239).

(Each per-prime component `MOD_{pᵢ}` is low-degree over `F_{pᵢ}` by entry-242
`ACC0LayeredCarryDegree.modpIndicator_totalDegree_le`; cited, not restated.)

## The open socket (step 5, not settled)

Can the multi-sorted observer (product of per-field low-degree components + symmetric combiner) feed Williams/BT
fast-SAT — yielding a quasipoly `SYM∘AND` — *without* collapsing to a single field (which Smolensky forbids, entry 244)?
This requires a fast-SAT / `SYM∘AND` machinery that consumes a **product-sorted** observer; it is not constructed here.
If yes → an `ACC⁰[m]` crossing (product-field observer → quasipoly `SYM∘AND` → fast-SAT → Williams/N-Frame); if no → a
formal obstruction to the multi-sorted route.  Open.

## Honest scope

This proves the multi-sorted product-field observer *construction*: `MOD_m` decomposes (CRT) into an `AND` of per-prime
residue-zero tests, each low-degree over its own field, read faithfully by the CRT residue tuple.  It does **not**
construct a multi-sorted fast-SAT, and the single-field collapse is refuted by Smolensky (entry 244).  Whether a
product-sorted observer feeds fast-SAT is the open step-5 question.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0MultiSortedObserver

/-- **The product-field combiner (PROVED).**  For coprime `p, q`, `(p·q) ∣ k ↔ p ∣ k ∧ q ∣ k`: `MOD_{pq}` is the `AND`
of the per-prime residue-zero tests (CRT).  This is the symmetric top combiner of the product-field observer. -/
theorem modm_iff_modp_and_modq (p q k : ℕ) (h : Nat.Coprime p q) :
    (p * q) ∣ k ↔ p ∣ k ∧ q ∣ k := by
  constructor
  · intro hk
    exact ⟨dvd_trans (Dvd.intro q rfl) hk, dvd_trans (Dvd.intro_left p rfl) hk⟩
  · rintro ⟨hp, hq⟩
    exact h.mul_dvd_of_dvd_of_dvd hp hq

/-- **The product-field structure (PROVED).**  `ZMod (p·q) ≃+* ZMod p × ZMod q` (Chinese Remainder): the observer lives
in the product `∏ F_{pᵢ}` of per-prime fields. -/
theorem prod_field_iso (p q : ℕ) (h : Nat.Coprime p q) :
    Nonempty (ZMod (p * q) ≃+* ZMod p × ZMod q) :=
  ⟨ZMod.chineseRemainder h⟩

/-- **The product observer is faithful (PROVED).**  The CRT residue tuple `k ↦ (k mod p, k mod q)` is a bijection
`ZMod (p·q) ≃ ZMod p × ZMod q` — the product observer reads the count mod `p·q` with no information loss (unlike a
single small field, entry 239). -/
theorem prodObs_bijective (p q : ℕ) (h : Nat.Coprime p q) :
    Function.Bijective (ZMod.chineseRemainder h).toFun :=
  (ZMod.chineseRemainder h).bijective

/-!
**The open socket (step 5).**  The product-field observer above is a faithful reader of `MOD_m` with per-prime
low-degree components (entry-242 `modpIndicator`).  Whether it can feed Williams/BT fast-SAT — a quasipoly `SYM∘AND` —
*without* collapsing to a single field (Smolensky-blocked, entry 244) is open: it needs a fast-SAT machinery that
consumes a product-sorted observer.  Not constructed here.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0MultiSortedObserver

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MultiSortedObserver.modm_iff_modp_and_modq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MultiSortedObserver.prod_field_iso
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MultiSortedObserver.prodObs_bijective
