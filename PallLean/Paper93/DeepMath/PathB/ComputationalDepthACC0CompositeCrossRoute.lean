import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CompositeMixedRadixSize
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CRTFinsetGate

/-!
# Composite cross-route bookkeeping — assembling the squarefree-composite BT closure

Entry 179 made `DynamicClosesAtBT` a *proved* theorem for the AC⁰[p] route.  For *composite* (squarefree) modulus the
closure is assembled from proved per-route pieces; this file does that **cross-route bookkeeping**, stating the two
assembled halves explicitly:

* **CRT decomposition (entry 171).**  A squarefree composite `MOD_{∏S}` is the conjunction of the per-prime tests:
  `(∏ p∈S, p) ∣ cnt ↔ ∀ p∈S, p ∣ cnt` — so the composite gate *is* `⋀_{p∈S} MOD_p`.
* **Mixed-radix quasipoly size (entry 178).**  The `AND` of the per-prime `SYM∘AND` forms (each of size `≤ Q`, from the
  per-prime exact form of entry 174 or the per-prime RS representation of entry 177) has `SYM∘AND` size `≤ (Q+1)^{|S|}`
  — quasipolynomial for a *constant* number of prime factors `|S|`.

Together: the squarefree composite `MOD_{∏S}` decomposes (CRT) into `|S|` per-prime tests, and their `AND` is a
quasipoly-size `SYM∘AND` — so the composite gate has a quasipoly BT representation, built entirely from the proved
AC⁰[pᵢ] pieces over the distinct primes.

## What is proved (clean axioms, no `sorry`)

* **`composite_count_decomposes`** — the CRT decomposition `(∏ p∈S, p) ∣ cnt ↔ ∀ p∈S, p ∣ cnt` (entry 171).
* **`composite_decide_decomposes`** — its `decide`/Boolean form: the composite `MOD_{∏S}` indicator on the count equals
  the conjunction of the per-prime indicators.
* **`composite_quasipoly_size`** — the `AND` of the per-prime `SYM∘AND` forms (each `≤ Q`) has `SYM∘AND` size
  `≤ (Q+1)^{|S|}` (entry 178), quasipolynomial for constant `|S|`.

## Honest scope

This is the cross-route *bookkeeping*: it states the two assembled halves — the CRT decomposition (the composite gate is
the per-prime conjunction) and the mixed-radix quasipoly size (the per-prime `AND` is quasipoly) — that together give the
composite gate a quasipoly BT representation from the proved per-prime AC⁰[pᵢ] pieces.  It does **not** itself run the
per-prime RS approximation of a whole composite *circuit* over each `F_{pᵢ}` (that is entry 177 applied per prime, then
combined here) — the remaining integration is the per-prime projection of a composite circuit, with `m` fixed so its
prime-factor count is a constant.  Beigel–Tarui and `NEXP ⊄ ACC⁰` (Williams 2011) are proven classical theorems ⇒
formalisation, not an open problem.  NOT a new separation, NOT `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CompositeCrossRoute

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.ACC0YBTExactCompose (HasSymAndForm)
open PallLean.Paper93.DeepMath.PathB.ACC0CompositeMixedRadixSize (andAll mixedRadix_quasipoly_size)

variable {n : ℕ}

/-- **CRT decomposition (proved, entry 171): the composite test is the per-prime conjunction.**  For a finset `S` of
distinct primes, `(∏ p∈S, p) ∣ cnt ↔ ∀ p∈S, p ∣ cnt` — the squarefree composite `MOD_{∏S}` *is* `⋀_{p∈S} MOD_p`. -/
theorem composite_count_decomposes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (cnt : ℕ) :
    ((∏ p ∈ S, p) ∣ cnt) ↔ ∀ p ∈ S, p ∣ cnt :=
  ACC0CRTFinsetGate.prod_primes_dvd_iff S hS cnt

/-- **The `decide`/Boolean form of the CRT decomposition (proved).**  The composite `MOD_{∏S}` indicator on the count
equals the conjunction of the per-prime indicators. -/
theorem composite_decide_decomposes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (cnt : ℕ) :
    (decide ((∏ p ∈ S, p) ∣ cnt) = true) ↔ ∀ p ∈ S, p ∣ cnt := by
  rw [decide_eq_true_eq]
  exact composite_count_decomposes S hS cnt

/-- **Mixed-radix quasipoly size of the per-prime `AND` (proved, entry 178).**  The `AND` of the per-prime `SYM∘AND`
forms (each of size `≤ Q` — from the per-prime exact form of entry 174 or per-prime RS rep of entry 177) has `SYM∘AND`
size `≤ (Q+1)^{|forms|}` — quasipolynomial for a *constant* number of prime factors and quasipolynomial per-prime size
`Q`.  Combined with `composite_decide_decomposes` (the composite gate *is* this `AND`), the composite `MOD` has a
quasipoly BT representation. -/
theorem composite_quasipoly_size (Q : ℕ) (forms : List ((Fin n → Bool) → Bool))
    (hforms : ∀ f ∈ forms, ∃ s, HasSymAndForm f s ∧ s ≤ Q) :
    HasSymAndForm (andAll forms) ((Q + 1) ^ forms.length) :=
  mixedRadix_quasipoly_size Q forms hforms

end PallLean.Paper93.DeepMath.PathB.ACC0CompositeCrossRoute

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeCrossRoute.composite_count_decomposes
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeCrossRoute.composite_decide_decomposes
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeCrossRoute.composite_quasipoly_size
