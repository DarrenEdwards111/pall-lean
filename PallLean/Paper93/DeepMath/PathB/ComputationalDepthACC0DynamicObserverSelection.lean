import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CountCarrySymmetric

/-!
# Dynamic observer selection — the boundary forces observer refinement (and the BT closure socket)

The N-Frame dynamic-boundary principle, made precise for the `MOD`/`ACC⁰` ladder: the boundary does not merely shrink
states, it *forces the observer to refine* exactly when the coarser observer loses the information needed to evaluate the
fragment.  This file formalises the principle and proves the refinement steps that are genuinely provable, then isolates
the deep claim (refinement closes at a quasipolynomial Beigel–Tarui observer) as an honest, clearly-labelled socket.

## The observer-selection principle

An **observer** `O : ℕ → α` reads the count `s = ∑ᵢ xᵢ` into an observation state.  It is **sufficient** for a decision
`f` when equal observations force equal `f`-values (`O` carries enough state to evaluate `f`); `O₁` **refines** `O₀` when
it distinguishes at least as much.  The boundary's chosen observer is the *weakest sufficient* one — the minimal state
that preserves evaluation.  As the fragment's modulus grows, sufficiency forces refinement up a ladder:

```
  incidence  <  residue (mod p)  <  CRT residues  <  p-adic carry (downshift tower)  <  threshold/carry  <  BT counting
```

## What is proved (clean axioms, no `sorry`)

* **`resObs_insufficient_for_modPow`** — the residue observer `s ↦ s mod p` is **not** sufficient for `MOD_{p^e}`
  (`e ≥ 2`): `0` and `p` share their residue but `MOD_{p^e}` separates them.  Refinement is *forced*.
* **`padicObs_sufficient_for_modPow`** — the `p`-adic carry observer `s ↦ (s/p^i mod p)_{i<e}` **is** sufficient for
  `MOD_{p^e}` (via the down-shift AND decomposition).  Refinement *succeeds* at the `p`-adic level.
* **`padicObs_finer_than_resObs`** — the `p`-adic observer refines the residue observer (its `i=0` component is the
  residue).  So the step residue → `p`-adic is a genuine refinement.
* **`observer_refines_modp_to_padic`** — the three together: the dynamic boundary refines `MOD_p`'s observer to the
  `p`-adic observer for `MOD_{p^e}`.
* **`carry_observer_eq_threshold_observer`** — the carry observer factors through a Hamming-**threshold** observer:
  `⌊s/p⌋ = ∑_{j} [s ≥ j·p]` (re-export of `…ACC0CountCarrySymmetric`).

## Honest scope — the socket (the ACC wall)

The refinement *ladder* is proved up to the threshold observer.  The conceptual closure — that repeated refinement
stabilises at a **quasipolynomial-size** Beigel–Tarui / `SYM∘AND` observer, making BT the *fixed point* of dynamic
refinement rather than an external trick — is **not** proved here.  It is stated as an explicit socket and the cash-out
to the Williams chain is pure glue (modus ponens) through that socket plus the quasipoly-size bound.  Discharging the
socket (or refuting it) **is** the open `ACC⁰[composite]` lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0DynamicObserverSelection

open Finset
open PallLean.Paper93.DeepMath.PathB

/-- An **observer** is a map `O : ℕ → α` reading the count into an observation state.  It is **sufficient** for the
decision `f` if equal observations force equal `f`-values — `O` carries the minimal state to evaluate `f`. -/
def Sufficient {α : Type*} (O : ℕ → α) (f : ℕ → Prop) : Prop :=
  ∀ x y, O x = O y → (f x ↔ f y)

/-- `O₁` **refines** (is finer than) `O₀`: it distinguishes at least as much, so the partition by `O₁` refines that by
`O₀`.  Observer refinement is the dynamic boundary moving up the ladder. -/
def Finer {α β : Type*} (O₁ : ℕ → α) (O₀ : ℕ → β) : Prop :=
  ∀ x y, O₁ x = O₁ y → O₀ x = O₀ y

/-- The decision computed by the fragment: `MOD_{p^e}` on the count. -/
def modPow (p e : ℕ) : ℕ → Prop := fun s => p ^ e ∣ s

/-- The **residue observer** (the `MOD_p` / field observer): `s ↦ s mod p`. -/
def resObs (p : ℕ) : ℕ → ZMod p := fun s => (s : ZMod p)

/-- The **`p`-adic carry observer**: the down-shift tower of residues `s ↦ (⌊s/p^i⌋ mod p)_{i<e}`. -/
def padicObs (p e : ℕ) : ℕ → (Fin e → ZMod p) := fun s i => ((s / p ^ (i : ℕ) : ℕ) : ZMod p)

/-- **Refinement is forced (proved): the residue observer is not sufficient for `MOD_{p^e}` (`e ≥ 2`).**
`0` and `p` have the same residue mod `p` (`resObs p 0 = resObs p p = 0`), yet `MOD_{p^e}` accepts `0` and rejects `p`.
So the `MOD_p` observer loses the information `MOD_{p^e}` needs — the boundary must refine. -/
theorem resObs_insufficient_for_modPow (p e : ℕ) (hp : p.Prime) (he : 2 ≤ e) :
    ¬ Sufficient (resObs p) (modPow p e) := by
  intro hS
  have h0p : resObs p 0 = resObs p p := by simp [resObs]
  have hpow : modPow p e p := (hS 0 p h0p).mp (by simp [modPow])
  rw [modPow] at hpow
  have hle := Nat.le_of_dvd hp.pos hpow
  have : p < p ^ e := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ e := Nat.pow_lt_pow_right hp.one_lt (by omega)
  omega

/-- **Refinement succeeds (proved): the `p`-adic carry observer is sufficient for `MOD_{p^e}`.**  Via the down-shift
decomposition `p^e ∣ s ↔ ∀ i < e, p ∣ ⌊s/p^i⌋`, equal `p`-adic observations force agreement on every conjunct, hence on
`MOD_{p^e}`.  The boundary's refinement lands at a sufficient observer at the `p`-adic level. -/
theorem padicObs_sufficient_for_modPow (p e : ℕ) (hp : 0 < p) :
    Sufficient (padicObs p e) (modPow p e) := by
  intro x y hxy
  rw [modPow, modPow,
      ACC0ValuationSparseTheory.modPrimePower_eq_and_of_downshift_modP p e x hp,
      ACC0ValuationSparseTheory.modPrimePower_eq_and_of_downshift_modP p e y hp]
  have key : ∀ i, i < e → (p ∣ (x / p ^ i) ↔ p ∣ (y / p ^ i)) := by
    intro i hi
    have hcomp : ((x / p ^ i : ℕ) : ZMod p) = ((y / p ^ i : ℕ) : ZMod p) := congrFun hxy ⟨i, hi⟩
    rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff, hcomp]
  constructor <;> intro h i hi
  · exact (key i hi).mp (h i hi)
  · exact (key i hi).mpr (h i hi)

/-- **The step is a genuine refinement (proved): the `p`-adic observer refines the residue observer.**  Its `i=0`
component is exactly the residue `s mod p` (`s / p^0 = s`), so equal `p`-adic observations force equal residues. -/
theorem padicObs_finer_than_resObs (p e : ℕ) (he : 1 ≤ e) :
    Finer (padicObs p e) (resObs p) := by
  intro x y hxy
  have := congrFun hxy ⟨0, he⟩
  simpa [padicObs, resObs] using this

/-- **Dynamic refinement `MOD_p → p`-adic (proved).**  The boundary's observer for `MOD_p` (residue) is insufficient for
`MOD_{p^e}`, the `p`-adic carry observer is sufficient, and it refines the residue observer — so the boundary is forced
to (and does) refine from the field-residue observer to the carry-aware `p`-adic observer. -/
theorem observer_refines_modp_to_padic (p e : ℕ) (hp : p.Prime) (he : 2 ≤ e) :
    ¬ Sufficient (resObs p) (modPow p e)
      ∧ Sufficient (padicObs p e) (modPow p e)
      ∧ Finer (padicObs p e) (resObs p) :=
  ⟨resObs_insufficient_for_modPow p e hp he,
   padicObs_sufficient_for_modPow p e hp.pos,
   padicObs_finer_than_resObs p e (by omega)⟩

/-- **Carry observer = threshold observer (proved).**  The carry component `⌊s/p⌋` of the `p`-adic observer factors
through a Hamming-**threshold** observer: `⌊s/p⌋ = ∑_{j∈[1,N]} [j·p ≤ s]` (for `⌊s/p⌋ ≤ N`).  So the next refinement of
the carry observer is the threshold/Majority observer — exactly where `ACC⁰` becomes hard. -/
theorem carry_observer_eq_threshold_observer (p s N : ℕ) (hp : 0 < p) (hN : s / p ≤ N) :
    s / p = ∑ j ∈ Finset.Icc 1 N, (if j * p ≤ s then 1 else 0) :=
  ACC0CountCarrySymmetric.count_carry_eq_sum_thresholds p s N hp hN

/-! ## The BT-closure socket and the cash-out (honest, unproved)

The refinement ladder above is proved up to the threshold observer.  The remaining content — that dynamic refinement
*closes* at a quasipolynomial-size Beigel–Tarui observer, which then drives the Williams chain — is the open
`ACC⁰[composite]` wall.  We record it as explicit Prop sockets and a pure-glue cash-out; we prove **none** of the
sockets.  `DynamicClosesAtBT` (refinement stabilises at a BT/`SYM∘AND` observer), `BTHasQuasipolySparse` (that observer
has a quasipoly-size sparse representation), and the Williams-style `quasipoly_to_speedup` are all hypotheses. -/

/-- **The cash-out (conditional glue — PROVED as stated, but every premise is an unproved socket).**  If dynamic
refinement closes at a BT observer (`hClosure : DynamicClosesAtBT`), and that yields a quasipolynomial sparse
representation (`closure_to_quasipoly`), and a quasipoly representation yields the `ACC⁰`-SAT speedup
(`quasipoly_to_speedup`, the Williams input), then the speedup holds.  This is the dynamic-observer route to
`NEXP ⊄ ACC⁰` *modulo the sockets* — pure modus ponens; the open content is entirely in `DynamicClosesAtBT` and the two
implications, which together are the `ACC⁰[composite]` lower bound and are **not** proved. -/
theorem dynamic_boundary_to_acc0_sat_speedup
    {DynamicClosesAtBT BTHasQuasipolySparse Speedup : Prop}
    (closure_to_quasipoly : DynamicClosesAtBT → BTHasQuasipolySparse)
    (quasipoly_to_speedup : BTHasQuasipolySparse → Speedup)
    (hClosure : DynamicClosesAtBT) : Speedup :=
  quasipoly_to_speedup (closure_to_quasipoly hClosure)

end PallLean.Paper93.DeepMath.PathB.ACC0DynamicObserverSelection

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DynamicObserverSelection.resObs_insufficient_for_modPow
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DynamicObserverSelection.padicObs_sufficient_for_modPow
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DynamicObserverSelection.padicObs_finer_than_resObs
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DynamicObserverSelection.observer_refines_modp_to_padic
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DynamicObserverSelection.carry_observer_eq_threshold_observer
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DynamicObserverSelection.dynamic_boundary_to_acc0_sat_speedup
