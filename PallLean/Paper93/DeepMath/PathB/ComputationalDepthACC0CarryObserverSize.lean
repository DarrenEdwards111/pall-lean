import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CarryCrossing

/-!
# Carry observer size — quasipoly vs. exponential (conservative bounds, proved)

Entry 238 named the crossing condition: a **carry-faithful** count observer (distinguishing counts the field observer
collapses across carry layers) realised by the low-degree machinery for composite `m`.  The natural N-Frame question
(per the roadmap): is such an observer's **state count** quasipolynomial or exponential?  This file defines the carry
observer's state and size and proves safe bounds — and the honest finding is clean: **the state count is quasipolynomial,
not exponential** (a faithful observer on counts `{0,…,N}` exists with exactly `N+1` states).  So the barrier is *not*
a counting blow-up; it is the **algebraic (low-degree) realisation** of that observer for composite modulus, which
remains the named open socket.

⚠️ **Scope discipline.**  These bound the *state count* of the carry observer.  They show counting is not the
obstruction; they do **not** realise the observer as a low-degree `SYM∘AND` for composite `m`, which is the open
`ACC⁰[m]` barrier.  Nothing here crosses it.

## Definitions

* `CarryProfileState m k := (k : ZMod m)` — the observer's state reading count `k` at modulus `m`.
* `Faithful m N` — the modulus-`m` observer is injective on counts `{0,…,N}` (recovers the exact count).
* `CarryObserverSize m N := #{ k mod m : k ∈ {0,…,N} }` — the number of distinct states the observer occupies.

## What is proved (clean axioms, no `sorry`)

* **`faithful_iff_le`** (PROVED) — the centerpiece: `Faithful m N ↔ N + 1 ≤ m`.  A modulus-`m` observer is faithful on
  `{0,…,N}` iff `m ≥ N+1` (pigeonhole `Fintype.card_le_of_injective` one way; `ZMod.val_cast_of_lt` the other).
* **`carryObserverSize_le_succ`** (PROVED) — `CarryObserverSize m N ≤ N + 1` (image of `N+1` counts).
* **`carryObserverSize_le_modulus`** (PROVED) — `CarryObserverSize m N ≤ m` (states live in `ZMod m`).  Together: a
  *fixed* modulus `m` caps the state count at `m`, so it is **not faithful** once `N + 1 > m` (carry layers needed).
* **`exists_faithful`** (PROVED) — **the quasipoly finding**: `Faithful (N+1) N`.  A faithful observer on `{0,…,N}`
  exists with exactly `N+1` states.  So for `N` quasipolynomial (e.g. `N = #monomials`), the carry observer's state
  count is quasipolynomial — **no exponential blow-up in counting**.
* **`field_faithful_iff`** (PROVED) — *trivial profile collapses to field observer*: `Faithful p N ↔ N + 1 ≤ p`.  When
  the count fits one field (`N < p`), the field observer mod `p` is already faithful (no carry layer needed).
* **`primePow_faithful_iff`** (PROVED) — *prime-power needs carry layers*: `Faithful (p^e) N ↔ N + 1 ≤ p^e`.  A
  prime-power observer is faithful iff it has enough layers (`p^e ≥ N+1`, i.e. `e ≳ log_p N` carry digits).

## The residual barrier (named in entry 238)

The faithful carry observer of size `N+1` realised as a *low-degree* `SYM∘AND` over the composite modulus `m` is the
open barrier — the entry-238 socket `ACC0CarryCrossing.CarryRefinementCrossing`.  This file shows it is **not** the state
count (which is quasipolynomial) but that algebraic realisation that is the composite-`ACC⁰[m]` obstruction.

## Honest scope

The proved bounds settle the quasipoly-vs-exponential question for the *state count*: a faithful carry observer needs
exactly `N+1` states (`faithful_iff_le`, `exists_faithful`) — **quasipolynomial**, not exponential.  A *fixed* modulus
caps states at `m` (`carryObserverSize_le_modulus`), so faithfulness on growing counts needs either a larger field
(`field_faithful_iff`) or carry layers (`primePow_faithful_iff`), both of which keep the state count quasipolynomial.
This **relocates the barrier**: the obstruction is not a counting blow-up but the **algebraic low-degree realisation**
(`LowDegRealizable`) of the observer for composite `m` — the open `ACC⁰[m]` separation-strength problem (entries
234/238).  This file does **not** realise it.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0CarryObserverSize

/-- The carry observer's state reading count `k` at modulus `m`: `(k : ZMod m)`. -/
def CarryProfileState (m k : ℕ) : ZMod m := (k : ZMod m)

/-- The modulus-`m` observer is **faithful** on counts `{0,…,N}`: injective there (recovers the exact count). -/
def Faithful (m N : ℕ) : Prop :=
  Function.Injective (fun k : Fin (N + 1) => CarryProfileState m k.val)

/-- The **carry observer size**: the number of distinct states the modulus-`m` observer occupies on counts `{0,…,N}`. -/
def CarryObserverSize (m N : ℕ) : ℕ :=
  (Finset.image (fun k : ℕ => (k : ZMod m)) (Finset.range (N + 1))).card

/-- **Faithful ⟺ enough states (PROVED).**  `Faithful m N ↔ N + 1 ≤ m`: the modulus-`m` observer recovers all counts
`{0,…,N}` iff it has at least `N+1` states.  Forward by pigeonhole (`Fintype.card_le_of_injective`, `ZMod.card`);
backward since counts `< N+1 ≤ m` have distinct residues (`ZMod.val_cast_of_lt`). -/
theorem faithful_iff_le (m N : ℕ) (hm : 0 < m) : Faithful m N ↔ N + 1 ≤ m := by
  haveI : NeZero m := ⟨hm.ne'⟩
  constructor
  · intro hinj
    have hc := Fintype.card_le_of_injective _ hinj
    simpa [ZMod.card] using hc
  · intro hle k k' h
    have hk : (k.val : ℕ) < m := lt_of_lt_of_le k.isLt hle
    have hk' : (k'.val : ℕ) < m := lt_of_lt_of_le k'.isLt hle
    apply Fin.ext
    have hv := congrArg ZMod.val h
    simp only [CarryProfileState, ZMod.val_cast_of_lt hk, ZMod.val_cast_of_lt hk'] at hv
    exact hv

/-- **Size is at most the count range (PROVED).**  `CarryObserverSize m N ≤ N + 1`. -/
theorem carryObserverSize_le_succ (m N : ℕ) : CarryObserverSize m N ≤ N + 1 := by
  unfold CarryObserverSize
  calc (Finset.image (fun k : ℕ => (k : ZMod m)) (Finset.range (N + 1))).card
      ≤ (Finset.range (N + 1)).card := Finset.card_image_le
    _ = N + 1 := Finset.card_range _

/-- **Size is at most the modulus (PROVED).**  `CarryObserverSize m N ≤ m` (states live in `ZMod m`).  Hence a *fixed*
modulus caps the state count, and cannot stay faithful once `N + 1 > m` — carry layers are then required. -/
theorem carryObserverSize_le_modulus (m N : ℕ) (hm : 0 < m) : CarryObserverSize m N ≤ m := by
  haveI : NeZero m := ⟨hm.ne'⟩
  unfold CarryObserverSize
  calc (Finset.image (fun k : ℕ => (k : ZMod m)) (Finset.range (N + 1))).card
      ≤ Fintype.card (ZMod m) := Finset.card_le_card (Finset.subset_univ _)
    _ = m := ZMod.card m

/-- **The quasipoly finding (PROVED).**  `Faithful (N+1) N`: a faithful carry observer on counts `{0,…,N}` exists with
exactly `N+1` states.  So the carry observer's state count is **quasipolynomial** when `N` is (e.g. `N = #monomials`) —
there is *no exponential blow-up in counting*.  The barrier lies elsewhere (low-degree realisation). -/
theorem exists_faithful (N : ℕ) : Faithful (N + 1) N :=
  (faithful_iff_le (N + 1) N (Nat.succ_pos N)).mpr (le_refl _)

/-- **Trivial profile collapses to the field observer (PROVED).**  `Faithful p N ↔ N + 1 ≤ p`: when the count fits one
field (`N < p`), the field observer mod `p` is already faithful — no carry layer needed (cf. entry-235/238). -/
theorem field_faithful_iff (p N : ℕ) (hp : 0 < p) : Faithful p N ↔ N + 1 ≤ p :=
  faithful_iff_le p N hp

/-- **Prime-power needs carry layers (PROVED).**  `Faithful (p^e) N ↔ N + 1 ≤ p^e`: a prime-power observer is faithful
iff it has enough carry layers (`p^e ≥ N+1`, i.e. `e ≳ log_p N` digits) — the extra layers beyond a single field
(cf. entry-235 `not_powerIndicator_primePow`). -/
theorem primePow_faithful_iff (p e N : ℕ) (hpe : 0 < p ^ e) : Faithful (p ^ e) N ↔ N + 1 ≤ p ^ e :=
  faithful_iff_le (p ^ e) N hpe

/-!
**The residual barrier (named in entry 238, not here).**  The faithful carry observer has state count `N+1`
(quasipolynomial, `exists_faithful`).  What remains open is realising it as a *low-degree* `SYM∘AND` over the composite
modulus — that is the entry-238 socket `ACC0CarryCrossing.CarryRefinementCrossing`, the open `ACC⁰[m]`
separation-strength problem.  The finding of this file is that the obstruction is *not* the state count (no exponential
blow-up) but that algebraic realisation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CarryObserverSize

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryObserverSize.faithful_iff_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryObserverSize.carryObserverSize_le_succ
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryObserverSize.carryObserverSize_le_modulus
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryObserverSize.exists_faithful
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryObserverSize.primePow_faithful_iff
