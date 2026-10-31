import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPaddingAssembly
import Mathlib.Tactic.Ring

/-!
# Mountain 1, camp 4: the witness-budget catch — the interface fixed before the machine is built

Camp 4's task was to construct the `PadVerifier` machine.  The construction attempt surfaced a
**spec bug** in the camp-2 interface, caught here *before* the machine-engineering climb was spent
on it:

**The obstruction.**  `PadVerifier.good` mirrors the `L`-verifier on the *same* witness `w'`, and
this corpus's `NTIME` clock is measured in the **pair** length (witness included — the design that
keeps monotonicity honest).  The pad stretches `x` but *not* `w'`: on witness-heavy pairs the padded
verifier's budget is `≈ cv·|w'|^q` while simulating `M` may take `≈ |w'|^{mq}`.  The clock-transfer
inequality any construction would rely on is **false**, machine-checked: `naive_budget_fails` — for
every constant `cv` there is a witness making the naive budget strictly smaller than the needed one
(already at `m = 2, q = 1, x = []`).

**The fix.**  Pad the witness too: the padded language's witness convention is `padWith m w`.  Then
the padded pair stretches in *both* components, and the corrected transfer holds with a constant
`3^{mq}` by a max/convexity argument: `pad_clock_transfer2` —
`c·(|encPair x w|+1)^{mq} ≤ c·3^{mq}·(|encPair (padWith m x) (padWith m w)|+1)^q`.  PROVED.

## What is proved

* **`naive_budget_fails`** — the refutation: the unpadded-witness clock transfer is false for every
  constant.  The camp-2 interface (`PadVerifier`) is thereby *obstructed* — not false (its
  `ntime_pad` remains a correct conditional), but its machine obligation is not constructible in
  general, and the campaign would have discovered this only after the climb.
* **`pad_clock_transfer2`** — the corrected budget, proved: `2a+b+2 ≤ 3·max(a+1, b+1)`, powers
  through `max^m ≤ (a+1)^m + (b+1)^m`, and both stretched components sit inside the padded pair.
* **`PadVerifier2` / `ntime_pad2`** — the fixed interface (witness convention `padWith m w`; reject
  clauses for non-padded `y` *and* non-padded witnesses) and the verifier theorem re-proved on it:
  all membership logic discharged; the machine obligation is now a *satisfiable* spec.
* **`ntimeHalf_of_padVerifiers2` / `concretePadding_of_machines2`** — the assembly rewired:
  `ConcretePadding` rests on `PadVerifiers2Exist` (the decode–check-both-pads–retag transducer,
  camp 5's target, with `pad_clock_transfer2` paying its clock) plus the virtual-input DTS half.

Same discipline as the `Universal` vacuity catch: audit the interface before spending the
construction.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PadWitnessBudget

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.IndirectDiagonalization
open PallLean.Paper93.DeepMath.PathB.ConcreteTradingClasses
open PallLean.Paper93.DeepMath.PathB.EncPairDecode
open PallLean.Paper93.DeepMath.PathB.PadFunction
open PallLean.Paper93.DeepMath.PathB.PaddingAssembly

/-! ### The refutation: the unpadded-witness budget is false -/

/-- The arithmetic core: `cv·(7cv+13) < (7cv+9)²` for every `cv`. -/
theorem naive_budget_core (cv : ℕ) : cv * (7 * cv + 13) < (7 * cv + 9) ^ 2 := by
  have h1 : cv * (7 * cv + 13) = 7 * (cv * cv) + 13 * cv := by ring
  have h2 : (7 * cv + 9) ^ 2 = 49 * (cv * cv) + 126 * cv + 81 := by ring
  omega

/-- **The naive budget fails (proved).**  With the witness unpadded, for every clock constant `cv`
there is a witness on which the padded verifier's budget (exponent `q = 1`, at the padded pair
length) is strictly below the original clock's need (exponent `mq = 2`, at the raw pair length) —
already at `m = 2`, `x = []`.  The camp-2 machine obligation is unconstructible in general. -/
theorem naive_budget_fails (cv : ℕ) :
    ∃ w : List Bool,
      cv * ((encPair (padWith 2 ([] : List Bool)) w).length + 1)
        < ((encPair ([] : List Bool) w).length + 1) ^ 2 := by
  refine ⟨List.replicate (7 * cv + 7) false, ?_⟩
  have e1 : (encPair (padWith 2 ([] : List Bool)) (List.replicate (7 * cv + 7) false)).length + 1
      = 7 * cv + 13 := by
    rw [encPair_length, padWith_length, List.length_replicate]
    simp only [List.length_nil]
    norm_num
    omega
  have e2 : (encPair ([] : List Bool) (List.replicate (7 * cv + 7) false)).length + 1
      = 7 * cv + 9 := by
    rw [encPair_length, List.length_replicate]
    simp only [List.length_nil]
    omega
  rw [e1, e2]
  exact naive_budget_core cv

/-! ### The corrected budget: pad the witness too -/

/-- **The corrected exponent conversion (proved).**  With both components padded, the clock at
exponent `m·q` on the raw pair fits inside the clock at exponent `q` on the padded pair, at the
price of the constant `3^{mq}`: `2a+b+2 ≤ 3·max`, `max^m ≤ (a+1)^m + (b+1)^m`, and both stretched
components sit inside the padded pair. -/
theorem pad_clock_transfer2 (m q c : ℕ) (x w : List Bool) :
    c * ((encPair x w).length + 1) ^ (m * q)
      ≤ c * 3 ^ (m * q) * ((encPair (padWith m x) (padWith m w)).length + 1) ^ q := by
  have hlen : (encPair x w).length + 1 = 2 * x.length + w.length + 2 := by
    rw [encPair_length]
    omega
  have hmax : 2 * x.length + w.length + 2 ≤ 3 * max (x.length + 1) (w.length + 1) := by
    rcases Nat.le_total x.length w.length with hab | hab
    · rw [max_eq_right (by omega : x.length + 1 ≤ w.length + 1)]; omega
    · rw [max_eq_left (by omega : w.length + 1 ≤ x.length + 1)]; omega
  have hmaxpow : max (x.length + 1) (w.length + 1) ^ m
      ≤ (x.length + 1) ^ m + (w.length + 1) ^ m := by
    rcases max_choice (x.length + 1) (w.length + 1) with hm' | hm'
    · rw [hm']; exact Nat.le_add_right _ _
    · rw [hm']; exact Nat.le_add_left _ _
  have hcore : (2 * x.length + w.length + 2) ^ m
      ≤ 3 ^ m * ((x.length + 1) ^ m + (w.length + 1) ^ m) :=
    calc (2 * x.length + w.length + 2) ^ m
        ≤ (3 * max (x.length + 1) (w.length + 1)) ^ m := Nat.pow_le_pow_left hmax m
      _ = 3 ^ m * max (x.length + 1) (w.length + 1) ^ m := by rw [Nat.mul_pow]
      _ ≤ 3 ^ m * ((x.length + 1) ^ m + (w.length + 1) ^ m) := Nat.mul_le_mul_left _ hmaxpow
  have hsum : (x.length + 1) ^ m + (w.length + 1) ^ m
      ≤ (encPair (padWith m x) (padWith m w)).length + 1 := by
    rw [encPair_length, padWith_length, padWith_length]
    omega
  have hfull : (2 * x.length + w.length + 2) ^ m
      ≤ 3 ^ m * ((encPair (padWith m x) (padWith m w)).length + 1) :=
    le_trans hcore (Nat.mul_le_mul_left _ hsum)
  calc c * ((encPair x w).length + 1) ^ (m * q)
      = c * ((2 * x.length + w.length + 2) ^ m) ^ q := by rw [hlen, pow_mul]
    _ ≤ c * (3 ^ m * ((encPair (padWith m x) (padWith m w)).length + 1)) ^ q :=
        Nat.mul_le_mul_left c (Nat.pow_le_pow_left hfull q)
    _ = c * 3 ^ (m * q) * ((encPair (padWith m x) (padWith m w)).length + 1) ^ q := by
        rw [Nat.mul_pow, ← pow_mul, Nat.mul_assoc]

/-! ### The fixed interface and the verifier theorem, re-proved -/

/-- **The fixed machine interface.**  The padded language's witness convention pads the witness too:
mirror the `L`-verifier on `(padWith m x, padWith m w)` pairs (`good`); reject non-padded inputs
(`badY`) and non-padded witnesses (`badW`).  `pad_clock_transfer2` pays this interface's clock —
the spec is now satisfiable. -/
structure PadVerifier2 (m q : ℕ) (M : Machine) (T : ℕ → ℕ) where
  /-- the padded-language verifier machine -/
  Mv : Machine
  /-- its clock -/
  Tv : ℕ → ℕ
  /-- its clock constant -/
  cv : ℕ
  /-- the clock is at exponent `q` -/
  clock : ClockLe q cv Tv
  /-- on padded input–witness pairs, mirror the `L`-verifier -/
  good : ∀ x w,
    (HaltsBy Mv (encPair (padWith m x) (padWith m w))
        (Tv (encPair (padWith m x) (padWith m w)).length) ∧
      decideOut Mv (encPair (padWith m x) (padWith m w))
        (Tv (encPair (padWith m x) (padWith m w)).length) = true)
    ↔ (HaltsBy M (encPair x w) (T (encPair x w).length) ∧
      decideOut M (encPair x w) (T (encPair x w).length) = true)
  /-- off the pad range, reject every witness -/
  badY : ∀ y, (∀ x, y ≠ padWith m x) → ∀ w'',
    ¬ (HaltsBy Mv (encPair y w'') (Tv (encPair y w'').length) ∧
      decideOut Mv (encPair y w'') (Tv (encPair y w'').length) = true)
  /-- non-padded witnesses are rejected -/
  badW : ∀ x w'', (∀ w, w'' ≠ padWith m w) →
    ¬ (HaltsBy Mv (encPair (padWith m x) w'') (Tv (encPair (padWith m x) w'').length) ∧
      decideOut Mv (encPair (padWith m x) w'') (Tv (encPair (padWith m x) w'').length) = true)

/-- **The verifier theorem on the fixed interface (proved).**  Given the `L`-verifier's data and a
`PadVerifier2`, the strictly padded language is in `NTIME(q)`.  All membership logic discharged. -/
theorem ntime_pad2 (m q : ℕ) (L : Lang) (M : Machine) (T : ℕ → ℕ)
    (hspec : ∀ x, (L x = true ↔ ∃ w,
      HaltsBy M (encPair x w) (T (encPair x w).length) ∧
      decideOut M (encPair x w) (T (encPair x w).length) = true))
    (P : PadVerifier2 m q M T) : NTIME q (padLang m L) := by
  refine ⟨P.Mv, P.Tv, P.cv, P.clock, fun y => ?_⟩
  by_cases hy : ∃ x, y = padWith m x
  · obtain ⟨x, rfl⟩ := hy
    rw [padLang_padWith]
    constructor
    · intro hLx
      obtain ⟨w, hw⟩ := (hspec x).mp hLx
      exact ⟨padWith m w, (P.good x w).mpr hw⟩
    · rintro ⟨w'', hw''⟩
      by_cases hw : ∃ w, w'' = padWith m w
      · obtain ⟨w, rfl⟩ := hw
        exact (hspec x).mpr ⟨w, (P.good x w).mp hw''⟩
      · push_neg at hw
        exact absurd hw'' (P.badW x w'' hw)
  · push_neg at hy
    rw [padLang_eq_false_of_not_pad m L y hy]
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨w'', hw''⟩
    exact P.badY y hy w'' hw''

/-! ### The assembly, rewired -/

/-- **The machine obligation, on the satisfiable spec.**  Camp 5's construction target. -/
def PadVerifiers2Exist : Prop :=
  ∀ m q (M : Machine) (T : ℕ → ℕ), 1 ≤ m → Nonempty (PadVerifier2 m q M T)

/-- The NTIME half from the fixed machine obligation (proved). -/
theorem ntimeHalf_of_padVerifiers2 (h : PadVerifiers2Exist) : PaddingNTIMEHalf := by
  intro m q L hm hL
  obtain ⟨M, T, c, hclock, hspec⟩ := hL
  obtain ⟨P⟩ := h m q M T hm
  exact ntime_pad2 m q L M T hspec P

/-- **The mountain, re-reduced (proved).**  `ConcretePadding` rests on the *satisfiable* machine
obligation plus the virtual-input DTS half. -/
theorem concretePadding_of_machines2 (hV : PadVerifiers2Exist) (hD : PaddingDTSHalf) :
    ConcretePadding :=
  concretePadding_of_halves (ntimeHalf_of_padVerifiers2 hV) hD

end PallLean.Paper93.DeepMath.PathB.PadWitnessBudget

#print axioms PallLean.Paper93.DeepMath.PathB.PadWitnessBudget.naive_budget_fails
#print axioms PallLean.Paper93.DeepMath.PathB.PadWitnessBudget.pad_clock_transfer2
#print axioms PallLean.Paper93.DeepMath.PathB.PadWitnessBudget.ntime_pad2
#print axioms PallLean.Paper93.DeepMath.PathB.PadWitnessBudget.concretePadding_of_machines2
