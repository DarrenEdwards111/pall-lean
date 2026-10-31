import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEncPairDecode

/-!
# Mountain 1, camp 2: the pad function and its verifier — mathematics discharged

The padding ingredient's verifier side (`NTIME(n^{mq})` language ⟹ its padded version in
`NTIME(n^q)`), built to the machine boundary.  Everything that is language-level or arithmetic
is PROVED here; the single remaining obligation is a machine interface (`PadVerifier`),
specified exactly, whose construction is the branching decode-check-retag transducer — machine
engineering in the style of the `comp`/emitter arcs, queued as the next camp.

## The objects

* **`padWith m x`** — the pad: `encPair x 0^{(|x|+1)^m}`.  Self-delimiting by construction;
  padded length `2|x| + 1 + (|x|+1)^m` (`padWith_length`) — the input inflated to its `m`-th
  power, which is what converts exponent `m·q` into exponent `q`.
* **`padLang m L`** — the STRICTLY padded language: accept `y` iff `y` decodes to `(x, junk)`
  with `junk` exactly the required all-`false` pad and `L x`.  Strictness matters: an
  under-padded string must be REJECTED, else the padded verifier's clock busts (decode-and-run
  on an unpadded input costs `n^{mq}`, not `n^q`).

## What is proved

* **`decodePair_sound`** — the decoder's reverse soundness: `decodePair y = some (x, w) ⟹
  y = encPair x w` (strong induction on length).  With the round trip this makes the encoding
  a genuine bijection onto its range — the fact the strictness case analysis rides on.
* **`padLang_padWith`** — on padded strings the language is `L` (round trip).
* **`padLang_eq_false_of_not_pad`** — off the pad range the language rejects (via soundness).
* **`pad_clock_transfer`** — THE arithmetic of padding: `c·(n+1)^{mq} ≤ c·(P+1)^q` for the
  padded length `P` — `pow_mul` plus base monotonicity.  This is the exponent conversion the
  whole ingredient exists for.
* **`ntime_pad`** — the verifier theorem: given the `L`-verifier and a `PadVerifier` machine
  for it, `padLang m L ∈ NTIME(q)`.  Both directions of the membership equivalence and the
  rejection of non-padded inputs are discharged here; the machine interface carries only
  simulation facts.

## The named remaining obligation

`PadVerifier` — a machine that on `encPair (padWith m x) w'` behaves as the `L`-verifier on
`encPair x w'` (`good`), and rejects every non-padded `y` (`bad`), within a `ClockLe q` clock.
Its construction (decode outer, check pad exactness, retag, defer — a branching composition,
`comp` with a reject branch) is machine engineering with no mathematical unknowns; it is the
next camp, not a wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PadFunction

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.IndirectDiagonalization
open PallLean.Paper93.DeepMath.PathB.ConcreteTradingClasses
open PallLean.Paper93.DeepMath.PathB.EncPairDecode

/-- The pad: input, then an all-`false` pad of length `(|x|+1)^m`, in the self-delimiting
pairing. -/
def padWith (m : ℕ) (x : List Bool) : List Bool :=
  encPair x (List.replicate ((x.length + 1) ^ m) false)

/-- Padded length: `2|x| + 1 + (|x|+1)^m`. -/
theorem padWith_length (m : ℕ) (x : List Bool) :
    (padWith m x).length = 2 * x.length + 1 + (x.length + 1) ^ m := by
  rw [padWith, encPair_length, List.length_replicate]

/-- The pad is injective. -/
theorem padWith_injective (m : ℕ) {x y : List Bool}
    (h : padWith m x = padWith m y) : x = y :=
  (encPair_injective h).1

/-- **Reverse soundness of the decoder (proved).**  A successful decode certifies the exact
encoding: `decodePair y = some (x, w) ⟹ y = encPair x w`. -/
theorem decodePair_sound (y : List Bool) :
    ∀ x w, decodePair y = some (x, w) → y = encPair x w := by
  suffices H : ∀ n (y : List Bool), y.length ≤ n →
      ∀ x w, decodePair y = some (x, w) → y = encPair x w from
    fun x w h => H y.length y (le_refl _) x w h
  intro n
  induction n with
  | zero =>
    intro y hy x w h
    have hnil : y = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hy)
    subst hnil
    simp [decodePair] at h
  | succ n ih =>
    intro y hy x w h
    cases y with
    | nil => simp [decodePair] at h
    | cons a rest =>
      cases a with
      | false =>
        simp only [decodePair, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hx, hw⟩ := h
        subst hx; subst hw
        rw [encPair_nil]
      | true =>
        cases rest with
        | nil => simp [decodePair] at h
        | cons b rest' =>
          simp only [decodePair] at h
          cases hd : decodePair rest' with
          | none => rw [hd] at h; simp at h
          | some p =>
            obtain ⟨x', w'⟩ := p
            rw [hd] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hx, hw⟩ := h
            have hlen : rest'.length ≤ n := by
              simp only [List.length_cons] at hy
              omega
            have hrest : rest' = encPair x' w' := ih rest' hlen x' w' hd
            subst hx; subst hw
            rw [encPair_cons, ← hrest]

/-- The strictly padded language: decode, check the pad EXACTLY, then ask `L`. -/
def padLang (m : ℕ) (L : Lang) : Lang := fun y =>
  match decodePair y with
  | some (x, junk) =>
      decide (junk = List.replicate ((x.length + 1) ^ m) false) && L x
  | none => false

/-- On padded strings the padded language is `L` (proved). -/
theorem padLang_padWith (m : ℕ) (L : Lang) (x : List Bool) :
    padLang m L (padWith m x) = L x := by
  simp [padLang, padWith, decodePair_encPair]

/-- Off the pad range the padded language rejects (proved, via reverse soundness). -/
theorem padLang_eq_false_of_not_pad (m : ℕ) (L : Lang) (y : List Bool)
    (h : ∀ x, y ≠ padWith m x) : padLang m L y = false := by
  simp only [padLang]
  cases hd : decodePair y with
  | none => rfl
  | some p =>
    obtain ⟨x, junk⟩ := p
    by_cases hj : junk = List.replicate ((x.length + 1) ^ m) false
    · exfalso
      apply h x
      rw [decodePair_sound y x junk hd, hj]
      rfl
    · simp [hj]

/-- **The exponent conversion (proved).**  The clock at exponent `m·q` on the raw length is
within the clock at exponent `q` on the padded length: `pow_mul` + base monotonicity. -/
theorem pad_clock_transfer (m q c n : ℕ) :
    c * (n + 1) ^ (m * q) ≤ c * (2 * n + 1 + (n + 1) ^ m + 1) ^ q := by
  apply Nat.mul_le_mul_left
  rw [Nat.pow_mul]
  apply Nat.pow_le_pow_left
  omega

/-- **The machine interface — the named remaining obligation of this camp.**  A verifier for
the padded language: on properly padded inputs it mirrors the `L`-verifier (`good`); on
everything else it rejects (`bad`); within a `ClockLe q` clock.  Construction = decode, check
pad exactness, retag, defer — a branching composition in the style of `comp`; machine
engineering, no mathematical unknowns. -/
structure PadVerifier (m q : ℕ) (M : Machine) (T : ℕ → ℕ) where
  /-- the padded-language verifier machine -/
  Mv : Machine
  /-- its clock -/
  Tv : ℕ → ℕ
  /-- its clock constant -/
  cv : ℕ
  /-- the clock is at exponent `q` -/
  clock : ClockLe q cv Tv
  /-- on padded inputs, mirror the `L`-verifier -/
  good : ∀ x w',
    (HaltsBy Mv (encPair (padWith m x) w') (Tv (encPair (padWith m x) w').length) ∧
      decideOut Mv (encPair (padWith m x) w') (Tv (encPair (padWith m x) w').length) = true)
    ↔ (HaltsBy M (encPair x w') (T (encPair x w').length) ∧
      decideOut M (encPair x w') (T (encPair x w').length) = true)
  /-- off the pad range, reject every witness -/
  bad : ∀ y, (∀ x, y ≠ padWith m x) → ∀ w',
    ¬ (HaltsBy Mv (encPair y w') (Tv (encPair y w').length) ∧
      decideOut Mv (encPair y w') (Tv (encPair y w').length) = true)

/-- **The verifier theorem (proved).**  Given the `L`-verifier's data and a `PadVerifier` for
it, the strictly padded language is in `NTIME(q)`.  All membership logic discharged; only the
machine interface remains. -/
theorem ntime_pad (m q : ℕ) (L : Lang) (M : Machine) (T : ℕ → ℕ)
    (hspec : ∀ x, (L x = true ↔ ∃ w,
      HaltsBy M (encPair x w) (T (encPair x w).length) ∧
      decideOut M (encPair x w) (T (encPair x w).length) = true))
    (P : PadVerifier m q M T) : NTIME q (padLang m L) := by
  refine ⟨P.Mv, P.Tv, P.cv, P.clock, fun y => ?_⟩
  by_cases hy : ∃ x, y = padWith m x
  · obtain ⟨x, rfl⟩ := hy
    rw [padLang_padWith]
    constructor
    · intro hLx
      obtain ⟨w, hw⟩ := (hspec x).mp hLx
      exact ⟨w, (P.good x w).mpr hw⟩
    · rintro ⟨w, hw⟩
      exact (hspec x).mpr ⟨w, (P.good x w).mp hw⟩
  · push_neg at hy
    rw [padLang_eq_false_of_not_pad m L y hy]
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨w, hw⟩
    exact P.bad y hy w hw

end PallLean.Paper93.DeepMath.PathB.PadFunction

#print axioms PallLean.Paper93.DeepMath.PathB.PadFunction.decodePair_sound
#print axioms PallLean.Paper93.DeepMath.PathB.PadFunction.padLang_padWith
#print axioms PallLean.Paper93.DeepMath.PathB.PadFunction.padLang_eq_false_of_not_pad
#print axioms PallLean.Paper93.DeepMath.PathB.PadFunction.pad_clock_transfer
#print axioms PallLean.Paper93.DeepMath.PathB.PadFunction.ntime_pad
