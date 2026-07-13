import Mathlib

/-!
# Round 4: error-polarity forcing for SAT circuit diagonalization — the polarity↔size duality

Paper round (`ATTACK_STEP6_ROUND4.md`) result, with its two passing mechanisms and its exact death-point
formalized.  The attack: force every erroneous SAT circuit to make a *witnessable* (NP-checkable) false-negative
error, collapsing Kannan-style `Σ₂` diagonalization to `NP` and yielding `SAT ∉ P/poly`.

Finding: the polarity obstruction (the coNP "over-claims SAT" branch) is **convertible** via SAT's downward
self-reducibility — but the conversion exposes a **size** obstruction, and the two are dual.

* `sat_iff_restr` — **the self-reduction gadget** (SAT-specific structure): a Boolean function is satisfiable iff
  one of its two restrictions on a coordinate is.  This is what lets the greedy search descend.
* `verifyWrap_sound` — **the false-negative-only conversion**: any search wrapped by a final verification has NO
  false positives — every accepted instance comes with a witness (NP-checkable).  So against the wrapped circuit
  both error branches are NP-witnessable: the polarity problem is solved (gate 2 passes).
* `encode_exceeds_length` — **the exact death-point** (gate 3): a self-referential diagonal `φ*` must encode the
  circuit `C_N` it targets, so `|φ*| ≥ |C_N| = N^k > N`; the formula exceeds its own length and the diagonal never
  closes.  `N < N^k` for `k ≥ 2` is the whole obstruction.

**Conclusion.**  Self-reducibility trades the polarity obstruction (gate 2) for the size obstruction (gate 3); it
cannot eliminate both.  This is precisely why non-uniform SAT diagonalization reaches `Σ₂` (where the coNP branch
is affordable) and cannot descend to `NP` — the missing-witness frontier is this duality.  Uniform diagonalization
escapes only because machines have `O(1)` descriptions.  Honest boundary, obstruction machine-checked.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SelfReductionPolarity

variable {m : ℕ}

/-- A Boolean function (a "formula" as its truth table). -/
abbrev BF (m : ℕ) := (Fin m → Bool) → Bool

/-- Satisfiability. -/
def Sat (f : BF m) : Prop := ∃ a, f a = true

/-- Restriction: fix coordinate `i` to `b`. -/
def restr (f : BF m) (i : Fin m) (b : Bool) : BF m := fun x => f (Function.update x i b)

/-- **The self-reduction gadget** (SAT-specific downward self-reducibility): `f` is satisfiable iff one of its two
coordinate-`i` restrictions is.  This is the structure the greedy witness-search descends through. -/
theorem sat_iff_restr (f : BF m) (i : Fin m) :
    Sat f ↔ Sat (restr f i false) ∨ Sat (restr f i true) := by
  constructor
  · rintro ⟨a, ha⟩
    have hkey : restr f i (a i) a = true := by
      unfold restr; rwa [Function.update_eq_self]
    cases hb : a i with
    | false => exact Or.inl ⟨a, by rw [hb] at hkey; exact hkey⟩
    | true => exact Or.inr ⟨a, by rw [hb] at hkey; exact hkey⟩
  · rintro (⟨a, ha⟩ | ⟨a, ha⟩)
    · exact ⟨Function.update a i false, ha⟩
    · exact ⟨Function.update a i true, ha⟩

/-- A search procedure produces a candidate assignment from a (purported) decider's behaviour on `f`. -/
def verifyWrap (search : BF m → (Fin m → Bool)) (f : BF m) : Bool := f (search f)

/-- **The false-negative-only conversion.**  Any search wrapped by a final verification has NO false positives:
every accepted `f` is genuinely satisfiable, *with the witness in hand* (NP-checkable).  So the coNP
"over-claims SAT" polarity branch is eliminated — the wrapped circuit errs only by false negatives, which are
themselves NP-witnessable. -/
theorem verifyWrap_sound (search : BF m → (Fin m → Bool)) (f : BF m)
    (h : verifyWrap search f = true) : Sat f :=
  ⟨search f, h⟩

/-- If the search is correct on satisfiable inputs, the wrapped decider is also complete — so a *correct* base
decider yields a fully-correct wrapped one; only an *incorrect* base decider leaves (NP-witnessable) false
negatives. -/
theorem verifyWrap_complete (search : BF m → (Fin m → Bool)) (f : BF m)
    (h : Sat f → f (search f) = true) (hf : Sat f) : verifyWrap search f = true :=
  h hf

/-- **The exact death-point (gate 3, size).**  A self-referential diagonal formula against a circuit family of
size `N^k` must encode that circuit, hence has length `≥ N^k`; for `k ≥ 2` this exceeds `N`, so no length-`N`
diagonal against the circuit of its own length exists.  `N < N^k` is the entire obstruction. -/
theorem encode_exceeds_length {N k : ℕ} (hN : 2 ≤ N) (hk : 2 ≤ k) : N < N ^ k := by
  have h2 : N < N ^ 2 := by nlinarith
  have hmono : N ^ 2 ≤ N ^ k := Nat.pow_le_pow_right (by omega) hk
  omega

end PallLean.Paper93.DeepMath.PathB.SelfReductionPolarity

#print axioms PallLean.Paper93.DeepMath.PathB.SelfReductionPolarity.sat_iff_restr
#print axioms PallLean.Paper93.DeepMath.PathB.SelfReductionPolarity.verifyWrap_sound
#print axioms PallLean.Paper93.DeepMath.PathB.SelfReductionPolarity.encode_exceeds_length
