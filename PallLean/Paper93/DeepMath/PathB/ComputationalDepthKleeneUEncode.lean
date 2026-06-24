import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneUCode

/-!
# Kleene interpreter project — phase 2: a clean tagged encoding of `UCode` (PROVED)

The dispatch (step 5) must read a code's constructor and recover its subcodes by arithmetic.  We give
`UCode` a **clean tagged encoding** `enc u = Nat.pair tag payload`, where `tag ∈ {0,…,7}` is the
constructor and `payload` holds the subcode encodings — so the dispatch is just `Nat.unpair`:

  `enc` — tagged recursive encoding (`tag`: zero 0, succ 1, left 2, right 3, pair 4, comp 5, prec 6,
    rfind' 7).
  `enc_tag` — `(Nat.unpair (enc u)).1 = enc u`'s constructor tag (per constructor).
  `enc_pair`/`enc_comp`/`enc_prec`/`enc_rfind'` — subcode-recovery: `(unpair payload)` recovers
    `(enc a, enc b)`.
  `enc_injective` — the encoding is faithful.

This is the arithmetic the dispatch `Code` implements: `tag := (unpair e).1`; subcodes from `(unpair e).2`.
Reading the tag and recovering subcodes from this encoding is `Nat.pair`/`unpair` only — far cleaner than
Mathlib's `encodeCode` `brecOn`.

## What is proved (clean axioms, no `sorry`)

* `UCode.enc` — the tagged encoding.
* `enc_tag_*` (per constructor), `enc_*_payload` — tag + subcode recovery.
* `enc_injective` — faithfulness.

## Honest scope

Phase 2: the tagged encoding + recovery arithmetic (the dispatch's data layer).  The dispatch `Code` itself,
the step evaluator, and the fuel recursion remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

/-- Clean tagged encoding: `enc u = Nat.pair tag payload`. -/
def UCode.enc : UCode → ℕ
  | .zero => Nat.pair 0 0
  | .succ => Nat.pair 1 0
  | .left => Nat.pair 2 0
  | .right => Nat.pair 3 0
  | .pair a b => Nat.pair 4 (Nat.pair a.enc b.enc)
  | .comp a b => Nat.pair 5 (Nat.pair a.enc b.enc)
  | .prec a b => Nat.pair 6 (Nat.pair a.enc b.enc)
  | .rfind' a => Nat.pair 7 a.enc

/-- **The constructor tag is `(unpair (enc u)).1` (proved), per constructor.** -/
theorem enc_tag (u : UCode) :
    (Nat.unpair u.enc).1 =
      (match u with
        | .zero => 0 | .succ => 1 | .left => 2 | .right => 3
        | .pair _ _ => 4 | .comp _ _ => 5 | .prec _ _ => 6 | .rfind' _ => 7) := by
  cases u <;> simp [UCode.enc, Nat.unpair_pair]

/-- **`pair` payload recovery (proved).** -/
theorem enc_pair_payload (a b : UCode) :
    (Nat.unpair (Nat.unpair (UCode.pair a b).enc).2) = (a.enc, b.enc) := by
  simp [UCode.enc, Nat.unpair_pair]

/-- **`comp` payload recovery (proved).** -/
theorem enc_comp_payload (a b : UCode) :
    (Nat.unpair (Nat.unpair (UCode.comp a b).enc).2) = (a.enc, b.enc) := by
  simp [UCode.enc, Nat.unpair_pair]

/-- **`prec` payload recovery (proved).** -/
theorem enc_prec_payload (a b : UCode) :
    (Nat.unpair (Nat.unpair (UCode.prec a b).enc).2) = (a.enc, b.enc) := by
  simp [UCode.enc, Nat.unpair_pair]

/-- **`rfind'` payload recovery (proved).** -/
theorem enc_rfind'_payload (a : UCode) :
    (Nat.unpair (UCode.rfind' a).enc).2 = a.enc := by
  simp [UCode.enc, Nat.unpair_pair]

/-- **The tagged encoding is injective (proved).** -/
theorem enc_injective : Function.Injective UCode.enc := by
  intro u v h
  induction u generalizing v with
  | pair a b iha ihb =>
    cases v <;> simp [UCode.enc, Nat.pair_eq_pair] at h <;> try (exact absurd h.1 (by decide))
    obtain ⟨ha, hb⟩ := h
    rw [iha ha, ihb hb]
  | comp a b iha ihb =>
    cases v <;> simp [UCode.enc, Nat.pair_eq_pair] at h <;> try (exact absurd h.1 (by decide))
    obtain ⟨ha, hb⟩ := h
    rw [iha ha, ihb hb]
  | prec a b iha ihb =>
    cases v <;> simp [UCode.enc, Nat.pair_eq_pair] at h <;> try (exact absurd h.1 (by decide))
    obtain ⟨ha, hb⟩ := h
    rw [iha ha, ihb hb]
  | rfind' a iha =>
    cases v <;> simp [UCode.enc, Nat.pair_eq_pair] at h <;> try (exact absurd h.1 (by decide))
    rw [iha h]
  | _ => cases v <;> simp_all [UCode.enc, Nat.pair_eq_pair]

/-!
**Phase 2 proved.**  `UCode.enc` is a clean tagged encoding: the dispatch reads the constructor as
`(unpair e).1` and recovers subcodes by `unpair` — pure `Nat.pair`/`unpair` arithmetic, and the encoding is
injective.  The dispatch `Code` (phase 5) implements exactly this.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.enc_injective
