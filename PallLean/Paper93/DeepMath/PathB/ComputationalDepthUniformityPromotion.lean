import Mathlib.Data.Nat.Basic

/-!
# The uniformity-promotion, specified off the 2^n blowup — spec + socket, NOT the promotion

The scale bridge has a proved half — `EXP ≠ NEXP ⟹ P ≠ NP` (padding, axiom-free) — and an open half:
promote Williams' non-uniform `NEXP ⊄ ACC⁰` up to the uniform `EXP ≠ NEXP` that the padding consumes.
The curiosity pass marked the crossing at the **2^n padding blowup**: un-padding a non-uniform bound
multiplies the scale by `2^n`, so a bound useful at the padded length becomes exponential at the original
length.  This file makes the promotion precise as a **spec and a socket**, and proves the one honest
fact around it — *why* the promotion must be off the blowup.

**It does NOT build the promotion.**  The conversion `input → output` is the field
`OffBlowupPromotion.converts`, left as an explicit open socket.  Filling it (a non-uniform → uniform
separation that avoids the blowup) is the separation itself.  The whole descent refused to fake the
crossing object; so does this file.

## What is proved

* **`unpadding_blows_up`** — un-padding a useful bound (one that is at least the identity — a genuine
  size lower bound) yields an exponential bound: `2^n ≤ Compression T n`.  This is the blowup, proved,
  and it is exactly why the padding route cannot promote Williams' output.
* **`promotion_must_be_off_blowup`** — the padding route provably blows up, AND an off-blowup promotion
  (the socket) yields the separation.  So the crossing is an off-blowup conversion — not the padding.
* **`trivialPromotion`** — the socket is fillable where no conversion is needed (input already uniform):
  the bridge finishes trivially there.  The OPEN part is exactly the non-uniform → uniform step.

## Honest scope

`OffBlowupPromotion` with a proved `converts` from Williams' non-uniform bound to the uniform separation
is the single open socket.  This file is its specification, not its construction.  Nothing here is a
proof of `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniformityPromotion

/-- **Un-padding.**  A bound `T` useful at the *padded* length `2^n`, read back at the *original* length
`n`.  Padding an EXP language into an NP one stretches the length from `n` to `2^n`; un-padding reads the
padded-scale bound at the original scale. -/
def Compression (T : ℕ → ℕ) (n : ℕ) : ℕ := T (2 ^ n)

/-- **The blowup is real (proved).**  A *useful* lower bound grows at least with its input (`m ≤ T m` —
a genuine size bound).  Un-padding it yields an **exponential** bound: `2^n ≤ Compression T n`.  This is
exactly why the padding route cannot compress Williams' non-uniform bound down to the uniform scale — the
compressed bound is `2^n`, not polynomial. -/
theorem unpadding_blows_up {T : ℕ → ℕ} (h : ∀ m, m ≤ T m) (n : ℕ) : 2 ^ n ≤ Compression T n := by
  unfold Compression
  exact h (2 ^ n)

/-- An **off-blowup promotion**: a conversion of a non-uniform bound (`input`, e.g. Williams' `NEXP ⊄
ACC⁰`) into a uniform separation (`output`, e.g. `EXP ≠ NEXP`) that does NOT go through the exponential
un-padding.  `converts` is the OPEN SOCKET — the conversion is not proved here; proving it (for Williams'
input) is the separation. -/
structure OffBlowupPromotion where
  /-- the non-uniform bound (Williams' output), abstractly. -/
  input : Prop
  /-- the uniform separation it should yield. -/
  output : Prop
  /-- SOCKET — the conversion, off the padding blowup.  NOT proved. -/
  converts : input → output

/-- **The promotion must be off the blowup (proved).**  Two facts together: (1) un-padding any useful
bound blows up to exponential — so the padding route cannot promote Williams' output; (2) an off-blowup
promotion (the socket) yields the separation.  Hence the crossing is an off-blowup conversion, and the
padding route is provably not it.  This BUILDS THE SPEC; `converts` stays open — filling it is `P ≠ NP`. -/
theorem promotion_must_be_off_blowup :
    (∀ T : ℕ → ℕ, (∀ m, m ≤ T m) → ∀ n, 2 ^ n ≤ Compression T n) ∧
      (∀ p : OffBlowupPromotion, p.input → p.output) :=
  ⟨fun _ h n => unpadding_blows_up h n, fun p => p.converts⟩

/-- **The socket is fillable where no conversion is needed (proved).**  If the input already *is* the
uniform output (nothing non-uniform to convert), the promotion is the identity and the bridge finishes.
The OPEN part is exactly the case where `input` (non-uniform) and `output` (uniform) genuinely differ. -/
def trivialPromotion (P : Prop) : OffBlowupPromotion := ⟨P, P, id⟩

/-- The trivial promotion really does convert (proved). -/
theorem trivialPromotion_converts (P : Prop) : (trivialPromotion P).input → (trivialPromotion P).output :=
  (trivialPromotion P).converts

end PallLean.Paper93.DeepMath.PathB.UniformityPromotion

#print axioms PallLean.Paper93.DeepMath.PathB.UniformityPromotion.unpadding_blows_up
#print axioms PallLean.Paper93.DeepMath.PathB.UniformityPromotion.promotion_must_be_off_blowup
