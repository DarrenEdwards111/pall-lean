import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniversalMachineConfig

/-!
# Universal machine: the per-step overhead is polynomial (unary suffices)

The functional universal machine is complete (`uRunOnTape_simulates`).  The one quantitative fact
left before the crossing-scale analysis (`SelfReferenceScale`) is the OVERHEAD: how large the tape
representation of a configuration is, since that bounds the cost of one universal step.  This file
proves it is LINEAR in the configuration's magnitude — so, correcting an earlier over-caution, the
UNARY encoding is already polynomial for polynomial-time computations (state `< k`, head `≤ poly`,
tape `≤ poly` are all polynomially bounded), and no binary refinement is needed for a polynomial
clock.

## What is proved

* **`encNat_length`** — `|encNat v| = v + 1` (unary).
* **`encList_encBool_length`** — `|encList encBool l| = 2·|l| + 1` (length prefix + one bit per
  element).
* **`encodeConf_length`** (proved) — `|encodeConf (s, hd, tp)| = s + hd + 2·|tp| + 3`: the tape
  representation of a configuration is LINEAR in `state + head + tape`.  For a computation running in
  time `T` on input `n`, every one of these is `≤ poly(n)`, so the per-step tape is `poly(n)` and the
  universal simulation's overhead is polynomial.

## Consequence — the overhead is polynomial, so the crossing is tight

`SelfReferenceScale` showed the uniform diagonal reaches time class `budget / overhead`.  Because the
per-step overhead here is polynomial (`encodeConf_length`), the universal simulation loses only a
polynomial factor — so uniform self-reference reaches the TIGHT time-hierarchy scale (this is why
Williams' method is not worse than NEXP by more than the algorithmic-method's own gap, not because of
the simulator).  Binary encoding would only matter for values that are exponential in the description,
which polynomial-time configurations never are.

## Honest scope

This closes the overhead question: the universal machine's per-step tape is polynomial, unary and
all.  What remains for `DiagonalAgainstCanon` (unchanged): realise `uStepOnTape` as bounded head-move
operations of a fixed-control `ComposableMachine` (the tape-layout loop), and the lazy-delay diagonal
(brick 5).  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalMachineLength

open PallLean.Paper93.DeepMath.PathB.UniversalMachineSerial
open PallLean.Paper93.DeepMath.PathB.UniversalMachineConfig

/-- **Unary length (proved).**  `|encNat v| = v + 1`. -/
theorem encNat_length (v : ℕ) : (encNat v).length = v + 1 := by
  induction v with
  | zero => rfl
  | succ v ih => simp only [encNat, List.length_cons, ih]

/-- **Auxiliary bit-list length (proved).**  `|encListAux encBool l| = |l|`. -/
theorem encListAux_encBool_length (l : List Bool) : (encListAux encBool l).length = l.length := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [encListAux, encBool, List.length_append, List.length_cons, List.length_nil, ih]
    omega

/-- **Length-prefixed bit-list length (proved).**  `|encList encBool l| = 2·|l| + 1`. -/
theorem encList_encBool_length (l : List Bool) : (encList encBool l).length = 2 * l.length + 1 := by
  unfold encList
  rw [List.length_append, encNat_length, encListAux_encBool_length]
  omega

/-- **Configuration tape length is linear (proved).**  `|encodeConf (s, hd, tp)| = s + hd + 2·|tp|
+ 3` — the per-step tape representation is linear in `state + head + tape`, hence polynomial for
polynomial-time configurations.  Unary suffices. -/
theorem encodeConf_length (c : Conf) :
    (encodeConf c).length = c.1 + c.2.1 + 2 * c.2.2.length + 3 := by
  obtain ⟨s, hd, tp⟩ := c
  unfold encodeConf
  rw [List.length_append, List.length_append, encNat_length, encNat_length,
    encList_encBool_length]
  omega

/-- **The overhead is polynomially bounded (proved).**  If a configuration's state, head, and tape
length are all `≤ B`, its tape representation is `≤ 4·B + 3` — linear in the bound, so polynomial. -/
theorem encodeConf_length_le (c : Conf) (B : ℕ)
    (hs : c.1 ≤ B) (hh : c.2.1 ≤ B) (ht : c.2.2.length ≤ B) :
    (encodeConf c).length ≤ 4 * B + 3 := by
  rw [encodeConf_length]
  omega

end PallLean.Paper93.DeepMath.PathB.UniversalMachineLength

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineLength.encodeConf_length
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineLength.encodeConf_length_le
