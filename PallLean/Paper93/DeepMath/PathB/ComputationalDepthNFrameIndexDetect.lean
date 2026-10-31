import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityEval

/-!
# N-Frame: the index-encoding detection primitive — Route G core

Route G (index-encoding) design rung.  Route F (§F) pinned the `√N` cap to the presence-bit
encoding: an affine literal over `F₂^v` costs `Θ(v)` presence bits, so `N ≥ v²` and
`v ≤ √N`.  Route G encodes each block's literals by INDICES into a fixed rich menu
(`menu : ι → Lit v`, a family PARAMETER, not input) of `M = poly(v)` entries, so a block
costs `O(log v)` input bits and the witness dimension rises to `v = Θ(N / log N) = N^{1−o(1)}`.

The cost is that toggling one index bit performs a MENU-JUMP `ℓ_{idx} → ℓ_{idx'}` — a
nonlinear operation on the input, breaking the presence-bit `decodeBlock`/`xbit` detection.
The detection PRIMITIVE that survives it, proved here:

  `twoPointCount ℓ a₀ u` — the `ZMod 2` count of `ℓ` holding over the two-point set
        `{a₀, a₀ + u}`.
  `twoPointCount_eq_dotp` — **PROVED, THE PRIMITIVE**: `twoPointCount ℓ a₀ u = dotp ℓ.1 u`.
        The two-point parity of ANY affine literal equals its FUNCTIONAL dotted with the
        pin-direction — VALUE-INDEPENDENT (the demanded value `ℓ.2` and base point `a₀`
        drop out entirely, echoing the parity-flip value-independence).
  `twoPoint_detect` — **PROVED**: two menu entries are two-point-distinguished (under a
        line pin `u`) iff their FUNCTIONALS separate against `u` — again independent of
        demanded values and base points.  Toggling an index bit is detectable iff the
        induced menu-functional change is non-orthogonal to `u`.

## Honest scope — the improvement and the hard barrier (assessed on paper, §G)

This raises the detectable witness dimension from `√N` to `N/log N`, improving the
achievable separation from `(2 + Θ(1/√N))N` toward `(2 + Θ(1/log N))N` (super-`√N`, the
first sub-linear-error regime).  But it is CAPPED at `N/log N` by the **fixed-menu barrier**:
spanning `F₂^v` needs `≥ v` menu directions of `≥ log v` index bits each, so `N ≥ v·log v`
and `v = O(N/log N)`.  Detection caps at `v`, so `cbudget ≤ 2N + O(N/log N) = (2 + o(1))N`
by this method.  **Constant `c` in `(2+c)N` is UNREACHABLE for affine `⊕#SAT` families under
N-frame (witness-rank) detection** — a genuine method barrier; constant `c` needs a
non-affine family whose detection is not witness-rank bounded.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameIndexDetect

open PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval

variable {v : ℕ}

/-- The `ZMod 2` count of literal `ℓ` holding over the two-point witness set `{a₀, a₀+u}`. -/
def twoPointCount (ℓ : Lit v) (a₀ u : Fin v → ZMod 2) : ZMod 2 :=
  (if litHolds a₀ ℓ then 1 else 0) + (if litHolds (a₀ + u) ℓ then 1 else 0)

/-- **THE INDEX-DETECTION PRIMITIVE (proved)**: the two-point parity of any affine literal
equals its functional dotted with the pin-direction — value- and base-point-independent. -/
theorem twoPointCount_eq_dotp (ℓ : Lit v) (a₀ u : Fin v → ZMod 2) :
    twoPointCount ℓ a₀ u = dotp ℓ.1 u := by
  have key : ∀ p d β : ZMod 2,
      ((if p = β then (1 : ZMod 2) else 0) + (if p + d = β then 1 else 0)) = d := by
    decide
  have h1 : litHolds a₀ ℓ ↔ (dotp ℓ.1 a₀ = ℓ.2) := Iff.rfl
  have hd : litHolds (a₀ + u) ℓ ↔ (dotp ℓ.1 a₀ + dotp ℓ.1 u = ℓ.2) := by
    unfold litHolds; rw [dotp_add_right]
  unfold twoPointCount
  rw [if_congr h1 rfl rfl, if_congr hd rfl rfl]
  exact key (dotp ℓ.1 a₀) (dotp ℓ.1 u) ℓ.2

/-- **THE DETECTION CRITERION (proved)**: two menu literals are two-point-distinguished under
line-pin `u` iff their functionals separate against `u` — independent of demanded values and
base points.  This is the index-toggle detection rule: toggling an index bit is detectable
iff it moves the selected functional off-orthogonal to `u`. -/
theorem twoPoint_detect (ℓ ℓ' : Lit v) (a₀ a₀' u : Fin v → ZMod 2) :
    twoPointCount ℓ a₀ u ≠ twoPointCount ℓ' a₀' u ↔ dotp ℓ.1 u ≠ dotp ℓ'.1 u := by
  rw [twoPointCount_eq_dotp, twoPointCount_eq_dotp]

/-- **The menu form (proved)**: detection of an index toggle `i → i'` in a fixed menu is a
functional-separation test on the menu, value-independent. -/
theorem menu_toggle_detect {ι : Type*} (menu : ι → Lit v) (i i' : ι)
    (a₀ a₀' u : Fin v → ZMod 2) :
    twoPointCount (menu i) a₀ u ≠ twoPointCount (menu i') a₀' u
      ↔ dotp (menu i).1 u ≠ dotp (menu i').1 u :=
  twoPoint_detect (menu i) (menu i') a₀ a₀' u

end PallLean.Paper93.DeepMath.PathB.NFrameIndexDetect

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameIndexDetect.twoPointCount_eq_dotp
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameIndexDetect.twoPoint_detect
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameIndexDetect.menu_toggle_detect
