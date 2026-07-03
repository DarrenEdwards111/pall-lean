import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameAntiNatural

/-!
# N-Frame: scoping the MCSP / incompressibility-flavoured invariant

The anti-natural-proofs file showed a winning invariant must be non-constructive or non-large.  The canonical
*non-constructive* candidate is the **minimum-description-size** invariant — MCSP / circuit complexity / Kolmogorov
complexity: `mcsp f` = the least size of a representation (circuit, program) computing `f`.  It clears the natural-proofs
barrier (computing it is not known to be efficient) and it is trivially *useful* (high `mcsp` ⇒ small circuits cannot
compute `f`).  This file scopes it — and pins down, as a theorem, whether it escapes the circularity trap.

We model the representation class abstractly: a type `Rep` with a `semantics : Rep → truth table` and a `size : Rep → ℕ`.

  `sizeClass s` — the functions with a description of size `≤ s` (the model's analogue of `SIZE(s)` / `P/poly`).
  `mcsp f` — the least description size of `f`.
  `sizeClass_iff_mcsp_le` — **PROVED**: `f` has a small description iff `mcsp f ≤ s`.
  `mcsp_gap_iff_not_sizeClass` — **PROVED, THE circularity**: `s < mcsp f  ↔  f ∉ sizeClass s`.  The MCSP *gap* is
        *identical* to class non-membership — proving the gap for a target **is** proving the separation.
  `mcsp_useful` — **PROVED**: the high-`mcsp` property is useful against `sizeClass s` — as expected of the canonical
        anti-natural invariant.

## Honest scope — it clears one barrier and lands squarely in the other trap

`mcsp` is genuinely anti-natural: it is non-constructive, so Razborov–Rudich does not forbid it (and being both *useful*
and *large* — most functions are incompressible, by counting — it is *forced* to be non-constructive, consistently).  So
it passes the screen `bdry`/sensitivity failed.  But `mcsp_gap_iff_not_sizeClass` shows it lands exactly in the
**circularity trap** the anti-natural file flagged: the invariant *is* the class complement.  Its "gap" carries no
independent content — establishing `s < mcsp target` is verbatim the separation `target ∉ sizeClass s`.  So `mcsp` is not
a *route*; it is the destination restated.

The one non-circular hope for MCSP-flavoured invariants is **hardness magnification** — that a *weak* lower bound on `mcsp`
itself magnifies to a strong one.  But that reduction is itself `P ≠ NP`-strength (in this repo's own audit, the
hardness-magnification package was proved *equivalent* to `MCSP`/`MINKT`-hardness, i.e. to `¬SAT ∈ P` — repackaging that
does not reduce the strength).  So the incompressibility candidate clears natural proofs only to reproduce the full
problem.  This file formalises that verdict; it does **not** produce a separating invariant.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameMCSP

open PallLean.Paper93.DeepMath.PathB.NFrameAntiNatural (BoolFn FnProperty Useful)

variable {n : ℕ} {Rep : Type*} (semantics : Rep → BoolFn n) (size : Rep → ℕ)

/-- The functions computed by a description of size `≤ s` — the model's `SIZE(s)`. -/
def sizeClass (s : ℕ) : FnProperty n := fun f => ∃ r, semantics r = f ∧ size r ≤ s

/-- The minimum description size (MCSP / circuit complexity / Kolmogorov complexity) of `f`. -/
noncomputable def mcsp (f : BoolFn n) : ℕ := sInf {m | ∃ r, semantics r = f ∧ size r = m}

/-- **Small description iff small `mcsp` (proved).** -/
theorem sizeClass_iff_mcsp_le (hsurj : ∀ f, ∃ r, semantics r = f) (s : ℕ) (f : BoolFn n) :
    sizeClass semantics size s f ↔ mcsp semantics size f ≤ s := by
  constructor
  · rintro ⟨r, hr, hs⟩
    exact le_trans (Nat.sInf_le ⟨r, hr, rfl⟩) hs
  · intro h
    have hne : {m | ∃ r, semantics r = f ∧ size r = m}.Nonempty := by
      obtain ⟨r0, hr0⟩ := hsurj f
      exact ⟨size r0, r0, hr0, rfl⟩
    obtain ⟨r, hr, hsz⟩ := Nat.sInf_mem hne
    exact ⟨r, hr, by rw [hsz]; exact h⟩

/-- **The circularity (proved).**  The MCSP *gap* `s < mcsp f` is *identical* to non-membership `f ∉ sizeClass s`.  The
invariant is the class complement: its gap for a target **is** the separation, carrying no independent content. -/
theorem mcsp_gap_iff_not_sizeClass (hsurj : ∀ f, ∃ r, semantics r = f) (s : ℕ) (f : BoolFn n) :
    s < mcsp semantics size f ↔ ¬ sizeClass semantics size s f := by
  rw [sizeClass_iff_mcsp_le semantics size hsurj, not_le]

/-- **The high-`mcsp` property is useful (proved).**  As the canonical anti-natural invariant should be — but by the
circularity above, its usefulness is definitional, not derived. -/
theorem mcsp_useful (hsurj : ∀ f, ∃ r, semantics r = f) (s : ℕ) :
    Useful (fun f => s < mcsp semantics size f) (sizeClass semantics size s) :=
  fun f hf => (mcsp_gap_iff_not_sizeClass semantics size hsurj s f).mp hf

end PallLean.Paper93.DeepMath.PathB.NFrameMCSP

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameMCSP.mcsp_gap_iff_not_sizeClass
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameMCSP.mcsp_useful
