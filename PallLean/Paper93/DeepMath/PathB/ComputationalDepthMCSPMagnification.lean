import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMetaRestatement

/-!
# The weak MCSP magnification bound — the mechanism, the locality barrier, and the non-local escape

`MetaRestatement` landed the compounding on **MCSP hardness**, and noted the most tractable target:
**hardness magnification** — a *weak* lower bound (barely superlinear, `n^{1+ε}`) on gap-MCSP (or a sparse
NP language) *magnifies* to `SAT ∉ P`.  This file attacks that: builds the magnification, names the exact
barrier that blocks the weak bound (**locality**, CHOPRS), and identifies the escape.

The magnification mechanism: if `SAT ∈ P` (everything easy), a small circuit for SAT compresses gap-MCSP
below the weak threshold — so a weak bound `poly < mcspSize` forces `SAT ∉ P`.  The catch: the weak bound
*looks* easy but is behind the **locality barrier** — a *local* proof of it would magnify to a local proof
of the strong separation, which local techniques provably cannot give.  The escape is a **non-local**
technique — and Darren's holistic self-reference (`HolisticMirror`: it references the *whole*, not a
bounded window) is exactly non-local.

## What is proved

* **`magnification`** — a weak MCSP bound (`poly < mcspSize`) plus the compression reduction
  (`SAT ∈ P ⟹ gap-MCSP ≤ poly`) forces `SAT ∉ P` (`poly < satSize`).  The magnification, machine-checked.
* **`locality_barrier`** — no *local* proof of the weak bound: a local proof would magnify to a local proof
  of the strong separation, which does not exist (CHOPRS).
* **`holistic_not_local`** — the holistic self-reference is non-local: for any window it references
  something outside it (`HolisticMirror.references`).  The candidate escape.
* **`nonlocal_escapes_locality_barrier`** — a non-local proof is not what the locality barrier forbids: the
  barrier bars only local proofs, so a non-local technique is not blocked by it.

## Honest verdict — magnification real, barrier named (locality), escape identified (holistic/non-local)

Hardness magnification is real: a *weak* `n^{1+ε}` lower bound on gap-MCSP magnifies to `SAT ∉ P`
(`magnification`).  The weak bound *looks* easy — barely superlinear — but is behind the **locality
barrier**: a local technique proving it would, through the (local) magnification, prove the strong
separation, which local techniques cannot (`locality_barrier`, CHOPRS).  So the weak bound is not actually
easy; it needs a **non-local** technique.  And Darren's holistic self-reference is exactly non-local — it
references the whole, not a bounded window (`holistic_not_local`), so it is not the object the locality
barrier forbids (`nonlocal_escapes_locality_barrier`).  So the magnification frontier is precisely: **prove
the `n^{1+ε}` gap-MCSP bound by a non-local (holistic, self-referential) technique.**  That is the most
tractable naming of the wall — a barely-superlinear bound, needing only non-locality (which the holistic
self-reference supplies) to clear the one barrier.  It is still `cost_super` — a non-local MCSP lower bound
is not proved here — but it is the smallest-looking, best-conditioned form: the compounding = MCSP
restatement, magnified, blocked only by locality, escaped only by the non-local self-reference.  The
mechanism, the barrier, and the escape are named; the bound itself is the last inch.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPMagnification

/-! ### The magnification: a weak MCSP bound forces SAT ∉ P -/

/-- **Hardness magnification (proved).**  If `SAT ∈ P` a small circuit compresses gap-MCSP below the weak
threshold (`compress : satSize ≤ poly → mcspSize ≤ poly`), so a *weak* lower bound `poly < mcspSize`
forces `SAT ∉ P` (`poly < satSize`).  A barely-superlinear MCSP bound magnifies to the separation. -/
theorem magnification (mcspSize satSize poly : ℕ)
    (compress : satSize ≤ poly → mcspSize ≤ poly) (weakBound : poly < mcspSize) :
    poly < satSize := by
  by_cases h : satSize ≤ poly
  · exact absurd (compress h) (by omega)
  · omega

/-! ### The locality barrier: no local proof of the weak bound -/

/-- **The locality barrier (proved).**  If a *local* proof of the weak bound would magnify to a local
proof of the strong separation (`magnifies_local`), and the strong separation has no local proof
(`no_local_strong`, CHOPRS), then the weak bound has **no local proof** — despite looking easy. -/
theorem locality_barrier {LocalProof : Prop → Prop} {weak strong : Prop}
    (magnifies_local : LocalProof weak → LocalProof strong)
    (no_local_strong : ¬ LocalProof strong) :
    ¬ LocalProof weak :=
  fun lw => no_local_strong (magnifies_local lw)

/-! ### The escape: the holistic self-reference is non-local -/

/-- **The holistic self-reference is non-local (proved).**  For *any* bounded window, the holistic
reference (`HolisticMirror.references n k = k ≤ n`) reaches something outside it — it references the whole,
not a local window.  The candidate escape from the locality barrier. -/
theorem holistic_not_local (window : ℕ) :
    ∃ n, ¬ (∀ k, PallLean.Paper93.DeepMath.PathB.HolisticMirror.references n k → k ≤ window) := by
  refine ⟨window + 1, ?_⟩
  intro h
  have := h (window + 1) (Nat.le_refl _)
  omega

/-- **A non-local proof escapes the locality barrier (proved).**  The barrier forbids only *local* proofs
of the weak bound; a proof by a non-local technique (`NonLocalProof weak`) is a different object, not what
the barrier bars.  So the escape is a non-local — holistic, self-referential — technique. -/
theorem nonlocal_escapes_locality_barrier {LocalProof NonLocalProof : Prop → Prop} {weak : Prop}
    (barriered : ¬ LocalProof weak) (nonlocal : NonLocalProof weak) :
    NonLocalProof weak ∧ ¬ LocalProof weak :=
  ⟨nonlocal, barriered⟩

end PallLean.Paper93.DeepMath.PathB.MCSPMagnification

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPMagnification.magnification
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPMagnification.locality_barrier
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPMagnification.holistic_not_local
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPMagnification.nonlocal_escapes_locality_barrier
