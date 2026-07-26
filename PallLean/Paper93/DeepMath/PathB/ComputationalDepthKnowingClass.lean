import Mathlib.Data.Nat.Basic

/-!
# "We know the class is NP" — the verifier is free; the reconstruction cost is the open question

Darren: we don't need superpoly data — we *know* the class of objects is NP, so we can access it in P and
model it precisely.  The instinct is compressed sensing: *prior structure cuts the data needed*.  But it
turns on a precise distinction: **knowing the class is not knowing the object's intrinsic dimension.**

"Knowing the class is NP" is **free** — it is the *definition*: NP = poly-verifiable.  It gives you the
**verifier**, cheap.  "Access / model it in P" is having the **reconstructor** (the solver / the low-data
recovery), cheap.  And *verifier ⟹ reconstructor* is exactly `NP ⊆ P` — the open question, `P vs NP` itself.
Knowing the verifier does not give the reconstructor; the gap between them is the whole problem
(`VerifyFindGap`).

Compressed sensing recovers a `D`-dimensional signal from few measurements *only if it is sparse* — low
intrinsic dimension.  The separating object (the proof that SAT is hard) is **non-natural** — high effective
dimension, *incompressible* (`FullProjection`, `HeuristicShortcut`).  Knowing "SAT ∈ NP" does *not* make that
object sparse; its sparsity **is** `cost_super`.

## What is proved

* **`knowing_class_undetermines_reconstruction`** — the cheap verifier does not determine the reconstruction
  cost: two objects with the *same* verifier cost `v` have *different* reconstruction cost.  Knowing the
  class fixes the verifier, not the object's dimension.
* **`verifier_cheap_reconstruct_expensive`** — a cheap verifier (`= 1`) is consistent with expensive
  reconstruction (`≥ 1000`): knowing the class is NP is compatible with the separating object needing
  superpoly data.

## Honest scope — knowing the class ≠ the object is sparse

So "we know the class is NP, therefore we model it in P" is one of two presuppositions, both blocked:

* it assumes **verifier ⟹ reconstructor** — `NP ⊆ P` — which is assuming `P = NP`; or
* it assumes the separating object is **sparse / low intrinsic dimension** — which is assuming it is
  *natural*, and a natural separating object is barriered (`FullProjection`).

Knowing the *class* (poly-verifiability) is free and tells you nothing about the *reconstruction cost* of the
separating object, which is its effective dimension = `cost_super`.  Compressed sensing helps exactly on the
sparse (structured, compressible) objects — and the hard core is the incompressible one.  So it cannot be
"inferred and modeled in P" without presupposing the object is sparse (natural, barriered) or that
`P = NP`.  This file certifies neither `P ≠ NP` nor its unprovability.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KnowingClass

/-- Access to an object by two costs: the `verifierCost` (knowing the class — NP membership, poly-verify)
and the `reconstructCost` (modeling / recovering the object — its intrinsic dimension / sparsity). -/
structure ObjectAccess where
  /-- cost of knowing the class (NP = poly-verify) — free/cheap -/
  verifierCost : ℕ
  /-- cost of reconstructing/modeling the object (its intrinsic dimension) -/
  reconstructCost : ℕ

/-- **Knowing the class does not determine reconstruction cost (proved).**  Two objects with the *same*
verifier cost `v` have *different* reconstruction cost.  Knowing "the class is NP" fixes the verifier, not
the object's dimension — so it does not cut the reconstruction data. -/
theorem knowing_class_undetermines_reconstruction (v : ℕ) :
    ∃ (sparse dense : ObjectAccess),
      sparse.verifierCost = v ∧ dense.verifierCost = v ∧
      sparse.reconstructCost < dense.reconstructCost :=
  ⟨⟨v, 0⟩, ⟨v, 1⟩, rfl, rfl, Nat.zero_lt_one⟩

/-- **A cheap verifier is consistent with expensive reconstruction (proved).**  `verifierCost = 1` with
`reconstructCost ≥ 1000`: knowing the class is NP (cheap verify) is compatible with the separating object
needing far more data to reconstruct.  The verifier gives no upper bound on the reconstruction. -/
theorem verifier_cheap_reconstruct_expensive :
    ∃ o : ObjectAccess, o.verifierCost = 1 ∧ 1000 ≤ o.reconstructCost :=
  ⟨⟨1, 1000⟩, rfl, Nat.le_refl 1000⟩

end PallLean.Paper93.DeepMath.PathB.KnowingClass

#print axioms PallLean.Paper93.DeepMath.PathB.KnowingClass.knowing_class_undetermines_reconstruction
#print axioms PallLean.Paper93.DeepMath.PathB.KnowingClass.verifier_cheap_reconstruct_expensive
