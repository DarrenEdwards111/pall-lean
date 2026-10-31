import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRavelWedge

/-!
# The observer‑centric Williams hybrid — N‑frame geometry + Williams engine, as one theorem

Native Williams is not observer‑centric.  But the hybrid is exactly: **N‑frame supplies the geometry**
(low‑action ⇒ a structured separator), and **Williams supplies the lower‑bound engine** (a separator ⇒ a fast
algorithm ⇒ a hierarchy contradiction).  This file states that composition as a single proved object.

## Proved (clean axioms, no `sorry`)

* `observer_centric_williams` — `(raveling: low‑action ⇒ in K) + (separatorSpeedup: a separator in K ⇒ fast
  SAT) + (hierarchy: fast SAT ⇒ collapse) + (noCollapse: the hierarchy theorem)` ⇒ **no observer is both
  low‑action and SAT‑correct.**  The two engines compose: raveling extracts the separator, Williams cashes it
  out against the hierarchy.

## The four inputs, and which are open

* `raveling` (low‑action ⇒ separator in `K`) — **provable for restricted `K`**; this corpus proves it
  (`adaptive_bottleneck_exists` + the residual‑non‑collapse classes).  The N‑frame geometry half.
* `separatorSpeedup` (a structured separator ⇒ a fast SAT algorithm) — **partly supplied by the framework**:
  a low‑boundary separator *is* a DP algorithm (`dpSat_beats_bruteforce`) with savings `n − r = Ω(n)`
  (`margin_le_of_correct`).  Needs the separator to compress witnesses for a *decision‑hard* family (open).
* `hierarchy` (fast SAT ⇒ class collapse) and `noCollapse` (the nondeterministic time hierarchy) — the **deep
  external Williams theorems**; `noCollapse` is real/provable (the teeth), `hierarchy` is Williams' algorithmic
  argument.

So the hybrid is the right architecture and it is *proved as a composition*; its open content is exactly the
two inputs the field is stuck on — a decision‑hard compressing family (for `separatorSpeedup`) and the NEXP→NP
descent (for `hierarchy`/`noCollapse` to bite at the polynomial level).  Not circular (the composition is real
logic); not a proof of the separation.
-/

namespace PallLean.Paper93.DeepMath.PathB.ObserverWilliams

variable {Obs : Type*}

/-- **The observer‑centric Williams hybrid (proved).**  Compose the N‑frame geometry (`raveling`: a low‑action
observer factors through a structured separator class `K`) with the Williams engine (`separatorSpeedup`: a
separator in `K` yields a fast SAT algorithm; `hierarchy`: that collapses a class; `noCollapse`: the time
hierarchy forbids it).  Conclusion: **no observer is both low‑action and SAT‑correct** — the separation in
observer form, conditional on the four inputs. -/
theorem observer_centric_williams (lowAction correctSAT inK : Obs → Prop) (fastSat collapse : Prop)
    (raveling : ∀ o, lowAction o → inK o)
    (separatorSpeedup : (∃ o, inK o ∧ correctSAT o) → fastSat)
    (hierarchy : fastSat → collapse)
    (noCollapse : ¬ collapse) :
    ∀ o, ¬ (lowAction o ∧ correctSAT o) :=
  fun o h => noCollapse (hierarchy (separatorSpeedup ⟨o, raveling o h.1, h.2⟩))

end PallLean.Paper93.DeepMath.PathB.ObserverWilliams

#print axioms PallLean.Paper93.DeepMath.PathB.ObserverWilliams.observer_centric_williams
