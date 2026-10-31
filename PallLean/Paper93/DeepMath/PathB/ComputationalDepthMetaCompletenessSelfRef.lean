/-!
# Attacking the completeness socket via self-reference: it needs MCSP ≤ SAT, not SAT ≤ MCSP

`MagnifiedMetaTrigger` left `completeness` (a superpolynomial bound on the meta-target ⟹ `SAT ∉ P`) as
a socket I flagged **DUBIOUS**, on the ground that "MCSP is not known NP-hard."  Attacking it via
self-reference shows that flag was **too strong** — it conflated two opposite reduction directions:

* **Direction A — `SAT ≤ MCSP` (MCSP is NP-hard).**  This is the famous OPEN problem
  (Kabanets–Cai, Murray–Williams barriers).  It is what you would need to conclude *SAT easy ⟹ MCSP
  easy* — and it is genuinely dubious.
* **Direction B — `MCSP ≤ SAT` (MCSP ∈ NP).**  This is what completeness ACTUALLY needs: *MCSP hard ⟹
  SAT hard*.  And it is a **theorem**, because MCSP ∈ NP: its witness is a *circuit*, verified by
  *evaluation* — exactly the self-referential circuit-evaluation that SAT expresses via Tseitin /
  Cook–Levin (`TriggerAnatomy` already proves this NP-witness shape for the concrete `mcspAt`).

So self-reference **discharges** the completeness socket: `MCSP ∈ NP` (self-reference) + Cook–Levin
(`SAT` NP-complete) give `MCSP ≤ SAT`, hence `MCSP ∉ P ⟹ SAT ∉ P`.  No NP-hardness of MCSP is used.

## What is proved

* **`hard_transfer`** — a reduction `A ≤ B` transfers hardness: `A ∉ P ⟹ B ∉ P`.
* **`mcsp_le_sat_of_inNP`** — `MCSP ∈ NP` gives the reduction `MCSP ≤ SAT` (via Cook–Levin, the
  `cookLevin` field): the self-referential direction.
* **`meta_completeness`** — the discharge: `MCSP ∈ NP` + `MCSP ∉ P` ⟹ `SAT ∉ P`.  Uses only the
  `InNP` (direction-B) fact, never `NPHard` (direction A).
* **`completeness_needs_only_inNP`** — the correction stated plainly: completeness follows from
  `InNP mcsp` alone.
* **`toyNPWorld`** — a consistency witness (the `NPWorld` structure is inhabited).

## Honest scope

For the **decision** problem MCSP, completeness is discharged — the self-referential reduction is real,
and my earlier "dubious" flag is corrected.  What stays genuinely open in the magnification route is
therefore **not** completeness but (i) the weak `n^{1+ε}` bound (behind the locality barrier) and
(ii) the `SelfImproving` anti-checker.  Residual subtleties I do not claim to have closed: gap/promise
versions of MCSP and the `MKtP` (Kolmogorov) target have their own reduction caveats; the clean
discharge here is for MCSP-decision with an explicit truth table.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MetaCompletenessSelfRef

/-- `Easy L` means `L` is decidable in polynomial time.  A polynomial reduction `A ≤ B` has the
operational content: if `B` is easy then `A` is easy. -/
def PolyReduces {Problem : Type} (Easy : Problem → Prop) (A B : Problem) : Prop :=
  Easy B → Easy A

/-- **Hardness transfers along a reduction (proved).**  If `A ≤ B` and `A ∉ P`, then `B ∉ P`. -/
theorem hard_transfer {Problem : Type} (Easy : Problem → Prop) (A B : Problem)
    (h : PolyReduces Easy A B) (hA : ¬ Easy A) : ¬ Easy B :=
  fun hB => hA (h hB)

/-- An **NP world**: an easiness predicate, an `InNP` predicate, and `SAT` as an NP-complete problem
(`cookLevin`: every NP problem reduces to `SAT`). -/
structure NPWorld (Problem : Type) where
  Easy : Problem → Prop
  InNP : Problem → Prop
  sat : Problem
  sat_inNP : InNP sat
  /-- **Cook–Levin**: `SAT` is NP-complete — every NP language reduces to it. -/
  cookLevin : ∀ A, InNP A → PolyReduces Easy A sat

/-- **MCSP is NP-hard** — direction A (`SAT ≤ MCSP`): every NP problem reduces to MCSP.  This is the
OPEN problem; it is NOT used below. -/
def NPHard {Problem : Type} (W : NPWorld Problem) (M : Problem) : Prop :=
  ∀ B, W.InNP B → PolyReduces W.Easy B M

/-- **The self-referential reduction `MCSP ≤ SAT` (proved).**  From `MCSP ∈ NP` and Cook–Levin.
`MCSP ∈ NP` because its witness is a circuit verified by evaluation — the self-reference. -/
theorem mcsp_le_sat_of_inNP {Problem : Type} (W : NPWorld Problem) (mcsp : Problem)
    (h_inNP : W.InNP mcsp) : PolyReduces W.Easy mcsp W.sat :=
  W.cookLevin mcsp h_inNP

/-- **The completeness socket, discharged via self-reference (proved).**  `MCSP ∈ NP` + `MCSP ∉ P`
⟹ `SAT ∉ P`.  Uses only `InNP mcsp` (direction B) and Cook–Levin — never `NPHard mcsp` (direction A,
the open problem). -/
theorem meta_completeness {Problem : Type} (W : NPWorld Problem) (mcsp : Problem)
    (h_inNP : W.InNP mcsp) (hHard : ¬ W.Easy mcsp) : ¬ W.Easy W.sat :=
  hard_transfer W.Easy mcsp W.sat (mcsp_le_sat_of_inNP W mcsp h_inNP) hHard

/-- **The correction, stated plainly (proved).**  Completeness follows from `InNP mcsp` alone — the
easy, self-referential direction — with no appeal to the open NP-hardness of MCSP. -/
theorem completeness_needs_only_inNP {Problem : Type} (W : NPWorld Problem) (mcsp : Problem)
    (h_inNP : W.InNP mcsp) : ¬ W.Easy mcsp → ¬ W.Easy W.sat :=
  meta_completeness W mcsp h_inNP

/-- A consistency witness: the `NPWorld` structure is inhabited. -/
def toyNPWorld : NPWorld Unit where
  Easy := fun _ => True
  InNP := fun _ => True
  sat := ()
  sat_inNP := trivial
  cookLevin := fun _ _ => fun _ => trivial

end PallLean.Paper93.DeepMath.PathB.MetaCompletenessSelfRef

#print axioms PallLean.Paper93.DeepMath.PathB.MetaCompletenessSelfRef.hard_transfer
#print axioms PallLean.Paper93.DeepMath.PathB.MetaCompletenessSelfRef.mcsp_le_sat_of_inNP
#print axioms PallLean.Paper93.DeepMath.PathB.MetaCompletenessSelfRef.meta_completeness
#print axioms PallLean.Paper93.DeepMath.PathB.MetaCompletenessSelfRef.completeness_needs_only_inNP
