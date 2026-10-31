import PallLean.GodMoveReal
import PallLean.ProfileCompression
import PallLean.PaperFaithfulSeparation
import PallLean.WithinProfileBound

/-!
# The P-side dome-interior collapse at `timeBound ≤ 4` is FALSE, refuted by the paper's own NP-side

Asked to prove the P-side dome-interior collapse for `timeBound ≤ 4`: that every compiled `timeBound ≤ 4`
machine has *polynomial* SPDP rank (`≤ n^200`) at `κ,ℓ = Θ(log n)`.  I did not prove it, because **it is false**,
and I can prove that it is false from two theorems already in the repo — both about the *same* natural number.

**The two bounds are on the same object.**
`GodMoveReal.compiled_np_lower_bound_any_dtm` (proved, kernel-clean `[propext, Classical.choice, Quot.sound]`)
and `ProfileCompression.p_side_rank_bound_for_cook_levin_of_exactWithinProfileLemma` (the P-side collapse,
conditional on the socket `WithinProfileBound.CookLevinExactWithinProfileFinrankLemma`) both bound the *same*
expression

`mlBlockedSpdpRank (cook_levin_compilation M n _ htb hns).partition (log n) (log n) (compiledPoly …)`

for the *same* `timeBound ≤ 4` machine `M`.  The NP-side proves it is `≥ C(n/3, log n)`; the P-side collapse
would make it `≤ n^200`.

**The sandwich is impossible.**  `PaperFaithfulSeparation.no_rank_sandwich_at_large_n` proves that for
`n ≥ 2^804` no natural number is both `≥ C(n/3, log n)` and `≤ n^200` (because `C(n/3, log n) = n^{Ω(log n)}`
strictly exceeds `n^200` at that scale).  So the P-side collapse conclusion contradicts the NP-side lower bound
directly: the socket `CookLevinExactWithinProfileFinrankLemma` is **false** for every `timeBound ≤ 4` machine at
`n ≥ 2^804` (`p_side_collapse_socket_false`), and the collapse conclusion `rank ≤ n^200` is unsatisfiable for
any such machine (`p_side_collapse_conclusion_false`).

**What this means.**  The compilation `cook_levin_compilation` assigns superpolynomial SPDP rank to *every*
machine in the `timeBound ≤ 4` class — the identity minor is baked into the compiled object regardless of `M`.
So on the *raw* compiled object there is no P/NP gap to collapse: the "P-side dome" is empty at
`timeBound ≤ 4`.  A separation would need the God-Move projection `Π⋆` to lower the rank for P-workloads while
preserving it for the witness — but that extraction is the unproved hypothesis (`AmplituhedronGaugeHyp` /
`Theorem207WitnessHyp`), not a theorem.  Proving the P-side collapse on the raw object, as asked, is proving a
falsehood.

## What is proved

* **`p_side_collapse_socket_false`** — for every `timeBound ≤ 4` machine at `n ≥ 2^804`, the P-side collapse
  socket `CookLevinExactWithinProfileFinrankLemma` is false.
* **`p_side_collapse_conclusion_false`** — the collapse conclusion itself (`rank ≤ n^200`) is unsatisfiable for
  any such machine: the compiled rank strictly exceeds `n^200`.

## Honest verdict — the request is to prove a falsehood; I proved it is false instead

The P-side dome-interior collapse at `timeBound ≤ 4` cannot be proved because it contradicts the paper's own
kernel-clean NP-side lower bound on the identical object.  Both `compiled_np_lower_bound_any_dtm` (NP-side,
`≥ C(n/3, log n)`) and the P-side collapse (`≤ n^200`) constrain the *same* `mlBlockedSpdpRank`, and
`no_rank_sandwich_at_large_n` proves those two bounds cannot both hold at `n ≥ 2^804`.  Hence the collapse
socket is false (`p_side_collapse_socket_false`) and the collapse conclusion is unsatisfiable
(`p_side_collapse_conclusion_false`).  The raw compilation gives every `timeBound ≤ 4` machine superpolynomial
rank, so the P-side dome is empty at that scale and the separation, if it exists, must live in the unproved
`Π⋆` extraction — not in a raw-object collapse.  I did not manufacture the collapse; I proved it is a
falsehood, using the repo's own theorems.  Nothing here is `P ≠ NP` (nor `P = NP`): it is an internal-consistency
finding about the compilation.
-/

namespace PallLean.PSideDomeCollapseRefuted

open PaperFaithfulSeparation MultilinearSPDP

/-- **The P-side collapse socket is false at `timeBound ≤ 4` (proved).**  If the socket
`CookLevinExactWithinProfileFinrankLemma` held, the P-side theorem would give `rank ≤ n^200`; but the NP-side
theorem gives `rank ≥ C(n/3, log n)` on the same object, and `no_rank_sandwich_at_large_n` forbids both at
`n ≥ 2^804`.  So the socket cannot hold. -/
theorem p_side_collapse_socket_false
    (M : TuringMachine.DTM) (n : ℕ) (hn2 : n ≥ 2) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ¬ WithinProfileBound.CookLevinExactWithinProfileFinrankLemma M n hn2 htb hns := by
  intro hsocket
  have hub := ProfileCompression.p_side_rank_bound_for_cook_levin_of_exactWithinProfileLemma
    M n hn2 htb hns hsocket
  have hlb := GodMoveReal.compiled_np_lower_bound_any_dtm M n hn htb hns
  exact no_rank_sandwich_at_large_n n hn ⟨_, hlb, hub⟩

/-- **The P-side collapse conclusion is unsatisfiable at `timeBound ≤ 4` (proved).**  The compiled SPDP rank of
any `timeBound ≤ 4` machine strictly exceeds `n^200` at `n ≥ 2^804`, so the collapse target `rank ≤ n^200` is
false — the identity minor forces superpolynomial rank on the raw compiled object regardless of `M`. -/
theorem p_side_collapse_conclusion_false
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ¬ mlBlockedSpdpRank
        (cook_levin_compilation M n (by omega : n ≥ 2) htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n (by omega : n ≥ 2) htb hns)) ≤ n ^ 200 := by
  intro hub
  have hlb := GodMoveReal.compiled_np_lower_bound_any_dtm M n hn htb hns
  exact no_rank_sandwich_at_large_n n hn ⟨_, hlb, hub⟩

end PallLean.PSideDomeCollapseRefuted

#print axioms PallLean.PSideDomeCollapseRefuted.p_side_collapse_socket_false
#print axioms PallLean.PSideDomeCollapseRefuted.p_side_collapse_conclusion_false
