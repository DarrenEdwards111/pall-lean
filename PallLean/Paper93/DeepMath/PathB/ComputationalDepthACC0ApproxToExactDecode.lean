import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PolyToSymAnd

/-!
# The Beigel–Tarui approximate→exact conversion: the socket, and the decoding mechanism (toy)

The bottom-clause no-go (`…ACC0ExactDegreeNoGo`) proved the *naive* route impossible: an exact, unbounded-fan-in
`OR`/`AND` over `F₂` has degree = fan-in, so no single exact low-degree polynomial per gate.  The only route left is
the genuine Beigel–Tarui move: take *approximate* low-degree representations and recover the *exact* value by a
**symmetric/count decoder** over several of them.  This file makes that route explicit and proves its decoding core.

Two pieces:

1. **The socket `ApproxToExactSymmetricDecode`** — the missing theorem, named explicitly: the target `f` is the
   *exact* symmetric (count) decode of `r` **low-degree** gates.  Crucially this is **non-trivial only because of the
   low-degree clause**: without it the socket is trivially true (take `r` copies of `f`); *with* it, the socket
   holding for an arbitrary `ACC⁰` `f` (with `r` quasipolynomial, degree `D` polylog) **is** Wall 1.

2. **The decoding mechanism `majority_decode` (toy, proved)** — error-corrected symmetric decoding: if a *majority* of
   the `r` approximants agree with `f` at every point, then `f` is *exactly* the threshold-count
   `[> r/2 \text{ are } 1]` of them — a symmetric function.  This proves the `exact` clause of the socket *given*
   majority-correct approximants; the open part is producing **low-degree** approximants that are majority-correct
   everywhere (the BT/Yao probabilistic construction).

```
no-go:   exact low-degree per gate          IMPOSSIBLE  (…ACC0ExactDegreeNoGo)
socket:  f = symmetric decode of low-deg gates   = Wall 1 (low-degree clause load-bearing)
toy:     majority-correct ⇒ exact threshold decode   PROVED  (the decoding half)
open:    low-degree approximants, majority-correct everywhere   = the BT construction (Wall 1)
```

## What is proved (clean axioms, no `sorry`)

* `IsLowDegreeGate` / `ApproxToExactSymmetricDecode` — the low-degree-gate predicate and the BT conversion socket.
* `socket_searchable` — the socket cash-out: `f` is the exact symmetric decode of `r` gates ⇒ SAT-searchable in
  `≤ r+1` cells (once `r+1 < 2^n`).
* `majority_decode` — error-corrected decoding: majority-correct at every point ⇒ `f x = [> r/2 of the gates are 1]`.
* `majority_decode_symmetric` — hence `f` is *exactly* a symmetric (threshold-count) function of the approximants.
* `majority_decode_gives_socket` — low-degree **and** majority-correct approximants ⇒ the socket holds (the toy
  discharges `exact`; low-degree is the open clause).

## Honest scope

The decoding mechanism is genuinely proved — symmetric threshold count *does* recover the exact value under controlled
error.  What is **not** proved (and not faked) is the construction the socket abstracts: that an arbitrary `ACC⁰`
function admits `r = quasipoly` **low-degree** approximants that are majority-correct at *every* one of the `2^n`
points.  That is the irreducible Beigel–Tarui analytic core — **Wall 1**.  Still the cell/observer model; `< 2^n`
cells is not a uniform algorithm (Wall 2).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md` and
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ApproxToExactDecode

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd

variable {n r : ℕ}

/-- A **low-degree gate**: a symmetric function of monomial-`AND`s of fan-in `≤ D` (a degree-`≤D` polynomial-style
gate).  The no-go (`…ACC0ExactDegreeNoGo`) shows an unbounded-fan-in `AND`/`OR` is *not* such a gate exactly; the BT
route uses these as *approximants*. -/
def IsLowDegreeGate (D : ℕ) (g : (Fin n → Bool) → Bool) : Prop :=
  ∃ (m : ℕ) (mono : Fin m → Finset (Fin n)) (h : ℕ → Bool),
    (∀ j, (mono j).card ≤ D) ∧ g = symEval (fun j x => monoAND (mono j) x) h

/-- **The Beigel–Tarui conversion socket (the missing theorem, made explicit).**  `f` is the *exact* symmetric (count)
decode of `r` **low-degree** gates.  Non-trivial only because of the low-degree clause: without it, `r` copies of `f`
satisfy it; with it, this holding for arbitrary `ACC⁰` `f` (with `r` quasipoly, `D` polylog) **is** Wall 1. -/
def ApproxToExactSymmetricDecode (D r : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (g : Fin r → (Fin n → Bool) → Bool) (decoder : ℕ → Bool),
    (∀ i, IsLowDegreeGate D (g i)) ∧ f = symEval g decoder

/-- **Socket cash-out (proved): the BT conversion ⇒ SAT-searchable in `≤ r+1` cells.**  The exact symmetric decode is
observed by the count of the `r` gates — the `SYM` top collapses the boundary to `r+1`. -/
theorem socket_searchable {D : ℕ} (f : (Fin n → Bool) → Bool)
    (hsock : ApproxToExactSymmetricDecode D r f) (hr : r + 1 < 2 ^ n) :
    ∃ (g : Fin r → (Fin n → Bool) → Bool) (decoder : ℕ → Bool),
      f = symEval g decoder
        ∧ (Satisfiable f ↔ ∃ c ∈ Finset.univ.image (gateCount g), decoder c = true)
        ∧ (Finset.univ.image (gateCount g)).card < 2 ^ n := by
  obtain ⟨g, decoder, _hlow, hexact⟩ := hsock
  refine ⟨g, decoder, hexact, ?_⟩
  rw [hexact]
  exact sym_searchable g decoder hr

/-- **Error-corrected symmetric decoding (toy, proved).**  If at *every* point a strict majority of the `r`
approximants agree with `f`, then `f` is *exactly* the threshold count `[> r/2 \text{ of the gates output } 1]`.  This
is the decoding half of the BT conversion — symmetric count recovers the exact value under controlled error. -/
theorem majority_decode (f : (Fin n → Bool) → Bool) (g : Fin r → (Fin n → Bool) → Bool)
    (hmaj : ∀ x, r < 2 * (Finset.univ.filter (fun i => g i x = f x)).card) :
    ∀ x, f x = decide (r < 2 * gateCount g x) := by
  intro x
  -- `gateCount` is the number of approximants outputting `1`
  have hcount : gateCount g x = (Finset.univ.filter (fun i => g i x = true)).card := by
    unfold gateCount
    rw [Finset.sum_boole, Nat.cast_id]
  -- `filter (= false)` is the complement of `filter (= true)`
  have hfeq : (Finset.univ.filter (fun i => g i x = false))
      = (Finset.univ.filter (fun i => ¬ (g i x = true))) :=
    Finset.filter_congr (fun i _ => by simp [Bool.not_eq_true])
  -- `#(=1) + #(=0) = r`
  have hsum : (Finset.univ.filter (fun i => g i x = true)).card
      + (Finset.univ.filter (fun i => g i x = false)).card = r := by
    have hcompl := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin r))) (fun i => g i x = true)
    rw [Finset.card_univ, Fintype.card_fin] at hcompl
    rw [hfeq]; exact hcompl
  rcases hfx : f x with _ | _
  · -- `f x = false`: majority output `0`, so `2·#(=1) < r`, threshold is `false`
    have hag : (Finset.univ.filter (fun i => g i x = f x)).card
        = (Finset.univ.filter (fun i => g i x = false)).card := by rw [hfx]
    have h := hmaj x
    rw [hag] at h
    have hnot : ¬ r < 2 * gateCount g x := by rw [hcount]; omega
    simp [hnot]
  · -- `f x = true`: majority output `1`, so `r < 2·#(=1)`, threshold is `true`
    have hag : (Finset.univ.filter (fun i => g i x = f x)).card
        = (Finset.univ.filter (fun i => g i x = true)).card := by rw [hfx]
    have h := hmaj x
    rw [hag] at h
    have hlt : r < 2 * gateCount g x := by rw [hcount]; omega
    simp [hlt]

/-- **The decode is exactly a symmetric function (proved).**  Under majority-correctness, `f = symEval g [> r/2]` — an
exact symmetric (count) decode of the approximants. -/
theorem majority_decode_symmetric (f : (Fin n → Bool) → Bool) (g : Fin r → (Fin n → Bool) → Bool)
    (hmaj : ∀ x, r < 2 * (Finset.univ.filter (fun i => g i x = f x)).card) :
    f = symEval g (fun k => decide (r < 2 * k)) := by
  funext x
  rw [majority_decode f g hmaj x]
  rfl

/-- **The toy discharges the socket's `exact` clause (proved).**  Low-degree approximants that are majority-correct at
every point yield the BT conversion socket.  The toy supplies `exact`; producing such *low-degree* majority-correct
approximants for arbitrary `ACC⁰` is the open clause — Wall 1. -/
theorem majority_decode_gives_socket {D : ℕ} (f : (Fin n → Bool) → Bool)
    (g : Fin r → (Fin n → Bool) → Bool) (hlow : ∀ i, IsLowDegreeGate D (g i))
    (hmaj : ∀ x, r < 2 * (Finset.univ.filter (fun i => g i x = f x)).card) :
    ApproxToExactSymmetricDecode D r f :=
  ⟨g, (fun k => decide (r < 2 * k)), hlow, majority_decode_symmetric f g hmaj⟩

end PallLean.Paper93.DeepMath.PathB.ACC0ApproxToExactDecode

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ApproxToExactDecode.socket_searchable
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ApproxToExactDecode.majority_decode
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ApproxToExactDecode.majority_decode_symmetric
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ApproxToExactDecode.majority_decode_gives_socket
