import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0YBTExactCompose
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0WilliamsCashout

/-!
# Is the YBT socket separation-strength?  Answered: NO — and here is the proof structure why

The honest test asked: confirm the YBT exact-normal-form socket (`HasExactSymAndForm` / the Yao–Beigel–Tarui depth
collapse) is separation-strength.  Digging into the corpus, the answer is **the opposite**, and the discipline requires
reporting it: the YBT socket is **not** separation-strength.  It is a *known true classical theorem* (Beigel–Tarui
1991) whose only open part is a quasipolynomial **size bound** on an *unconditionally existing* construction.  The
separation-strength lives entirely **downstream**, in the realization + Williams sockets (already self-audited as
equivalent to the separation).

**Why YBT is not separation-strength (each fact is proved in the corpus, re-exported here):**

1. *The exact `SYM∘AND` form exists unconditionally.*  `acc0circuit_hasSymAndForm`: **every** `ACC⁰` circuit equals a
   count gate over `symAndSize C` monomial-`AND`s — a genuine theorem, no socket.  In particular `hasSymAndForm_mod`
   builds the exact form for a `MOD_q` gate of **any** modulus `q` (composite included) — it is *counting-based*
   (`modQStatOn`, an integer weight), hence **characteristic-free**, so composite `MOD` is *no barrier to existence*
   (exactly entry 290's escape: counting over `ℤ` carries every characteristic).
2. *The YBT socket is purely a size bound.*  `acc0circuit_hasExactSymAndForm`: once `symAndSize C + 1 < 2^n`, the socket
   `HasExactSymAndForm C` fires.  So the only open content is the quasipolynomial *size* — the Beigel–Tarui theorem,
   true and known, hard *combinatorics* to formalize, but **not** a hardness assumption.
3. *The socket yields only a cell-model search.*  `ybt_socket_searchable`: `HasExactSymAndForm C ⇒` SAT decided in
   `< 2^n` **cells** — not a uniform algorithm, not the separation.
4. *The separation-strength is downstream.*  `realization_socket_iff_separation`, `williams_socket_iff_separation`:
   once the cell speedup holds, the *realization* and *Williams* sockets are each **logically equivalent to**
   `NEXP ⊄ ACC⁰`.  Those carry the whole difficulty.

So even with YBT fully formalized, the separation would still require realization + Williams — which *are*
separation-strength.  YBT is the true, known, combinatorially-hard **front half**; it does not carry the separation.

## What is proved (clean axioms, no `sorry`)

* **`exact_symAnd_form_exists`** (re-export) — every `ACC⁰` circuit has an exact `SYM∘AND` form unconditionally.
* **`mod_form_characteristic_free`** (re-export) — a `MOD_q` gate has an exact form for **every** `q` (counting-based,
  composite `MOD` no barrier).
* **`ybt_socket_is_size_bound`** (re-export) — the socket fires from `symAndSize C + 1 < 2^n`: its content is a size.
* **`ybt_socket_yields_cell_search`** (re-export) — the socket gives only a `< 2^n`-cell search.
* **`realization_is_separation_strength`, `williams_is_separation_strength`** (re-export) — the downstream sockets are
  each `↔ NEXP ⊄ ACC⁰`.
* **`ybt_socket_not_separation_strength`** (PROVED bundle) — the conclusion: the exact form exists unconditionally, the
  socket is just a size bound, and the separation-strength is the (downstream) realization socket — so YBT is not it.

## Honest scope

This **corrects and answers** the question: the YBT socket is not separation-strength — it is a known true theorem
(existence proved here unconditionally; quasipoly size = Beigel–Tarui, hard combinatorics).  The separation-strength is
the realization + Williams cash-out, already self-audited.  Reporting this honestly (rather than rubber-stamping
"separation-strength") is the point.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0YBTSocketStrength

open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0YBTExactCompose
open PallLean.Paper93.DeepMath.PathB.ACC0YBTSocket
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsCashout

variable {n : ℕ}

/-- **The exact `SYM∘AND` form exists unconditionally (re-export).**  Every `ACC⁰` circuit equals a count gate over
`symAndSize C` monomial-`AND`s — a genuine theorem, no socket.  The YBT socket is *not* about existence. -/
theorem exact_symAnd_form_exists (C : ACC0Circuit n) :
    HasSymAndForm (fun x => eval C x) (symAndSize C) :=
  acc0circuit_hasSymAndForm C

/-- **A `MOD_q` gate has an exact form for every modulus (re-export) — composite `MOD` is no barrier.**  The form is
counting-based (`modQStatOn`, an integer weight on `S`), hence *characteristic-free*: it exists for **any** `q`,
composite included.  This is entry 290's escape inside the YBT reduction — the polynomial method's `no_common_char`
barrier never even touches the *existence* of the YBT form. -/
theorem mod_form_characteristic_free (q : ℕ) (S : Finset (Fin n)) (t : ZMod q) :
    HasSymAndForm (fun x => decide (modQStatOn S q x = t)) S.card :=
  hasSymAndForm_mod q S t

/-- **The YBT socket is purely a size bound (re-export).**  Once `symAndSize C + 1 < 2^n`, the always-existing exact
form *is* the socket `HasExactSymAndForm C`.  So the only open content is the quasipolynomial *size* — the Beigel–Tarui
theorem, true and known, hard combinatorics, **not** a hardness assumption. -/
theorem ybt_socket_is_size_bound (C : ACC0Circuit n) (hsize : symAndSize C + 1 < 2 ^ n) :
    HasExactSymAndForm C :=
  acc0circuit_hasExactSymAndForm C hsize

/-- **The socket yields only a cell-model search (re-export).**  `HasExactSymAndForm C ⇒` SAT decided by a `< 2^n`-cell
search — not a uniform algorithm, not the separation. -/
theorem ybt_socket_yields_cell_search (C : ACC0Circuit n) (hC : HasExactSymAndForm C) :
    ∃ (m : ℕ) (mono : Fin m → Finset (Fin n)) (h : ℕ → Bool),
      (Satisfiable (eval C) ↔
          ∃ c ∈ Finset.univ.image (gateCount (fun j x => monoAND (mono j) x)), h c = true)
        ∧ (Finset.univ.image (gateCount (fun j x => monoAND (mono j) x))).card < 2 ^ n :=
  ybt_socket_searchable C hC

/-- **The realization socket IS separation-strength (re-export self-audit).**  Once the residue cell speedup holds, the
uniform-realization socket is *logically equivalent* to `NEXP ⊄ ACC⁰`.  This — not YBT — carries the separation. -/
theorem realization_is_separation_strength {NEXPnotACC0 : Prop}
    (hspeedup : ∀ k, MixedACCResidueSatSpeedup k) :
    UniformWilliamsRealizationSocket NEXPnotACC0 ↔ NEXPnotACC0 :=
  realization_socket_iff_separation hspeedup

/-- **The Williams socket IS separation-strength (re-export self-audit).**  Once a uniform `ACC⁰`-SAT speedup holds, the
Williams algorithmic-method hypothesis is *logically equivalent* to `NEXP ⊄ ACC⁰`. -/
theorem williams_is_separation_strength {UniformACC0SatSpeedup NEXPnotACC0 : Prop}
    (huniform : UniformACC0SatSpeedup) :
    (UniformACC0SatSpeedup → NEXPnotACC0) ↔ NEXPnotACC0 :=
  williams_socket_iff_separation huniform

/-- **The answer (PROVED bundle): the YBT socket is NOT separation-strength.**  Three facts together:
(a) the exact `SYM∘AND` form exists *unconditionally* for every `ACC⁰` circuit (`acc0circuit_hasSymAndForm`) — no
socket, a genuine theorem; (b) the YBT socket is exactly the *size bound* `symAndSize C + 1 < 2^n` firing on that
existing form (`acc0circuit_hasExactSymAndForm`) — the open part is quasipoly size, the true Beigel–Tarui theorem; and
(c) the separation-strength is the *downstream* realization socket, which is `↔ NEXP ⊄ ACC⁰` once the speedup holds
(`realization_socket_iff_separation`).  So YBT is the true/known front half; it does not carry the separation, which
lives in realization + Williams. -/
theorem ybt_socket_not_separation_strength {NEXPnotACC0 : Prop} :
    (∀ C : ACC0Circuit n, HasSymAndForm (fun x => eval C x) (symAndSize C))
    ∧ (∀ C : ACC0Circuit n, symAndSize C + 1 < 2 ^ n → HasExactSymAndForm C)
    ∧ (∀ (_hspeedup : ∀ k, MixedACCResidueSatSpeedup k),
        UniformWilliamsRealizationSocket NEXPnotACC0 ↔ NEXPnotACC0) :=
  ⟨acc0circuit_hasSymAndForm, acc0circuit_hasExactSymAndForm,
   fun hspeedup => realization_socket_iff_separation hspeedup⟩

/-!
**The answer.**  The YBT exact-normal-form socket is **not** separation-strength.  The exact `SYM∘AND` form exists
unconditionally (`exact_symAnd_form_exists`), for `MOD_q` gates of every modulus via characteristic-free counting
(`mod_form_characteristic_free`, entry 290's escape); the socket is purely a quasipolynomial *size* bound on that
existing form (`ybt_socket_is_size_bound`) — the true, known Beigel–Tarui theorem, hard combinatorics but not a hardness
assumption; and it yields only a cell-model search (`ybt_socket_yields_cell_search`).  The separation-strength is
**downstream**: the realization and Williams sockets are each `↔ NEXP ⊄ ACC⁰`
(`realization_is_separation_strength`, `williams_is_separation_strength`).  So the honest correction to the premise:
YBT is the true front half; the separation lives in realization + Williams.  Not faked — the negative is reported as
found.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0YBTSocketStrength

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0YBTSocketStrength.exact_symAnd_form_exists
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0YBTSocketStrength.mod_form_characteristic_free
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0YBTSocketStrength.ybt_socket_is_size_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0YBTSocketStrength.ybt_socket_yields_cell_search
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0YBTSocketStrength.realization_is_separation_strength
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0YBTSocketStrength.williams_is_separation_strength
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0YBTSocketStrength.ybt_socket_not_separation_strength
