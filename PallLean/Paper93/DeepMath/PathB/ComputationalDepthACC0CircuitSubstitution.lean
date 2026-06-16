import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ProbabilisticAmplification

/-!
# The circuit-substitution assembly — error accumulates additively over gates

The probabilistic-polynomial layer is complete: exact `MOD` indicators, the `OR` polynomial (error `1/p`), and its
amplification to `(1/p)^t` (`…ACC0ProbabilisticAmplification`).  To turn per-gate approximants into a single
approximant of a *whole* constant-depth circuit, one substitutes the polynomials bottom-up and bounds the accumulated
error by the union bound.  This file proves that **substitution error bound** for a faithful circuit model.

A circuit over `n` inputs is `inp / cst / una / bin` (unary and binary gates; `AND`/`OR`/`MOD`/`NOT` are instances —
the bookkeeping is the same for any gate operation).  `eval` is the true value; `step P c` applies the true gate of `c`
to the chosen approximants `P` of its children; the *local* error of a node is where its approximant `P c` disagrees
with `step P c` (the gate's own probabilistic-polynomial error).  The hybrid argument then gives:

\[ \#\{x : P\,c\,x \ne \mathrm{eval}\,c\,x\} \;\le\; \mathrm{size}(c)\cdot\varepsilon \]

whenever every node's local error is `≤ ε`.

## What is proved (clean axioms, no `sorry`)

* **`Circ`, `eval`, `size`, `step`** — the circuit model, true evaluation, gate count, and one-step approximant.
* **`circuit_error_bound`** — the substitution union bound: if every node's local approximant errs on `≤ ε` inputs,
  the whole circuit's approximant errs on `≤ size · ε` inputs.  Proved by structural induction (the hybrid argument:
  at each gate the error is at most the gate's own error plus the propagated children errors).

## The remaining read-off socket

* **`CircuitToSymAndReadoff`** — converting the low-error low-degree polynomial approximant of a constant-depth circuit
  into a quasipolynomial approximate `SYM∘AND` representation (the sparse cube-sum / level-count conversion already
  built on the counting side), discharging `…ACC0BTSizeRecurrence.QuasipolyApproxCompression`.  Left as the named
  socket; the substitution *error* half is proved here.

## Honest scope

The error-accumulation core of the substitution — the genuine hybrid union bound over the circuit — is *proved* for the
circuit model.  The degree multiplication and the final polynomial-to-`SYM∘AND` read-off (needing the `MvPolynomial`
substitution and the sparse-counting conversion) remain the named socket.  With the gate errors calibrated to
`ε = 2^n/(10·size)` (amplification + `error_choice`) this gives total error `< 2^n/10`.  Nothing here is `NEXP ⊄ ACC⁰`
or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CircuitSubstitution

open scoped Classical
open Finset

variable {n : ℕ}

/-- A circuit over `n` Boolean inputs: input, constant, unary gate, binary gate.  `AND`/`OR`/`MOD`/`NOT` are
instances of `una`/`bin` (the substitution bookkeeping is the same for any gate operation). -/
inductive Circ (n : ℕ) where
  | inp : Fin n → Circ n
  | cst : Bool → Circ n
  | una : (Bool → Bool) → Circ n → Circ n
  | bin : (Bool → Bool → Bool) → Circ n → Circ n → Circ n

/-- The true value of a circuit. -/
def eval : Circ n → (Fin n → Bool) → Bool
  | .inp i => fun x => x i
  | .cst b => fun _ => b
  | .una f c => fun x => f (eval c x)
  | .bin g a b => fun x => g (eval a x) (eval b x)

/-- The gate count (number of nodes). -/
def size : Circ n → ℕ
  | .inp _ => 1
  | .cst _ => 1
  | .una _ c => size c + 1
  | .bin _ a b => size a + size b + 1

/-- The one-step approximant: apply the true gate of `c` to the children's chosen approximants `P`. -/
def step (P : Circ n → (Fin n → Bool) → Bool) : Circ n → (Fin n → Bool) → Bool
  | .inp i => fun x => x i
  | .cst b => fun _ => b
  | .una f c => fun x => f (P c x)
  | .bin g a b => fun x => g (P a x) (P b x)

/-- **The substitution error bound (proved): substitution accumulates error at most additively over the gates.**  If
every node's approximant `P c` agrees with the gate-of-approximated-children `step P c` on all but `ε` inputs (the
gate's own probabilistic-polynomial error), then the whole circuit's approximant `P c` agrees with the true value
`eval c` on all but `size c · ε` inputs.  Proved by the hybrid argument: at each gate the error is at most the gate's
own local error plus the propagated children errors. -/
theorem circuit_error_bound (P : Circ n → (Fin n → Bool) → Bool) (ε : ℕ)
    (H : ∀ c, (Finset.univ.filter (fun x => P c x ≠ step P c x)).card ≤ ε) :
    ∀ c, (Finset.univ.filter (fun x => P c x ≠ eval c x)).card ≤ size c * ε := by
  intro c
  induction c with
  | inp i => simpa [size, step, eval] using H (Circ.inp i)
  | cst b => simpa [size, step, eval] using H (Circ.cst b)
  | una f c ih =>
      have hsub :
          (Finset.univ.filter (fun x => P (Circ.una f c) x ≠ eval (Circ.una f c) x))
            ⊆ (Finset.univ.filter (fun x => P (Circ.una f c) x ≠ step P (Circ.una f c) x))
              ∪ (Finset.univ.filter (fun x => P c x ≠ eval c x)) := by
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx
        simp only [mem_union, mem_filter, mem_univ, true_and]
        by_cases h1 : P (Circ.una f c) x = step P (Circ.una f c) x
        · right
          intro hce
          apply hx
          calc P (Circ.una f c) x = step P (Circ.una f c) x := h1
            _ = f (P c x) := rfl
            _ = f (eval c x) := by rw [hce]
            _ = eval (Circ.una f c) x := rfl
        · left; exact h1
      calc (Finset.univ.filter (fun x => P (Circ.una f c) x ≠ eval (Circ.una f c) x)).card
          ≤ ((Finset.univ.filter (fun x => P (Circ.una f c) x ≠ step P (Circ.una f c) x))
              ∪ (Finset.univ.filter (fun x => P c x ≠ eval c x))).card := Finset.card_le_card hsub
        _ ≤ (Finset.univ.filter (fun x => P (Circ.una f c) x ≠ step P (Circ.una f c) x)).card
              + (Finset.univ.filter (fun x => P c x ≠ eval c x)).card := Finset.card_union_le _ _
        _ ≤ ε + size c * ε := add_le_add (H _) ih
        _ = size (Circ.una f c) * ε := by simp only [size]; ring
  | bin g a b iha ihb =>
      have hsub :
          (Finset.univ.filter (fun x => P (Circ.bin g a b) x ≠ eval (Circ.bin g a b) x))
            ⊆ (Finset.univ.filter (fun x => P (Circ.bin g a b) x ≠ step P (Circ.bin g a b) x))
              ∪ ((Finset.univ.filter (fun x => P a x ≠ eval a x))
                ∪ (Finset.univ.filter (fun x => P b x ≠ eval b x))) := by
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx
        simp only [mem_union, mem_filter, mem_univ, true_and]
        by_cases h1 : P (Circ.bin g a b) x = step P (Circ.bin g a b) x
        · by_cases ha : P a x = eval a x
          · by_cases hb : P b x = eval b x
            · exact absurd
                (by calc P (Circ.bin g a b) x = step P (Circ.bin g a b) x := h1
                      _ = g (P a x) (P b x) := rfl
                      _ = g (eval a x) (eval b x) := by rw [ha, hb]
                      _ = eval (Circ.bin g a b) x := rfl) hx
            · right; right; exact hb
          · right; left; exact ha
        · left; exact h1
      calc (Finset.univ.filter (fun x => P (Circ.bin g a b) x ≠ eval (Circ.bin g a b) x)).card
          ≤ ((Finset.univ.filter (fun x => P (Circ.bin g a b) x ≠ step P (Circ.bin g a b) x))
              ∪ ((Finset.univ.filter (fun x => P a x ≠ eval a x))
                ∪ (Finset.univ.filter (fun x => P b x ≠ eval b x)))).card := Finset.card_le_card hsub
        _ ≤ (Finset.univ.filter (fun x => P (Circ.bin g a b) x ≠ step P (Circ.bin g a b) x)).card
              + ((Finset.univ.filter (fun x => P a x ≠ eval a x)).card
                + (Finset.univ.filter (fun x => P b x ≠ eval b x)).card) := by
              refine le_trans (Finset.card_union_le _ _) ?_
              exact Nat.add_le_add_left (Finset.card_union_le _ _) _
        _ ≤ ε + (size a * ε + size b * ε) := add_le_add (H _) (add_le_add iha ihb)
        _ = size (Circ.bin g a b) * ε := by simp only [size]; ring

/-- **The remaining read-off socket (open).**  Converting a low-error, low-degree polynomial approximant of a
constant-depth circuit (produced by substituting the amplified probabilistic polynomials, with error controlled by
`circuit_error_bound`) into a quasipolynomial approximate `SYM∘AND` representation — the sparse cube-sum / level-count
conversion on the counting side — discharges `…ACC0BTSizeRecurrence.QuasipolyApproxCompression` (the named socket there;
not re-wrapped here).  The substitution *error* half is proved above. -/
theorem circuit_substitution_readoff_socket
    (RSRep ACC0SatSpeedup NEXPHasACC0Circuits Collapse : Prop)
    (readoff : RSRep)
    (counting : RSRep → ACC0SatSpeedup)
    (williams : ACC0SatSpeedup → NEXPHasACC0Circuits → Collapse)
    (hierarchy : ¬ Collapse) :
    ¬ NEXPHasACC0Circuits :=
  ACC0RankRouteFrontier.composite_route_to_NEXP_not_ACC0
    RSRep ACC0SatSpeedup NEXPHasACC0Circuits Collapse readoff counting williams hierarchy

end PallLean.Paper93.DeepMath.PathB.ACC0CircuitSubstitution

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CircuitSubstitution.circuit_error_bound
