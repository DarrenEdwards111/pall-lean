/-
  PallLean/Paper93/Direct/BooleanityDirect.lean

  Paper §9 Lemma 31 — direct booleanity factor membership in the
  concrete `W_σ(τ)` family.

  Agent M1 of 3 (parallel).

  ## Scope

  This file packages Agent H3's unconditional membership theorem
  `booleanity_factor_mem_ambient_unconditional` (commit `34e3af5`)
  through Agent J1's `concreteW` family (commit `b36a8b1`). The result
  is an unconditional existence of an embedding `σ : Fin 4 ↪ Fin n` with
  `σ 0 = v` along which the compiled Cook-Levin booleanity factor
  `1 - X_v + X_v^2` lies in the concrete ambient per-type space
  `concreteW n hn4 σ .booleanity`.

  Since Agent J1 defines
      `concreteW n hn4 σ τ := ambientPerTypeSpace
                                  perTypeInterfaceSpace n hn4 σ τ`,
  the concrete and abstract ambient per-type spaces are definitionally
  equal, and H3's conclusion transports unchanged. We nevertheless
  spell out the reduction explicitly (via `show`) so that no
  `rfl`-folding depends on implicit reducibility settings at the call
  site.

  ## Deliverable

    * `booleanity_factor_direct_mem` — for every Turing-machine
      parameter tuple `(M, n, hn, htb, hns)` with `hn4 : n ≥ 4` and
      every variable `v : Fin n`, there exists an embedding
      `σ : Fin 4 ↪ Fin n` with
      `(1 - X v + X v^2 : MvPolynomial (Fin n) ℚ)`
      in `concreteW n hn4 σ .booleanity`.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Spanning.DischargeOneMem
import PallLean.Paper93.Wiring.ConcreteW

namespace PallLean.Paper93.Direct

open MvPolynomial
open PallLean.Paper93
open PallLean.Paper93.Bridge
open PallLean.Paper93.Spanning
open PallLean.Paper93.Wiring
open SymmetricPowerBound (ConstraintType)

/-- **Direct booleanity factor membership in `concreteW`.**

For every Turing-machine parameter tuple `(M, n, hn, htb, hns)` with
`hn4 : n ≥ 4` and every variable `v : Fin n`, there exists an
embedding `σ : Fin 4 ↪ Fin n` along which the compiled Cook-Levin
booleanity factor `1 - X_v + X_v^2` lies in Agent J1's concrete
ambient per-type space `concreteW n hn4 σ .booleanity`.

This is Agent H3's `booleanity_factor_mem_ambient_unconditional`
(which targets `ambientPerTypeSpace perTypeInterfaceSpace n hn4 σ
.booleanity`) transported through Agent J1's definition

    concreteW n hn4 σ τ := ambientPerTypeSpace
                              perTypeInterfaceSpace n hn4 σ τ

which makes the two ambient spaces definitionally equal. -/
theorem booleanity_factor_direct_mem
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (v : Fin n) (hn4 : n ≥ 4) :
    ∃ σ : Fin 4 ↪ Fin n,
      (1 - MvPolynomial.X v + (MvPolynomial.X v) ^ 2 :
          MvPolynomial (Fin n) ℚ)
        ∈ concreteW n hn4 σ ConstraintType.booleanity := by
  -- Use H3's unconditional membership composed with J1's concreteW.
  -- `concreteW n hn4 σ τ = ambientPerTypeSpace perTypeInterfaceSpace n
  -- hn4 σ τ` by definition, so the two membership statements are
  -- definitionally equal.
  obtain ⟨σ, hMem⟩ :=
    booleanity_factor_mem_ambient_unconditional M n hn htb hns v hn4
  refine ⟨σ, ?_⟩
  -- Unfold `concreteW` to the abstract ambient per-type space.
  show (1 - MvPolynomial.X v + (MvPolynomial.X v) ^ 2 :
          MvPolynomial (Fin n) ℚ)
        ∈ ambientPerTypeSpace perTypeInterfaceSpace n hn4 σ
            ConstraintType.booleanity
  exact hMem

/-! ## Kernel-only axiom trace

The deliverable should depend only on
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms booleanity_factor_direct_mem

end PallLean.Paper93.Direct
