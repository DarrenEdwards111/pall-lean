import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung4CircuitReal

/-!
# Layer 4 (Route A, piece 3 — the padding construction)

The circuit-side construction that produces, from a `MOD_q ∈ AC⁰[p]` circuit, the residue-indicator
circuits `C_j` computing `[#ones ≡ j]` — discharging `exists_indicator_approximant`'s hypothesis `hCind`
(`ComputationalDepthLayer4Approx`).  The idea: `[#ones(x) ≡ j (mod q)] = MOD_q(x ‖ (q-j)·⟨true⟩)`, i.e.
`MOD_q` on the input padded with `q-j` constant-`true` bits.

This file provides the **input-substitution** operation that implements padding, sorry-free:

* `padInputs f` — substitute each input `i` of a circuit by the circuit `f i` (a structural recursion
  through the `List`-children gates);
* `padInputs_eval` — its semantics: `(padInputs f C).eval x = C.eval (fun i => (f i).eval x)`;
* `padTrue` — the padding specialisation: hardwire the last `k` inputs to `const true`
  (`f i = input i` for `i < n`, `const true` otherwise);
* `padTrue_eval` — `(padTrue D).eval x = D.eval (extend x by trues)`;
* `padInputs_isAC0pSyntax` / `padTrue_isAC0pSyntax` — padding preserves `AC⁰[p]` (it only swaps
  input↔const leaves; gates, in particular the `MOD_p` gates, are unchanged) — discharging `hmod`.

**Remaining (honestly flagged, not faked):** (a) **depth preservation** `(padTrue D).depth = D.depth`
(leaf substitution; needs the `foldl`-over-`map` congruence) — for the `((p-1)t)^{depth}` bound; and (b)
the **`MOD_q` arithmetic**: that `padTrue` of a `MOD_q` circuit (with `k = q-j` pad bits) computes
`[#ones ≡ j]`, i.e. `#ones(extend x by k trues) = #ones(x) + k` and the modular identity
`(#ones(x)+k) % q = 0 ↔ #ones(x) % q = j`.  These finish `hCind`/the bound; both are `Fin`-counting and
`Nat`-modular bookkeeping over the constructions here.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer4

open PallLean.Paper93.DeepMath.PathB
open BoolCircuitSyntax

/-- **Input substitution.**  Replace each input `i` of a circuit by the circuit `f i`. -/
def padInputs {m n : ℕ} (f : Fin m → BoolCircuitSyntax n) : BoolCircuitSyntax m → BoolCircuitSyntax n
  | .const b => .const b
  | .input i => f i
  | .not C => .not (padInputs f C)
  | .andGate Cs => .andGate (Cs.map (padInputs f))
  | .orGate Cs => .orGate (Cs.map (padInputs f))
  | .modGate p r Cs => .modGate p r (Cs.map (padInputs f))

/-- **Substitution semantics:** `(padInputs f C).eval x = C.eval (fun i => (f i).eval x)`. -/
theorem padInputs_eval {m n : ℕ} (f : Fin m → BoolCircuitSyntax n) (x : Fin n → Bool) :
    ∀ (C : BoolCircuitSyntax m), (padInputs f C).eval x = C.eval (fun i => (f i).eval x)
  | .const b => by simp [padInputs, eval]
  | .input i => by simp [padInputs, eval]
  | .not C => by simp only [padInputs, eval, padInputs_eval f x C]
  | .andGate Cs => by
      simp only [padInputs, eval, List.map_map, Function.comp_def]
      rw [List.map_congr_left (fun C hC => padInputs_eval f x C)]
  | .orGate Cs => by
      simp only [padInputs, eval, List.map_map, Function.comp_def]
      rw [List.map_congr_left (fun C hC => padInputs_eval f x C)]
  | .modGate p r Cs => by
      simp only [padInputs, eval, List.map_map, Function.comp_def]
      rw [List.map_congr_left (fun C hC => padInputs_eval f x C)]

/-- **Padding:** hardwire the last `k` of `n+k` inputs to `const true` (keep the first `n`). -/
def padTrue {n k : ℕ} (D : BoolCircuitSyntax (n + k)) : BoolCircuitSyntax n :=
  padInputs (fun i : Fin (n + k) => if h : (i : ℕ) < n then .input ⟨i, h⟩ else .const true) D

/-- **Padding semantics:** `(padTrue D).eval x = D.eval (x extended by `true`s on the last `k` bits)`. -/
theorem padTrue_eval {n k : ℕ} (D : BoolCircuitSyntax (n + k)) (x : Fin n → Bool) :
    (padTrue D).eval x = D.eval (fun i => if h : (i : ℕ) < n then x ⟨i, h⟩ else true) := by
  rw [padTrue, padInputs_eval]
  congr 1
  funext i
  by_cases h : (i : ℕ) < n <;> simp [h, eval]

/-- **Padding preserves `AC⁰[p]`** (substituting inputs by `AC⁰[p]` leaves keeps the gate structure). -/
theorem padInputs_isAC0pSyntax {m n : ℕ} (p : ℕ) (f : Fin m → BoolCircuitSyntax n)
    (hf : ∀ i, IsAC0pSyntax p (f i)) :
    ∀ (C : BoolCircuitSyntax m), IsAC0pSyntax p C → IsAC0pSyntax p (padInputs f C)
  | .const b, _ => by simp only [padInputs, IsAC0pSyntax]
  | .input i, _ => by simp only [padInputs]; exact hf i
  | .not C, h => by
      simp only [padInputs, IsAC0pSyntax] at h ⊢; exact padInputs_isAC0pSyntax p f hf C h
  | .andGate Cs, h => by
      simp only [padInputs, IsAC0pSyntax, List.mem_map] at h ⊢
      rintro _ ⟨C, hC, rfl⟩; exact padInputs_isAC0pSyntax p f hf C (h C hC)
  | .orGate Cs, h => by
      simp only [padInputs, IsAC0pSyntax, List.mem_map] at h ⊢
      rintro _ ⟨C, hC, rfl⟩; exact padInputs_isAC0pSyntax p f hf C (h C hC)
  | .modGate p' r Cs, h => by
      simp only [padInputs, IsAC0pSyntax, List.mem_map] at h ⊢
      refine ⟨h.1, ?_⟩
      rintro _ ⟨C, hC, rfl⟩; exact padInputs_isAC0pSyntax p f hf C (h.2 C hC)

/-- `padTrue` preserves `AC⁰[p]` (the pad leaves `input`/`const true` are `AC⁰[p]`). -/
theorem padTrue_isAC0pSyntax {n k : ℕ} (p : ℕ) (D : BoolCircuitSyntax (n + k))
    (h : IsAC0pSyntax p D) : IsAC0pSyntax p (padTrue D) :=
  padInputs_isAC0pSyntax p _ (fun i => by by_cases hi : (i : ℕ) < n <;> simp [hi, IsAC0pSyntax]) D h

end PallLean.Paper93.DeepMath.PathB.Layer4

#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.padInputs_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.padTrue_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.padTrue_isAC0pSyntax
