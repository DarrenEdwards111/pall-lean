import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3AC0pPolyMod

/-!
# Layer 3 — full `IsAC0pSyntax` correctness of the circuit → polynomial representation

Assembles the exact-representation correctness over the **whole** `AC⁰[p]` gate basis
(`IsAC0pSyntax p`): constants, inputs, `¬`, `∧`, `∨` (from `toPoly_eval_AC0`'s machinery) **and**
`MOD_p` gates (from `toPoly_modGate_eval`, the Fermat indicator).  For a prime `p`:

* `toPoly_eval_AC0p` — `MvPolynomial.eval (embed p x) (toPoly p C) = boolToZMod p (C.eval x)` for every
  `IsAC0pSyntax p` circuit `C`.

So every `AC⁰[p]` circuit has an *exact* polynomial representation over `ZMod p` agreeing with it on
`{0,1}`-inputs — the (high-degree) foundation the Razborov–Smolensky low-degree *approximation* refines.
No lower bound, no capstone.  AC⁰[p] is a higher circuit-lower-bound layer; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer3

open PallLean.Paper93.DeepMath.PathB
open MvPolynomial

variable {n : ℕ}

-- The full AC⁰[p] correctness (mutual with the list version; explicit recursive argument so the
-- recursion through the List-nested circuit is structural, as in `toPoly_eval_AC0`).
mutual
theorem toPoly_eval_AC0p (p : ℕ) [Fact p.Prime] (x : Fin n → Bool) :
    (c : BoolCircuitSyntax n) → BoolCircuitSyntax.IsAC0pSyntax p c →
      MvPolynomial.eval (embed p x) (toPoly p c) = boolToZMod p (c.eval x)
  | .const b, _ => by simp [toPoly, BoolCircuitSyntax.eval]
  | .input i, _ => by simp [toPoly, BoolCircuitSyntax.eval, embed]
  | .not c, hc => by
      simp only [BoolCircuitSyntax.IsAC0pSyntax] at hc
      have hci := toPoly_eval_AC0p p x c hc
      simp only [toPoly, map_sub, map_one, BoolCircuitSyntax.eval, hci]
      cases c.eval x <;> simp [boolToZMod]
  | .andGate cs, hc => by
      simp only [BoolCircuitSyntax.IsAC0pSyntax] at hc
      simp only [toPoly, BoolCircuitSyntax.eval]
      rw [eval_prod_toPolyList p x cs (toPolyList_eval_AC0p p x cs hc), boolToZMod_all, List.map_map]
      rfl
  | .orGate cs, hc => by
      simp only [BoolCircuitSyntax.IsAC0pSyntax] at hc
      simp only [toPoly, BoolCircuitSyntax.eval, map_sub, map_one]
      rw [eval_prod_one_sub_toPolyList p x cs (toPolyList_eval_AC0p p x cs hc), boolToZMod_any,
        List.map_map]
      rfl
  | .modGate q r cs, hc => by
      simp only [BoolCircuitSyntax.IsAC0pSyntax] at hc
      obtain ⟨hq, hcs⟩ := hc
      rw [hq]
      exact toPoly_modGate_eval p x r cs (toPolyList_eval_AC0p p x cs hcs)
theorem toPolyList_eval_AC0p (p : ℕ) [Fact p.Prime] (x : Fin n → Bool) :
    (cs : List (BoolCircuitSyntax n)) → (∀ c ∈ cs, BoolCircuitSyntax.IsAC0pSyntax p c) →
      ∀ c ∈ cs, MvPolynomial.eval (embed p x) (toPoly p c) = boolToZMod p (c.eval x)
  | [], _ => fun c hc => absurd hc (by simp)
  | c0 :: cs, h => fun c hc => by
      rcases List.mem_cons.mp hc with rfl | hmem
      · exact toPoly_eval_AC0p p x c (h c (by simp))
      · exact toPolyList_eval_AC0p p x cs (fun c'' hc'' => h c'' (by simp [hc''])) c hmem
end

end PallLean.Paper93.DeepMath.PathB.Layer3

#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.toPoly_eval_AC0p
