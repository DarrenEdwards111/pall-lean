import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3WriteWrite

/-!
# Entry 392 — universal-TM-table build: the 3-symbol encoding `encodeNatBits3` (proved)

Migrating toward a `Sym3` universal machine (so the marker rule-loop can run on the encoded tape) starts with the
encoding.  This brick ports `encodeNatBits` (entry 338) and its content lemmas (entry 345) to the 3-symbol alphabet: a
nat `n` is `n` ones (`I`) then a zero/separator (`O`).

## What is proved (clean axioms, no `sorry`)

* **`encodeNatBits3 n`** — `List.replicate n I ++ [O]`.
* **`encodeNatBits3_length`** (PROVED) — `(encodeNatBits3 n).length = n + 1`.
* **`encNat3_getD_lt`** (PROVED) — `j < n → (encodeNatBits3 n ++ rest).getD j O = I` (the ones).
* **`encNat3_getD_eq`** (PROVED) — `(encodeNatBits3 n ++ rest).getD n O = O` (the separator).

## Honest scope

This **founds the 3-symbol encoding** — the basis for `Sym3` scanners and, ultimately, the `Sym3` universal machine.
It does **not** yet build any `Sym3` scanner, nor the rule-loop, nor `EmitsEncodedStep`.  Building those fragment by
fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Encode

open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3)

/-- **Encode a nat** over `Sym3` as `n` ones then a zero separator. -/
def encodeNatBits3 (n : ℕ) : List Sym3 := List.replicate n Sym3.I ++ [Sym3.O]

theorem encodeNatBits3_length (n : ℕ) : (encodeNatBits3 n).length = n + 1 := by
  simp [encodeNatBits3]

/-- **The ones (PROVED).**  `(encodeNatBits3 n ++ rest).getD j O = I` for `j < n`. -/
theorem encNat3_getD_lt (n : ℕ) (rest : List Sym3) (j : ℕ) (hj : j < n) :
    (encodeNatBits3 n ++ rest).getD j Sym3.O = Sym3.I := by
  rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simp only [encodeNatBits3, List.length_append, List.length_replicate, List.length_cons, List.length_nil]; omega)]
  simp only [encodeNatBits3]
  rw [List.getElem?_append_left (by rw [List.length_replicate]; exact hj), List.getElem?_replicate_of_lt hj]
  rfl

/-- **The separator (PROVED).**  `(encodeNatBits3 n ++ rest).getD n O = O`. -/
theorem encNat3_getD_eq (n : ℕ) (rest : List Sym3) :
    (encodeNatBits3 n ++ rest).getD n Sym3.O = Sym3.O := by
  rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simp only [encodeNatBits3, List.length_append, List.length_replicate, List.length_cons, List.length_nil]; omega)]
  simp only [encodeNatBits3]
  rw [List.getElem?_append_right (by rw [List.length_replicate])]
  simp

/-!
**The 3-symbol encoding, founded.**  `encodeNatBits3` and its content lemmas mirror the `Bool` encoding (entries
338/345) over the marker alphabet — the basis for the `Sym3` scanners next.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Encode

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Encode.encNat3_getD_lt
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Encode.encNat3_getD_eq
