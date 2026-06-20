import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Encode

/-!
# Entry 393 — universal-TM-table build: the 3-symbol transition encoding `encodeTransBits3` (proved)

The simulated machine is a *Bool* TM; the universal machine works on a *Sym3* tape (so it can use markers).  So the
encoding maps a Bool transition onto a `Sym3` tape: nat fields as `I`-runs (entry 392), and the symbol bits mapped
`true ↦ I`, `false ↦ O`.  This is the `Sym3` port of `encodeTransBits`/`encodeTransBits_length` (entries 338/372).

## What is proved (clean axioms, no `sorry`)

* **`boolToSym3 b`** — `if b then I else O`.
* **`encodeTransBits3 t`** — `encodeNatBits3 (state) ++ boolToSym3 (read) :: (encodeNatBits3 (state') ++ boolToSym3
  (write) :: encodeNatBits3 (move))`.
* **`encodeTransBits3_length`** (PROVED) — `(encodeTransBits3 t).length = t.1.1 + t.2.1 + t.2.2.2.val + 5`.

## Honest scope

This **ports the transition encoding** to the marker alphabet.  It does **not** yet build any `Sym3` scanner, nor the
rule-loop, nor `EmitsEncodedStep`.  Building those fragment by fragment is the genuine remaining construction, **not
faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EncTrans

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMTrans)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Encode (encodeNatBits3)

/-- **Map a simulated Bool symbol to `Sym3`**: `true ↦ I`, `false ↦ O`. -/
def boolToSym3 (b : Bool) : Sym3 := if b then Sym3.I else Sym3.O

/-- **Encode a (Bool) transition onto a `Sym3` tape**: the five fields `state, read, state', write, move`, nats as
`I`-runs and symbol bits via `boolToSym3`. -/
def encodeTransBits3 (t : TMTrans) : List Sym3 :=
  encodeNatBits3 t.1.1 ++ boolToSym3 t.1.2 ::
    (encodeNatBits3 t.2.1 ++ boolToSym3 t.2.2.1 :: encodeNatBits3 t.2.2.2.val)

theorem encodeTransBits3_length (t : TMTrans) :
    (encodeTransBits3 t).length = t.1.1 + t.2.1 + t.2.2.2.val + 5 := by
  obtain ⟨⟨rs, rsym⟩, ws, wsym, mv⟩ := t
  simp only [encodeTransBits3, encodeNatBits3, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil]
  omega

/-!
**The 3-symbol transition encoding, proved.**  `encodeTransBits3` puts a simulated Bool transition on the marker tape,
mirroring entries 338/372.  Next: the machine and config encodings, then the `Sym3` scanners — fragment by verified
fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EncTrans

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EncTrans.encodeTransBits3_length
