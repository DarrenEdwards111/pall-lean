import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModpGate

/-!
# The native/non-native bridge — `MOD_p` easy over `F_p`, hard over `F_q`, wired to the `PatternRich` socket

The broad N-Frame search is done; this is the assembly path.  This file makes the native/non-native split
*theorem-level* (not commentary) and connects the native `MOD_p` result (entry 270) to the `PatternRich`/cross-field
lower-bound socket (entries 262/264) via the **dictator family**, whose cross-field count is exactly `MOD_p`.

**Native (easy).**  Over `F_p`, `MOD_p` has the exact polynomial `1 − (∑ᵢ xᵢ)^{p-1}` of degree `p-1`, fan-in-free
(`ACC0ModpGate.modp_native_repr`).  Restated here as `modp_native_easy`.

**The cross-field identity.**  The dictator family `gᵢ(x) := xᵢ` has `#{i : gᵢ fires} = #{true inputs}`, so its
cross-field count mod `p` is the Hamming weight mod `p`, and `MOD_p` fires iff that count is `0`
(`modp_iff_dictator_crossFieldCount_zero`).  Thus `MOD_p` *is* the cross-field-count object of entry 251.

**Non-native (hard).**  The dictator family is `AlgExpander` *and* `PatternRich (2^s)`
(`dictator_meets_patternRich_socket`), so it hits the antecedent of `PatternRichCrossFieldLowerBound` (entry 262): its
cross-field count mod `q` (`q ≠ p`) is the central non-native hard object — `MOD_q`, hard in `AC⁰[p]` by the in-arc
`Layer4.mod_q_indicators_false`.

## What is proved (clean axioms, no `sorry`)

* **`modp_native_easy`** (PROVED) — over `F_p`, `MOD_p` has the exact degree-`(p-1)` representation (entry 270).
* **`dictator_crossFieldCount_eq`** (PROVED) — `crossFieldCount q (dictator) x = #{true inputs} mod q`.
* **`modp_iff_dictator_crossFieldCount_zero`** (PROVED) — `MOD_p` fires iff the dictator cross-field count mod `p`
  is `0`: `MOD_p` is the cross-field-count object.
* **`dictator_meets_patternRich_socket`** (PROVED) — the dictator family is `AlgExpander ∧ PatternRich (2^s)`: it hits
  the antecedent of the central lower-bound socket.
* **`native_nonnative_split`** (PROVED) — the theorem-level split: (native) the exact `F_p` representation, and
  (cross-field) the identification of `MOD_p` with the dictator cross-field count.

## The central wall (named socket)

* **`NonNativeMODHard`** — the cross-field count of an `AlgExpander ∧ PatternRich` family mod `q` (`q ≠ p`) is hard:
  `PatternRichCrossFieldLowerBound` (entry 262/264), the Razborov–Smolensky obstruction.  For composite `q` it is the
  open `ACC⁰[composite]` wall (entry-238 `CarryRefinementCrossing`).

## Honest scope

This makes the native/non-native split theorem-level — native `MOD_p` is the proved exact degree-`(p-1)` `F_p`
representation; the non-native object is the proved identification of `MOD_p` with the dictator cross-field count, whose
mod-`q` hardness is the named central socket `PatternRichCrossFieldLowerBound` (already shown to follow from the proved
RS kernel modulo the single `PolynomialMethodApproximation` socket, entry 264).  The general non-native lower bound is
**not** proved (it is the wall).  This is **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0NativeNonNativeBridge

open PallLean.Paper93.DeepMath.PathB.ACC0AlgebraicExpansion (AlgExpander)
open PallLean.Paper93.DeepMath.PathB.ACC0FirePatternRichness (PatternRich)
open PallLean.Paper93.DeepMath.PathB.ACC0VaryingAffinePatterns (PatternRichCrossFieldLowerBound)

/-- **Native (easy): `MOD_p` over `F_p` has the exact degree-`(p-1)` representation (PROVED).**  The polynomial
`1 − (∑ᵢ xᵢ)^{p-1}` computes `MOD_p` exactly over `F_p`, fan-in-free (entry 270). -/
theorem modp_native_easy {p : ℕ} [Fact p.Prime] {n : ℕ} (x : Fin n → Bool) :
    ACC0ModpGate.modpPoly p x = if ACC0ModpGate.modpGate p x then 1 else 0 :=
  ACC0ModpGate.modp_native_repr x

/-- **The dictator cross-field count is the Hamming weight mod `q` (PROVED).**  For `gᵢ(x) := xᵢ`,
`crossFieldCount q (dictator) x = #{true inputs} mod q`. -/
theorem dictator_crossFieldCount_eq {q n : ℕ} (x : Fin n → Bool) :
    ACC0CrossFieldCountCore.crossFieldCount q (fun (i : Fin n) (x : Fin n → Bool) => x i) x
      = (Finset.univ.filter (fun i => x i = true)).card % q := rfl

/-- **`MOD_p` is the dictator cross-field count (PROVED).**  `MOD_p` fires iff the dictator cross-field count mod `p`
is `0` — identifying the `MOD_p` gate with the cross-field-count object of entry 251. -/
theorem modp_iff_dictator_crossFieldCount_zero {p n : ℕ} (x : Fin n → Bool) :
    ACC0ModpGate.modpGate p x = true
      ↔ ACC0CrossFieldCountCore.crossFieldCount p (fun (i : Fin n) (x : Fin n → Bool) => x i) x = 0 := by
  rw [ACC0ModpGate.modpGate_fires_iff, dictator_crossFieldCount_eq, Nat.dvd_iff_mod_eq_zero]

/-- **The dictator family hits the central lower-bound socket (PROVED).**  It is `AlgExpander` (entry 260) *and*
`PatternRich (2^s)` (entry 261) — the antecedent of `PatternRichCrossFieldLowerBound` (entry 262). -/
theorem dictator_meets_patternRich_socket {F : Type} [Field F] (s : ℕ) :
    AlgExpander (F := F) (fun (i : Fin s) (x : Fin s → Bool) => x i)
      ∧ PatternRich (fun (i : Fin s) (x : Fin s → Bool) => x i) (2 ^ s) :=
  ⟨ACC0CoFiring.dictator_algExpander s, ACC0FirePatternRichness.dictator_patternRich s⟩

/-- **The native/non-native split, theorem-level (PROVED).**  (Native) `MOD_p` has the exact degree-`(p-1)` `F_p`
representation; (cross-field) `MOD_p` is exactly the dictator cross-field count mod `p`.  The non-native hardness of
that count over `F_q` (`q ≠ p`) is the central socket `PatternRichCrossFieldLowerBound`, whose antecedent the dictator
family satisfies (`dictator_meets_patternRich_socket`). -/
theorem native_nonnative_split {p : ℕ} [Fact p.Prime] {n : ℕ} :
    (∀ x : Fin n → Bool, ACC0ModpGate.modpPoly p x = if ACC0ModpGate.modpGate p x then 1 else 0)
      ∧ (∀ x : Fin n → Bool, ACC0ModpGate.modpGate p x = true
          ↔ ACC0CrossFieldCountCore.crossFieldCount p
              (fun (i : Fin n) (x : Fin n → Bool) => x i) x = 0) :=
  ⟨fun x => modp_native_easy x, fun x => modp_iff_dictator_crossFieldCount_zero x⟩

/-- **The central wall (named socket).**  The non-native hardness: the cross-field count of an
`AlgExpander ∧ PatternRich` family mod `q` (`q ≠ p`) needs superpolynomial resources —
`PatternRichCrossFieldLowerBound` (entries 262/264).  For composite `q` this is the open `ACC⁰[composite]` wall
(entry-238 `CarryRefinementCrossing`). -/
def NonNativeMODHard {s : ℕ} (gates : Fin s → ((Fin s → Bool) → Bool)) (CrossFieldCountHard : Prop)
    (F : Type) [Field F] : Prop :=
  PatternRichCrossFieldLowerBound gates CrossFieldCountHard F

/-!
**The bridge.**  Native `MOD_p` (over `F_p`) is the proved exact degree-`(p-1)` representation (`modp_native_easy`); the
non-native object is `MOD_p` as the dictator cross-field count (`modp_iff_dictator_crossFieldCount_zero`), whose mod-`q`
hardness is the central socket `PatternRichCrossFieldLowerBound` — and the dictator family *satisfies its antecedent*
(`dictator_meets_patternRich_socket`).  Entry 264 already reduced that socket to the single `PolynomialMethodApproximation`
ingredient, and entries 264–270 proved the entire RS analytic kernel feeding it.  The split is now theorem-level: every
gate is low-degree *native*; the whole difficulty is the *non-native composite-`MOD`* lower bound, the single open wall.
Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0NativeNonNativeBridge

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NativeNonNativeBridge.modp_iff_dictator_crossFieldCount_zero
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NativeNonNativeBridge.dictator_meets_patternRich_socket
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NativeNonNativeBridge.native_nonnative_split
