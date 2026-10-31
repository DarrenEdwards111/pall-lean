import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RSAgreementBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BTClosureFrontier

/-!
# The final integration — `DynamicClosesAtBT`, proved for the AC⁰[p] route, chained to `¬ NEXP`

This is the culmination of the BT-closure arc (entries 166–178).  Entry 175 left `DynamicClosesAtBT` as an abstract
socket; the per-route work then proved its mathematical content: the AC⁰[p] route has a *complete* Beigel–Tarui
representation — low degree, quasipolynomial size, and bounded error, all proved together (`rs_agreement_BT`, entry
177); the composite route is assembled from the proved CRT (entry 171), prime-power mixed-radix `SYM∘AND` (entry 174),
and mixed-radix quasipoly size (entry 178).

Here we make `DynamicClosesAtBT` a **proved theorem, not a socket**, for the AC⁰[p] route: `DynamicClosesAtBT_AC0p`
states that *every* AC⁰[p] `BoolCircuitSyntax` circuit has a complete BT representation, and `dynamicClosesAtBT_AC0p_proved`
proves it (universally) from `rs_agreement_BT`.  Then `acc0p_BTclosure_to_NEXP` plugs the *proved* closure into the
entry-166 chain, so `¬ NEXPHasACC0Circuits` follows from the **Williams sockets alone** — the entire Beigel–Tarui
(closure) side is now discharged for AC⁰[p].

## What is proved (clean axioms, no `sorry`)

* **`DynamicClosesAtBT_AC0p` / `dynamicClosesAtBT_AC0p_proved`** — the BT closure for AC⁰[p], PROVED: every AC⁰[p]
  circuit has a complete BT representation (∃ form `ω` with polylog degree, quasipoly `SYM∘AND` size, and bounded
  error).  This is `DynamicClosesAtBT` as a *theorem* for the AC⁰[p] route, not a socket.
* **`acc0p_BTclosure_to_NEXP`** — the proved AC⁰[p] closure chained through entry 166 to `¬ NEXPHasACC0Circuits`: with
  the closure discharged, only the Williams sockets (`closure_to_quasi`, `quasi_to_speed`, `williams`, `hierarchy`)
  remain.

## Honest scope

For the **AC⁰[p] route** `DynamicClosesAtBT` is now a genuinely *proved* theorem (the complete BT representation), and the
chain to `¬ NEXP` rests only on the Williams meta-theorem sockets — which are themselves `NEXP ⊄ ACC⁰`-strength named
classical theorems (Williams 2011), not BT content.  For **arbitrary `ACC⁰`** (composite modulus) the closure is *not*
collapsed into this one theorem: it is assembled from the proved per-route pieces — CRT per-prime decomposition (entry
171), prime-power exact mixed-radix `SYM∘AND` (entry 174), the per-prime complete representation over each `F_{pᵢ}`
(entry 177), and the mixed-radix quasipoly size for the constant number of prime factors (entry 178) — with the
cross-route bookkeeping (decomposing a composite circuit's correctness per prime) as the remaining integration.
Beigel–Tarui and `NEXP ⊄ ACC⁰` (Williams 2011) are proven classical theorems ⇒ formalisation, not an open problem.
NOT a new separation, NOT `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0DynamicClosesAtBTComplete

open scoped Classical
open MvPolynomial Finset
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Layer3

/-- **`DynamicClosesAtBT` for the AC⁰[p] route (concrete).**  Every AC⁰[p] `BoolCircuitSyntax` circuit `C` (every `MOD`
gate has modulus `p`) has a complete Beigel–Tarui representation: a form choice `ω` whose RS approximant
`toAgree p t (oracleOf p t C ω) C` has polylog degree `≤ ((p−1)·t)^{depth}`, quasipoly `SYM∘AND` size
`≤ (n+1)^{((p−1)·t)^{depth}}`, and bounded error `· p^t ≤ (#subcircuits)·2^n`. -/
def DynamicClosesAtBT_AC0p (p t : ℕ) [Fact p.Prime] : Prop :=
  ∀ {n : ℕ} (C : BoolCircuitSyntax n),
    (∀ q r cs, (BoolCircuitSyntax.modGate q r cs : BoolCircuitSyntax n) ∈ subcircuits C → q = p) →
    ∃ ω : FormSpace p t C,
      (toAgree p t (oracleOf p t C ω) C).totalDegree ≤ ((p - 1) * t) ^ C.depth
      ∧ ((toAgree p t (oracleOf p t C ω) C).support.image (fun d => d.support)).card
          ≤ (n + 1) ^ (((p - 1) * t) ^ C.depth)
      ∧ (Finset.univ.filter (fun x : Fin n → Bool =>
            eval (fun i => boolToZMod p (x i)) (toAgree p t (oracleOf p t C ω) C)
              ≠ boolToZMod p (C.eval x))).card * p ^ t
          ≤ (subcircuits C).toFinset.card * Fintype.card (Fin n → Bool)

/-- **`DynamicClosesAtBT` is PROVED for the AC⁰[p] route (not a socket).**  Universally, from `rs_agreement_BT` (entry
177): every AC⁰[p] circuit has the complete BT representation. -/
theorem dynamicClosesAtBT_AC0p_proved (p t : ℕ) [Fact p.Prime] (ht : 1 ≤ t) :
    DynamicClosesAtBT_AC0p p t :=
  fun C hmod => ACC0RSAgreementBound.rs_agreement_BT p t ht C hmod

/-- **The proved AC⁰[p] closure chained to `¬ NEXPHasACC0Circuits` (the BT side fully discharged).**  Plugging the
*proved* `DynamicClosesAtBT_AC0p` into the entry-166 chain, `¬ NEXPHasACC0Circuits` follows from the Williams sockets
alone — the entire Beigel–Tarui (closure) side is discharged for AC⁰[p].  The remaining premises
(`closure_to_quasi`, `quasi_to_speed`, `williams`, `hierarchy`) are the named Williams meta-theorem sockets, not BT
content. -/
theorem acc0p_BTclosure_to_NEXP (p t : ℕ) [Fact p.Prime] (ht : 1 ≤ t)
    {BTQuasi ACC0Speed NEXPC Collapse : Prop}
    (closure_to_quasi : DynamicClosesAtBT_AC0p p t → BTQuasi)
    (quasi_to_speed : BTQuasi → ACC0Speed)
    (williams : ACC0Speed → NEXPC → Collapse)
    (hierarchy : ¬ Collapse) : ¬ NEXPC :=
  ACC0BTClosureFrontier.dynamicClosure_to_NEXP_not_ACC0
    (DynamicClosesAtBT_AC0p p t) BTQuasi ACC0Speed NEXPC Collapse
    (dynamicClosesAtBT_AC0p_proved p t ht) closure_to_quasi quasi_to_speed williams hierarchy

end PallLean.Paper93.DeepMath.PathB.ACC0DynamicClosesAtBTComplete

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DynamicClosesAtBTComplete.dynamicClosesAtBT_AC0p_proved
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DynamicClosesAtBTComplete.acc0p_BTclosure_to_NEXP
