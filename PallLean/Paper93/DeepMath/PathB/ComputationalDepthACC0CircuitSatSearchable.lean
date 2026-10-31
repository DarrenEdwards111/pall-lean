import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CircuitToSymAnd
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0MiniBTSize
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0YBTSocket

/-!
# Conditional ACC⁰ SAT speedup: bounded collapse ⇒ `< 2^n` search (PROVED)

The algorithmic consequence of the exact syntactic lift.  `acc0circuit_eval_hasSymAndRep` shows every
`ACC0Circuit` is *exactly* a single-count `SYM∘AND`.  Here we **size-track** that lift and feed it to the
YBT cash-out (`ybt_socket_searchable`):

  `circuitTowerSize` — the explicit collapsed size: `const ↦ 0`, `var ↦ 1`, `mod q S t ↦ |S|`,
  `not ↦` same, `and`/`or ↦ s_a·(s_b+1)+s_b` (the per-node mixed-radix merge).
  `acc0circuit_eval_hasSymAndRepSize` — `eval C` is exactly a `SYM∘AND` over `circuitTowerSize C` gates.
  `acc0circuit_sat_searchable` — **if `circuitTowerSize C + 1 < 2^n`**, then `Satisfiable (eval C)` is
  decided by a search over `< 2^n` count cells.

So any `ACC0Circuit` whose exact collapse fits under `2^n` (bounded depth + fan-in, where the mixed-radix
product stays small) has a genuine sub-`2^n` SAT search — the exact-route speedup, with the regime made
explicit.

## What is proved (clean axioms, no `sorry`)

* `hasSymAndRepSize_not/and/or` — size-tracking SYM∘AND closures (`and`/`or` via `miniBT_collapse_size`).
* `acc0circuit_eval_hasSymAndRepSize` — the size-tracking syntactic lift.
* `hasExactSymAndForm_of_size` — `HasSymAndRepSize (eval C) s` + `s+1 < 2^n` ⇒ `HasExactSymAndForm C`.
* `acc0circuit_sat_searchable` — the conditional `< 2^n` SAT search.

## Honest scope

The speedup is **conditional on `circuitTowerSize C + 1 < 2^n`** — i.e. on the *exact* collapse staying
small.  `circuitTowerSize` is the iterated mixed-radix **tower**, which for unbounded depth explodes past
`2^n`: there the hypothesis fails and this gives nothing.  Keeping the size quasipoly across unbounded
depth (so the speedup is unconditional) is the open Beigel–Tarui content.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CircuitSatSearchable

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver (gateCount symEval)
open PallLean.Paper93.DeepMath.PathB.ACC0Mod6SymAndDepth2 (satCount)
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd (monoAND)
open PallLean.Paper93.DeepMath.PathB.ACC0ModSymAndForm (monoAND_singleton)
open PallLean.Paper93.DeepMath.PathB.ACC0MiniBTSize
open PallLean.Paper93.DeepMath.PathB.ACC0YBTSocket (HasExactSymAndForm ybt_socket_searchable)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitToSymAnd (satCount_orderEmb_eq_weightOn)
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation (weightOn modQStatOn)

variable {n : ℕ}

/-! ### Size-tracking SYM∘AND closures -/

theorem hasSymAndRepSize_not {F : (Fin n → Bool) → Bool} {s : ℕ} (h : HasSymAndRepSize F s) :
    HasSymAndRepSize (fun x => !F x) s := by
  obtain ⟨supp, sym, hF⟩ := h
  exact ⟨supp, fun c => !sym c, fun x => by simp only [hF]⟩

theorem hasSymAndRepSize_and {F G : (Fin n → Bool) → Bool} {sf sg : ℕ}
    (hF : HasSymAndRepSize F sf) (hG : HasSymAndRepSize G sg) :
    HasSymAndRepSize (fun x => F x && G x) (sf * (sg + 1) + sg) := by
  obtain ⟨s1, symF, hFx⟩ := hF
  obtain ⟨s2, symG, hGx⟩ := hG
  exact miniBT_collapse_size ⟨s1, s2, fun a b => symF a && symG b, fun x => by simp only [hFx, hGx]⟩

theorem hasSymAndRepSize_or {F G : (Fin n → Bool) → Bool} {sf sg : ℕ}
    (hF : HasSymAndRepSize F sf) (hG : HasSymAndRepSize G sg) :
    HasSymAndRepSize (fun x => F x || G x) (sf * (sg + 1) + sg) := by
  obtain ⟨s1, symF, hFx⟩ := hF
  obtain ⟨s2, symG, hGx⟩ := hG
  exact miniBT_collapse_size ⟨s1, s2, fun a b => symF a || symG b, fun x => by simp only [hFx, hGx]⟩

/-- The subset MOD gate, with size `|S|`. -/
theorem modGateOn_hasSymAndRepSize (q : ℕ) (S : Finset (Fin n)) (t : ZMod q) :
    HasSymAndRepSize (fun x => decide (modQStatOn S q x = t)) S.card := by
  refine ⟨fun j => {S.orderEmbOfFin rfl j}, fun c => decide ((c : ZMod q) = t), fun x => ?_⟩
  rw [satCount_orderEmb_eq_weightOn]; rfl

/-! ### The explicit collapsed size and the size-tracking lift -/

/-- The explicit collapsed (mixed-radix tower) size of an `ACC0Circuit`. -/
def circuitTowerSize : ACC0Circuit n → ℕ
  | .const _ => 0
  | .var _ => 1
  | .not c => circuitTowerSize c
  | .and a b => circuitTowerSize a * (circuitTowerSize b + 1) + circuitTowerSize b
  | .or a b => circuitTowerSize a * (circuitTowerSize b + 1) + circuitTowerSize b
  | .mod _ S _ => S.card

/-- **The size-tracking syntactic lift (proved).**  `eval C` is exactly a `SYM∘AND` over
`circuitTowerSize C` `AND`-gates. -/
theorem acc0circuit_eval_hasSymAndRepSize (C : ACC0Circuit n) :
    HasSymAndRepSize (eval C) (circuitTowerSize C) := by
  induction C with
  | const b => exact ⟨Fin.elim0, fun _ => b, fun _ => rfl⟩
  | var i =>
    refine ⟨fun _ => {i}, fun c => decide (0 < c), fun x => ?_⟩
    show eval (ACC0Circuit.var i) x = decide (0 < satCount (fun _ : Fin 1 => ({i} : Finset (Fin n))) x)
    simp only [eval, satCount, monoAND, decide_eq_true_eq, Finset.mem_singleton, forall_eq]
    by_cases hxi : x i = true <;> simp [hxi]
  | not c ih => simp only [eval, circuitTowerSize]; exact hasSymAndRepSize_not ih
  | and a b iha ihb => simp only [eval, circuitTowerSize]; exact hasSymAndRepSize_and iha ihb
  | or a b iha ihb => simp only [eval, circuitTowerSize]; exact hasSymAndRepSize_or iha ihb
  | mod q S t => exact modGateOn_hasSymAndRepSize q S t

/-! ### Bridge to the YBT socket and the conditional SAT speedup -/

/-- **`HasSymAndRepSize` + size `< 2^n` ⇒ `HasExactSymAndForm` (proved).** -/
theorem hasExactSymAndForm_of_size {C : ACC0Circuit n} {s : ℕ}
    (h : HasSymAndRepSize (eval C) s) (hs : s + 1 < 2 ^ n) : HasExactSymAndForm C := by
  obtain ⟨supp, sym, hF⟩ := h
  refine ⟨s, supp, sym, ?_, hs⟩
  funext x
  rw [hF x]
  show sym (satCount supp x) = symEval (fun j x => monoAND (supp j) x) sym x
  unfold symEval
  congr 1
  rw [satCount, gateCount]
  exact Finset.card_filter _ _

/-- **Conditional ACC⁰ SAT speedup (proved).**  If the exact collapse fits — `circuitTowerSize C + 1 <
2^n` — then `Satisfiable (eval C)` is decided by a search over `< 2^n` count cells. -/
theorem acc0circuit_sat_searchable (C : ACC0Circuit n) (hsz : circuitTowerSize C + 1 < 2 ^ n) :
    ∃ (m : ℕ) (mono : Fin m → Finset (Fin n)) (h : ℕ → Bool),
      (Satisfiable (eval C) ↔
          ∃ c ∈ Finset.univ.image (gateCount (fun j x => monoAND (mono j) x)), h c = true)
        ∧ (Finset.univ.image (gateCount (fun j x => monoAND (mono j) x))).card < 2 ^ n :=
  ybt_socket_searchable C
    (hasExactSymAndForm_of_size (acc0circuit_eval_hasSymAndRepSize C) hsz)

/-!
**Conditional SAT speedup proved.**  Any `ACC0Circuit` with `circuitTowerSize C + 1 < 2^n` has a sub-`2^n`
SAT search — the exact-route speedup, regime explicit.  `circuitTowerSize` is the iterated mixed-radix
tower; for unbounded depth it exceeds `2^n` and the hypothesis fails.  Quasipoly-across-depth (so the
speedup becomes unconditional) is the open Beigel–Tarui content.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CircuitSatSearchable

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CircuitSatSearchable.acc0circuit_eval_hasSymAndRepSize
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CircuitSatSearchable.acc0circuit_sat_searchable
