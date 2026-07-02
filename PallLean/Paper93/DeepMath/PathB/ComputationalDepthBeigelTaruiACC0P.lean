import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBeigelTaruiModGate
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBeigelTaruiToda

/-!
# Beigel–Tarui, rung 14: full `ACC⁰[p]` formulas reduce to `SYM∘AND`

Rungs 1–13 handled `AND`/`OR`/`NOT` (formulas → `SYM∘AND`) and the `MOD_p` *gate* in isolation.  This file assembles
them into a **full `ACC⁰[p]` formula type** — `AND`/`OR`/`NOT`/`MOD_p` (unbounded fan-in `MOD_p`) — arithmetises it
exactly over `F_p`, and folds the result to `SYM∘AND`.  So every `ACC⁰[p]` formula reduces exactly to the `SYM∘AND`
normal form.

  `ACCForm` — the `ACC⁰[p]` formula type: variables, `¬`, `∧`, `∨`, and unbounded-fan-in `MOD_p`.
  `ACCForm.eval` / `ACCForm.arithP` — Boolean evaluation and its arithmetisation over `F_p` (the `MOD_p` gate becomes
        `(∑ sub-polynomials)^{p-1}`, via Fermat).
  `eval_arithP` — **PROVED, exact arithmetisation**: `arithP` evaluates to the formula's Boolean value, on every gate —
        including `MOD_p` (nested-inductive structural recursion + rung 2's `fermatInd` + the count-of-accepting-subs).
  `accform_eq_symAnd` — **PROVED, the full reduction**: an `ACC⁰[p]` formula's value is `Nat.cast` of the count of
        satisfied replicated ANDs of `arithP` — the `SYM∘AND` normal form (composing `eval_arithP` with rung 11's
        Toda fold).
  `accform_iff_symAnd` — **PROVED**: the formula accepts iff that count is `1` in `F_p`.

## Honest scope

This is the **exact** `SYM∘AND` reduction of a full `ACC⁰[p]` formula (`AND`/`OR`/`NOT`/`MOD_p`), the Beigel–Tarui
normal form for the *prime-power-free* case (modulus = the field characteristic).  Two things remain for the full
Beigel–Tarui theorem over `ACC⁰[m]`: (i) **composite `MOD_m`** (`m` with ≥ 2 prime factors) — the genuinely hard case,
which is exactly the `MOD_6`/`ACC⁰[6]` two-fields *barrier this arc already proved is real* (no single field makes every
modulus low-degree; it needs Toda's `ℤ`-lifting); and (ii) the **quasipolynomial** AND count — the *low-degree* RS
approximation (rungs 3–8) in place of exact arithmetisation, giving `#monomials ≤ (n+1)^{polylog}` for depth-`d`
circuits (the exact reduction here has exponential `#monomials`).  This file supplies the full exact `ACC⁰[p]` →
`SYM∘AND` reduction, feeding the repo's `symEval`/`gateCount` count layer and `…NFrameFastSAT.symAndModel`.  Nothing here
is the Beigel–Tarui reduction over composite `ACC⁰[m]`, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0P

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.RazborovSmolensky (fermatInd)
open PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase
  (embed embed_not embed_and embed_or repCount eval_eq_repCount_cast)
open scoped Classical

variable {n : ℕ}

/-- The `ACC⁰[p]` formula type: variables, `¬`, `∧`, `∨`, and unbounded-fan-in `MOD_p`. -/
inductive ACCForm (n : ℕ)
  | var (i : Fin n)
  | bnot (a : ACCForm n)
  | band (a b : ACCForm n)
  | bor (a b : ACCForm n)
  | mod (l : List (ACCForm n))

/-- Boolean evaluation: `MOD_p` accepts iff the number of accepting sub-formulas is nonzero mod `p`. -/
def ACCForm.eval (p : ℕ) : ACCForm n → (Fin n → Bool) → Bool
  | .var i, x => x i
  | .bnot a, x => !(a.eval p x)
  | .band a b, x => a.eval p x && b.eval p x
  | .bor a b, x => a.eval p x || b.eval p x
  | .mod l, x => decide (¬ p ∣ (l.filter (fun a => a.eval p x)).length)

/-- Arithmetisation over `F_p`: the `MOD_p` gate becomes `(∑ sub-polynomials)^{p-1}` (Fermat). -/
noncomputable def ACCForm.arithP (p : ℕ) : ACCForm n → MvPolynomial (Fin n) (ZMod p)
  | .var i => X i
  | .bnot a => 1 - a.arithP p
  | .band a b => a.arithP p * b.arithP p
  | .bor a b => a.arithP p + b.arithP p - a.arithP p * b.arithP p
  | .mod l => (l.map (fun a => a.arithP p)).sum ^ (p - 1)

variable {p : ℕ} [Fact p.Prime]

/-- The sum of the sub-gates' embedded values is the count of accepting sub-gates, cast to `F_p`. -/
theorem sum_embed_eq_count (l : List (ACCForm n)) (x : Fin n → Bool) :
    (l.map (fun a => (embed (a.eval p x) : ZMod p))).sum
      = ((l.filter (fun a => a.eval p x)).length : ZMod p) := by
  induction l with
  | nil => simp [embed]
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, ih, List.filter_cons]
    cases h : a.eval p x
    · simp [embed]
    · simp only [embed, if_true, List.length_cons, Nat.cast_add, Nat.cast_one]; ring

/-- **Exact arithmetisation (proved)**: `arithP` evaluates to the `ACC⁰[p]` formula's Boolean value — on every gate,
including `MOD_p` (via `fermatInd` and the accepting-sub count). -/
theorem eval_arithP : ∀ (f : ACCForm n) (x : Fin n → Bool),
    (eval (fun i => embed (x i))) (ACCForm.arithP p f) = embed (ACCForm.eval p f x)
  | .var i, x => by simp [ACCForm.arithP, ACCForm.eval]
  | .bnot a, x => by
      rw [ACCForm.arithP, map_sub, map_one, eval_arithP a x, ACCForm.eval, embed_not]
  | .band a b, x => by
      rw [ACCForm.arithP, map_mul, eval_arithP a x, eval_arithP b x, ACCForm.eval, embed_and]
  | .bor a b, x => by
      rw [ACCForm.arithP, map_sub, map_add, map_mul, eval_arithP a x, eval_arithP b x,
        ACCForm.eval, embed_or]
  | .mod l, x => by
      rw [ACCForm.arithP, map_pow, map_list_sum, List.map_map]
      simp only [Function.comp_def]
      rw [List.map_congr_left (g := fun a => (embed (a.eval p x) : ZMod p))
        (fun a _ => eval_arithP a x)]
      rw [sum_embed_eq_count, fermatInd, ACCForm.eval]
      have hiff : ((l.filter (fun a => a.eval p x)).length : ZMod p) = 0
          ↔ p ∣ (l.filter (fun a => a.eval p x)).length := CharP.cast_eq_zero_iff (ZMod p) p _
      by_cases h : p ∣ (l.filter (fun a => a.eval p x)).length
      · rw [if_pos (hiff.mpr h)]; simp [embed, h]
      · rw [if_neg (fun hc => h (hiff.mp hc))]; simp [embed, h]

/-- **The full `ACC⁰[p]` → `SYM∘AND` reduction (proved)**: an `ACC⁰[p]` formula's value is `Nat.cast` of the count of
satisfied replicated ANDs of its arithmetisation — the `SYM∘AND` normal form.  Composes `eval_arithP` with rung 11's
Toda fold. -/
theorem accform_eq_symAnd (f : ACCForm n) (x : Fin n → Bool) :
    (embed (ACCForm.eval p f x) : ZMod p) = (repCount (ACCForm.arithP p f) x : ZMod p) := by
  rw [← eval_arithP f x, eval_eq_repCount_cast]

/-- **Acceptance read off the `SYM` top (proved)**: the `ACC⁰[p]` formula accepts iff its replicated-AND count is `1`
in `F_p`. -/
theorem accform_iff_symAnd (f : ACCForm n) (x : Fin n → Bool) :
    ACCForm.eval p f x = true ↔ (repCount (ACCForm.arithP p f) x : ZMod p) = 1 := by
  rw [← accform_eq_symAnd]
  cases h : ACCForm.eval p f x <;> simp [embed]

end PallLean.Paper93.DeepMath.PathB.ACC0P

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0P.eval_arithP
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0P.accform_eq_symAnd
