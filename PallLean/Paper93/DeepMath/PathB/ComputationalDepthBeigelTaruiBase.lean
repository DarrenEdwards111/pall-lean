import Mathlib

/-!
# Beigel–Tarui, rung 1: the polynomial-method arithmetisation base

The Beigel–Tarui socket (`ACC⁰ → SYM∘AND`) is discharged by the **polynomial method**: represent Boolean gates by
polynomials over a ring / field, then reduce degree.  This file builds the foundation that method rests on — an
**exact arithmetisation** of Boolean `AND`/`OR`/`NOT` formulas as polynomials over an arbitrary commutative ring,
proved to compute the Boolean function on Boolean inputs — together with the two facts the degree machinery uses: the
connective identities and Boolean idempotence.

  `embed b` — the ring element `1`/`0` of a Boolean `b`.
  `embed_not` / `embed_and` / `embed_or` — **PROVED**: the arithmetisations `1 - x`, `x·y`, `x + y - x·y` compute
        Boolean `NOT`/`AND`/`OR` exactly on `{0,1}`.
  `embed_idem` — **PROVED**: `embed b · embed b = embed b` (Boolean values are idempotent) — the fact that lets the
        polynomial method reduce any representing polynomial to a **multilinear** one (`x² = x`), bounding degree by the
        number of variables.
  `BForm` / `arith` / `eval` / `arith_eval` — **PROVED, the base theorem**: every `AND`/`OR`/`NOT` formula arithmetises,
        by structural induction, to a ring polynomial that computes the formula's Boolean value on every Boolean input.

## Honest scope

This is the *exact* arithmetisation — the polynomial-method base, valid over any commutative ring (in particular any
`ZMod p`).  It is **not** the Beigel–Tarui reduction.  What remains is the deep content: (i) the **degree reduction** —
the Razborov–Smolensky *probabilistic polynomial* over `F_p` approximating `AND`/`OR` with a low-degree polynomial and
small error, cutting the exact degree (up to `n`) down to `polylog`; (ii) the `MOD_m` gate arithmetisation over `F_p`
(Fermat / roots of unity); (iii) the **depth reduction** composing these into a single `SYM ∘ AND` with `m`
quasipolynomial.  Those are the crux of Beigel–Tarui; this file supplies the exact arithmetisation base they build on.
Nothing here is the Beigel–Tarui reduction, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase

variable {n : ℕ}

/-- The ring element (`1` or `0`) of a Boolean value. -/
def embed {R : Type*} [CommRing R] (b : Bool) : R := if b then 1 else 0

/-- **`NOT` arithmetises as `1 - x` (proved)**. -/
theorem embed_not {R : Type*} [CommRing R] (b : Bool) : (1 : R) - embed b = embed (!b) := by
  cases b <;> simp [embed]

/-- **`AND` arithmetises as `x · y` (proved)**. -/
theorem embed_and {R : Type*} [CommRing R] (a b : Bool) :
    (embed a : R) * embed b = embed (a && b) := by
  cases a <;> cases b <;> simp [embed]

/-- **`OR` arithmetises as `x + y - x · y` (proved)**. -/
theorem embed_or {R : Type*} [CommRing R] (a b : Bool) :
    (embed a : R) + embed b - embed a * embed b = embed (a || b) := by
  cases a <;> cases b <;> simp [embed]

/-- **Boolean idempotence (proved)**: `embed b · embed b = embed b`.  This is what lets the polynomial method reduce any
representing polynomial to a *multilinear* one (`x² = x`), so its degree is bounded by the number of variables. -/
theorem embed_idem {R : Type*} [CommRing R] (b : Bool) : (embed b : R) * embed b = embed b := by
  cases b <;> simp [embed]

/-- An `AND`/`OR`/`NOT` formula over `n` Boolean inputs. -/
inductive BForm (n : ℕ)
  | var (i : Fin n)
  | bnot (a : BForm n)
  | band (a b : BForm n)
  | bor (a b : BForm n)

/-- Boolean evaluation of a formula. -/
def BForm.eval : BForm n → (Fin n → Bool) → Bool
  | .var i, x => x i
  | .bnot a, x => !(a.eval x)
  | .band a b, x => (a.eval x) && (b.eval x)
  | .bor a b, x => (a.eval x) || (b.eval x)

/-- Ring arithmetisation of a formula: `NOT ↦ 1 - ·`, `AND ↦ ·`, `OR ↦ inclusion–exclusion`. -/
def BForm.arith {R : Type*} [CommRing R] : BForm n → (Fin n → R) → R
  | .var i, v => v i
  | .bnot a, v => 1 - a.arith v
  | .band a b, v => a.arith v * b.arith v
  | .bor a b, v => a.arith v + b.arith v - a.arith v * b.arith v

/-- **The arithmetisation base (proved)**: the ring polynomial `f.arith` computes the Boolean value `f.eval` on every
Boolean input — an exact arithmetisation of any `AND`/`OR`/`NOT` formula over any commutative ring.  This is the
foundation the Beigel–Tarui / Razborov–Smolensky degree machinery builds on. -/
theorem arith_eval {R : Type*} [CommRing R] (f : BForm n) (x : Fin n → Bool) :
    f.arith (fun i => (embed (x i) : R)) = (embed (f.eval x) : R) := by
  induction f with
  | var i => rfl
  | bnot a ih => rw [BForm.arith, ih, embed_not, BForm.eval]
  | band a b iha ihb => rw [BForm.arith, iha, ihb, embed_and, BForm.eval]
  | bor a b iha ihb => rw [BForm.arith, iha, ihb, embed_or, BForm.eval]

end PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase

#print axioms PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase.arith_eval
#print axioms PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase.embed_idem
