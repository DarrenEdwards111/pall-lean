import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneMul

/-!
# Kleene interpreter project — compose workhorses + rank as a Code (PROVED)

Two **workhorse** lemmas that make the per-cell-body assembly tractable (every multi-argument `Code`
application reduces cleanly), plus the rank computed as a `Code`.

  `comp_eval` — `g.eval X = some a ⇒ (comp f g).eval X = f.eval a`.
  `comp_pair_eval` — `g.eval X = some a`, `h.eval X = some b` ⇒ `(comp f (pair g h)).eval X = f.eval (pair a b)`.
  `cfgRankCode` — `cfgRankCode.eval (pair (pair E B) (pair k (pair ec n))) = (k·(E+1)+ec)·(B+1)+n`
    (`= cfgRank E B k ec n`), composing `mulCode`/`addCode`.

## What is proved (clean axioms, no `sorry`)

* `comp_eval`, `comp_pair_eval`, `cfgRankCode`, `eval_cfgRankCode`.

## Honest scope

The compose workhorses + rank-as-a-Code (for indexing sub-results).  The decode Code, the per-cell body
(`mkDispatch` + `lookupCode`), the correctness chain, the interpreter, and the runtime remain.  Nothing here
is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec

/-- **Compose workhorse (proved): `(comp f g).eval X = f.eval a` when `g.eval X = some a`.** -/
theorem comp_eval (f g : Code) (X a : ℕ) (hg : g.eval X = Part.some a) :
    (Code.comp f g).eval X = f.eval a := by
  show (g.eval X).bind f.eval = _; rw [hg, Part.bind_some]

/-- **Compose-pair workhorse (proved).** -/
theorem comp_pair_eval (f g h : Code) (X a b : ℕ)
    (hg : g.eval X = Part.some a) (hh : h.eval X = Part.some b) :
    (Code.comp f (Code.pair g h)).eval X = f.eval (Nat.pair a b) := by
  show ((Code.pair g h).eval X).bind f.eval = _
  rw [show (Code.pair g h).eval X = Part.some (Nat.pair a b) from by
        rw [show (Code.pair g h).eval X = Nat.pair <$> g.eval X <*> h.eval X from rfl, hg, hh]
        simp [Part.map_some, Seq.seq, Part.bind_some],
      Part.bind_some]

/-- The rank as a `Code` (input `pair (pair E B) (pair k (pair ec n))`). -/
def cfgRankCode : Code :=
  Code.comp addCode (Code.pair
    (Code.comp mulCode (Code.pair
      (Code.comp addCode (Code.pair
        (Code.comp mulCode (Code.pair (Code.comp Code.left Code.right)
          (Code.comp Code.succ (Code.comp Code.left Code.left))))
        (Code.comp Code.left (Code.comp Code.right Code.right))))
      (Code.comp Code.succ (Code.comp Code.right Code.left))))
    (Code.comp Code.right (Code.comp Code.right Code.right)))

/-- **Rank-as-a-Code correctness (proved): `= cfgRank E B k ec n`.** -/
theorem eval_cfgRankCode (E B k ec n : ℕ) :
    cfgRankCode.eval (Nat.pair (Nat.pair E B) (Nat.pair k (Nat.pair ec n)))
      = Part.some ((k * (E + 1) + ec) * (B + 1) + n) := by
  set X := Nat.pair (Nat.pair E B) (Nat.pair k (Nat.pair ec n)) with hX
  have hK : (Code.comp Code.left Code.right).eval X = Part.some k := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hE : (Code.comp Code.left Code.left).eval X = Part.some E := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hB : (Code.comp Code.right Code.left).eval X = Part.some B := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hEc : (Code.comp Code.left (Code.comp Code.right Code.right)).eval X = Part.some ec := by
    rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hN : (Code.comp Code.right (Code.comp Code.right Code.right)).eval X = Part.some n := by
    rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hE1 : (Code.comp Code.succ (Code.comp Code.left Code.left)).eval X = Part.some (E + 1) := by
    rw [comp_eval _ _ _ _ hE]; simp [Code.eval]
  have hB1 : (Code.comp Code.succ (Code.comp Code.right Code.left)).eval X = Part.some (B + 1) := by
    rw [comp_eval _ _ _ _ hB]; simp [Code.eval]
  have ht1 : (Code.comp mulCode (Code.pair (Code.comp Code.left Code.right)
        (Code.comp Code.succ (Code.comp Code.left Code.left)))).eval X = Part.some (k * (E + 1)) := by
    rw [comp_pair_eval _ _ _ _ _ _ hK hE1, eval_mulCode]
  have ht2 : (Code.comp addCode (Code.pair (Code.comp mulCode (Code.pair (Code.comp Code.left Code.right)
        (Code.comp Code.succ (Code.comp Code.left Code.left))))
        (Code.comp Code.left (Code.comp Code.right Code.right)))).eval X = Part.some (k * (E + 1) + ec) := by
    rw [comp_pair_eval _ _ _ _ _ _ ht1 hEc, eval_addCode]
  have ht3 : (Code.comp mulCode (Code.pair (Code.comp addCode (Code.pair (Code.comp mulCode
        (Code.pair (Code.comp Code.left Code.right) (Code.comp Code.succ (Code.comp Code.left Code.left))))
        (Code.comp Code.left (Code.comp Code.right Code.right))))
        (Code.comp Code.succ (Code.comp Code.right Code.left)))).eval X
      = Part.some ((k * (E + 1) + ec) * (B + 1)) := by
    rw [comp_pair_eval _ _ _ _ _ _ ht2 hB1, eval_mulCode]
  show cfgRankCode.eval X = _
  rw [show cfgRankCode = Code.comp addCode (Code.pair (Code.comp mulCode (Code.pair (Code.comp addCode
        (Code.pair (Code.comp mulCode (Code.pair (Code.comp Code.left Code.right)
          (Code.comp Code.succ (Code.comp Code.left Code.left))))
          (Code.comp Code.left (Code.comp Code.right Code.right))))
        (Code.comp Code.succ (Code.comp Code.right Code.left))))
      (Code.comp Code.right (Code.comp Code.right Code.right))) from rfl,
    comp_pair_eval _ _ _ _ _ _ ht3 hN, eval_addCode]

/-!
**Workhorses + rank-as-a-Code proved.**  `comp_eval`/`comp_pair_eval` streamline multi-argument `Code`
applications; `cfgRankCode` computes the table index.  The decode Code, the per-cell body, the correctness
chain, the interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_cfgRankCode
