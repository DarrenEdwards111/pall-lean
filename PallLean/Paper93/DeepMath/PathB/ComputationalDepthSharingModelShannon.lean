import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCircuitUniversality
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The diagonal ingredient in the sharing model: hard functions provably exist for `cbudget`

`ArrowCollapse` located where the direct attack breaks: the missing step is a fact about the **real**
cost that a flat cost lacks — a diagonal ingredient.  This file supplies the half of that ingredient
that is real mathematics today, **in the arc's own model**: Shannon's counting bound for the
sharing-model cost `cbudget` (minimal `CGate`-list length) — hard functions provably exist.

The corpus already holds the classical Shannon theorem at Layer 8
(`Layer8ShannonExplicit.exists_function_needing_exp_size`, near-`2ⁿ/n` threshold, its own `Circuit`
model).  What is new here is the port to the **sharing model the whole meta-arc prices** — `CGate`
lists with arbitrary fan-out wire reuse, the very `cbudget` in `WhatIsLeft` — so the existence result
lands in the arc's own currency, with a `cbudget` corollary.

## The construction

* **Padding** (`pad_exact`) — every circuit extends to any exact length with the same output (append
  `un id` copy gates), so "computable within `L`" = "computable at exactly `L`".
* **Codes** (`GateCode`, `Code`) — a finite code type for length-`L` circuits: indices capped at `L`
  (`encodeGate`), semantically faithful because an out-of-range read is `false` either way
  (`getD_min_eq`, `evalGate_decode_encode`), gate-wise congruence lifted to runs (`runFrom_congr`).
* **Surjectivity** (`codeEval_hits`) — every function computable within `L` is hit by a code.
* **Counting** (`card_code`) — `|Code n L| = (n + 2 + 4(L+1) + 16(L+1)²)^L`, against `2^{2ⁿ}` functions.
* **`shannon_exists` / `shannon_exists'`** — the pigeonhole: below the threshold, some `f` is computed
  by **no** circuit of length `≤ L` — in the sharing model, where every wall-brick of the arc lives.
* **`cbudget_gt_of_all_long`** — the arc-currency corollary: such an `f` has `L < cbudget f` (given
  any circuit for `f` at all, which supplies the `sInf` nonemptiness).
* **`hard_function_exists_ten`** — a concrete instance: some 10-input function needs more than 10
  gates (`1992¹⁰ < 2^{1024}`, checked by kernel arithmetic).

## Honest scope — abundance without explicitness: the largeness barrier from the positive side

Hard functions **exist** for the arc's own `cbudget` — machine-checked, unconditional, in the model
with sharing.  But the witness is **anonymous**: counting names no explicit function, and *that* is
the natural-proofs largeness fact seen from the positive side — hardness is abundant, which is exactly
why a property capturing it is large, hence barred as a route to an **explicit** bound.  The arrow
needs the doubling for SAT *specifically*; existence supplies a nameless `f`.  Closing the gap from
"some `f` is hard" to "SAT is hard" is the explicitness step — `cost_super`.  This is the counting
half of the Kannan-direction ingredient (the diagonal); the Σ₂ machinery that *names* an escaping
class is the remaining, genuinely open-scale arc.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SharingModelShannon

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.CircuitUniversality

variable {n : ℕ}

/-! ### Padding: every circuit extends to any exact length with the same output -/

/-- Appending a copy gate (`un id` of the last wire) preserves the output. -/
theorem output_pad (c : List (CGate n)) (x : Fin n → Bool) :
    output (c ++ [CGate.un id (c.length - 1)]) x = output c x := by
  have hlen : (c ++ [CGate.un id (c.length - 1)]).length - 1 = c.length := by simp
  show (wvals x (c ++ [CGate.un id (c.length - 1)])).getD
      ((c ++ [CGate.un id (c.length - 1)]).length - 1) false
      = (wvals x c).getD (c.length - 1) false
  rw [hlen, wvals_snoc, ← wvals_length x c, getD_snoc]
  rfl

/-- **Padding (proved).**  Every circuit extends to any exact length `L ≥ its length`, same output. -/
theorem pad_exact (c : List (CGate n)) :
    ∀ L, c.length ≤ L → ∃ c' : List (CGate n), c'.length = L ∧ ∀ x, output c' x = output c x := by
  intro L
  induction L with
  | zero =>
    intro hc
    exact ⟨c, by omega, fun _ => rfl⟩
  | succ L ih =>
    intro hc
    rcases Nat.lt_or_ge L c.length with hlt | hge
    · exact ⟨c, by omega, fun _ => rfl⟩
    · obtain ⟨c', hlen, hout⟩ := ih hge
      refine ⟨c' ++ [CGate.un id (c'.length - 1)], by simp [hlen], fun x => ?_⟩
      rw [output_pad c' x, hout x]

/-! ### Codes: a finite type covering all length-`L` circuits up to semantics -/

/-- A finite code for one gate of a length-`L` circuit: indices capped at `L`. -/
abbrev GateCode (n L : ℕ) : Type :=
  Fin n ⊕ (Bool ⊕ (((Bool → Bool) × Fin (L + 1)) ⊕ ((Bool → Bool → Bool) × (Fin (L + 1) × Fin (L + 1)))))

/-- A finite code for a whole length-`L` circuit. -/
abbrev Code (n L : ℕ) : Type := Fin L → GateCode n L

/-- Boolean functions on `n` inputs. -/
abbrev BF (n : ℕ) : Type := (Fin n → Bool) → Bool

/-- Decode one gate. -/
def decodeGate {L : ℕ} : GateCode n L → CGate n
  | Sum.inl i => CGate.var i
  | Sum.inr (Sum.inl b) => CGate.cst b
  | Sum.inr (Sum.inr (Sum.inl (op, j))) => CGate.un op j.val
  | Sum.inr (Sum.inr (Sum.inr (op, j, k))) => CGate.bin op j.val k.val

/-- Encode one gate, capping wire indices at `L`. -/
def encodeGate (L : ℕ) : CGate n → GateCode n L
  | CGate.var i => Sum.inl i
  | CGate.cst b => Sum.inr (Sum.inl b)
  | CGate.un op j => Sum.inr (Sum.inr (Sum.inl (op, ⟨min j L, by omega⟩)))
  | CGate.bin op j k => Sum.inr (Sum.inr (Sum.inr (op, ⟨min j L, by omega⟩, ⟨min k L, by omega⟩)))

/-- Capping an index at `L ≥ vals.length` does not change a wire read (out-of-range is `false` both
ways). -/
theorem getD_min_eq (vals : List Bool) (j L : ℕ) (hv : vals.length ≤ L) :
    vals.getD (min j L) false = vals.getD j false := by
  rcases Nat.lt_or_ge j vals.length with hj | hj
  · rw [min_eq_left (by omega : j ≤ L)]
  · rw [getD_eq_default _ _ _ hj, getD_eq_default _ _ _ (by omega : vals.length ≤ min j L)]

/-- **Encoding is semantically faithful (proved).**  Decoding the encoded gate evaluates identically
whenever the wire list has length `≤ L`. -/
theorem evalGate_decode_encode (L : ℕ) (x : Fin n → Bool) (vals : List Bool)
    (hv : vals.length ≤ L) (g : CGate n) :
    evalGate x vals (decodeGate (encodeGate L g)) = evalGate x vals g := by
  cases g with
  | var i => rfl
  | cst b => rfl
  | un op j =>
    show op (vals.getD (min j L) false) = op (vals.getD j false)
    rw [getD_min_eq vals j L hv]
  | bin op j k =>
    show op (vals.getD (min j L) false) (vals.getD (min k L) false)
        = op (vals.getD j false) (vals.getD k false)
    rw [getD_min_eq vals j L hv, getD_min_eq vals k L hv]

/-- Gate-wise semantic congruence lifts to whole runs. -/
theorem runFrom_congr (x : Fin n → Bool) :
    ∀ (c₁ c₂ : List (CGate n)) (vals : List Bool),
      c₁.length = c₂.length →
      (∀ m, m < c₁.length → ∀ vals' : List Bool, vals'.length = vals.length + m →
        evalGate x vals' (c₁.getD m default) = evalGate x vals' (c₂.getD m default)) →
      runFrom x vals c₁ = runFrom x vals c₂ := by
  intro c₁
  induction c₁ with
  | nil =>
    intro c₂ vals hlen _
    cases c₂ with
    | nil => rfl
    | cons g gs => simp at hlen
  | cons g gs ih =>
    intro c₂ vals hlen hg
    cases c₂ with
    | nil => simp at hlen
    | cons g' gs' =>
      simp only [runFrom]
      have h0 : evalGate x vals g = evalGate x vals g' := by
        have h := hg 0 (Nat.succ_pos _) vals (by omega)
        rwa [List.getD_cons_zero, List.getD_cons_zero] at h
      rw [h0]
      apply ih gs' (vals ++ [evalGate x vals g'])
      · simp only [List.length_cons] at hlen; omega
      · intro m hm vals' hv'
        have h := hg (m + 1) (by simp only [List.length_cons]; omega) vals'
          (by simp only [List.length_append, List.length_singleton] at hv'; omega)
        rwa [List.getD_cons_succ, List.getD_cons_succ] at h

/-! ### From codes to circuits -/

/-- The circuit a code denotes. -/
def codeCircuit {L : ℕ} (f : Code n L) : List (CGate n) := List.ofFn (fun i => decodeGate (f i))

/-- The function a code computes. -/
def codeEval (n L : ℕ) (f : Code n L) : BF n := fun x => output (codeCircuit f) x

/-- `getD` on `ofFn` below the length is the function value. -/
theorem getD_ofFn {α : Type} (d : α) :
    ∀ (L : ℕ) (f : Fin L → α) (m : ℕ) (hm : m < L), (List.ofFn f).getD m d = f ⟨m, hm⟩ := by
  intro L
  induction L with
  | zero => intro f m hm; omega
  | succ L ih =>
    intro f m hm
    rw [List.ofFn_succ]
    cases m with
    | zero =>
      rw [List.getD_cons_zero]
      congr 1
    | succ m' =>
      rw [List.getD_cons_succ, ih (fun i => f i.succ) m' (by omega)]
      rfl

/-- **Every function computable within `L` is hit by a code (proved).** -/
theorem codeEval_hits (n L : ℕ) (f : BF n) (c : List (CGate n)) (hcomp : computes c f)
    (hclen : c.length ≤ L) : ∃ code : Code n L, codeEval n L code = f := by
  obtain ⟨c₁, hlen₁, hout₁⟩ := pad_exact c L hclen
  refine ⟨fun i => encodeGate L (c₁.getD i.val default), funext fun x => ?_⟩
  have hlc : (codeCircuit (n := n) (L := L)
      (fun i => encodeGate L (c₁.getD i.val default))).length = L := by
    simp only [codeCircuit, List.length_ofFn]
  have hrun : runFrom x [] (codeCircuit (fun i => encodeGate L (c₁.getD i.val default)))
      = runFrom x [] c₁ := by
    apply runFrom_congr
    · rw [hlc, hlen₁]
    · intro m hm vals' hv'
      rw [hlc] at hm
      have hv'' : vals'.length = m := by simpa using hv'
      have hgd : (codeCircuit (fun i => encodeGate L (c₁.getD i.val default))).getD m default
          = decodeGate (encodeGate L (c₁.getD m default)) := by
        simp only [codeCircuit]
        rw [getD_ofFn default L _ m hm]
      rw [hgd]
      exact evalGate_decode_encode L x vals' (by omega) (c₁.getD m default)
  calc codeEval n L (fun i => encodeGate L (c₁.getD i.val default)) x
      = (runFrom x [] (codeCircuit (fun i => encodeGate L (c₁.getD i.val default)))).getD
          ((codeCircuit (fun i => encodeGate L (c₁.getD i.val default))).length - 1) false := rfl
    _ = (runFrom x [] c₁).getD (c₁.length - 1) false := by rw [hrun, hlc, hlen₁]
    _ = output c₁ x := rfl
    _ = output c x := hout₁ x
    _ = f x := hcomp x

/-! ### The counting bound -/

/-- **Shannon in the sharing model (proved).**  If the code count is below `2^{2ⁿ}`, some function is
computed by no circuit of length `≤ L` — in the model with sharing, the arc's own cost. -/
theorem shannon_exists (n L : ℕ) (hcard : Fintype.card (Code n L) < 2 ^ 2 ^ n) :
    ∃ f : BF n, ∀ c : List (CGate n), computes c f → L < c.length := by
  by_contra hno
  push_neg at hno
  have hsurj : Function.Surjective (codeEval n L) := by
    intro f
    obtain ⟨c, hcomp, hclen⟩ := hno f
    exact codeEval_hits n L f c hcomp hclen
  have hle : Fintype.card (BF n) ≤ Fintype.card (Code n L) :=
    Fintype.card_le_of_surjective _ hsurj
  have hbf : Fintype.card (BF n) = 2 ^ 2 ^ n := by
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  omega

/-- The explicit code count: `(n + 2 + 4(L+1) + 16(L+1)²)^L`. -/
theorem card_code (n L : ℕ) :
    Fintype.card (Code n L) = (n + 2 + 4 * (L + 1) + 16 * ((L + 1) * (L + 1))) ^ L := by
  have h1 : Fintype.card (Bool → Bool) = 4 := by
    rw [Fintype.card_fun, Fintype.card_bool]
    decide
  have h2 : Fintype.card (Bool → Bool → Bool) = 16 := by
    rw [Fintype.card_fun, h1, Fintype.card_bool]
    decide
  rw [show Fintype.card (Code n L) = Fintype.card (GateCode n L) ^ L from by
    rw [Fintype.card_fun, Fintype.card_fin]]
  congr 1
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, h1, h2]
  ring

/-- **Shannon, explicit-threshold form (proved).** -/
theorem shannon_exists' (n L : ℕ)
    (h : (n + 2 + 4 * (L + 1) + 16 * ((L + 1) * (L + 1))) ^ L < 2 ^ 2 ^ n) :
    ∃ f : BF n, ∀ c : List (CGate n), computes c f → L < c.length :=
  shannon_exists n L (by rw [card_code]; exact h)

/-- **The `cbudget` corollary (proved).**  A function all of whose circuits are long has large
`cbudget` — given any circuit for it at all (the `sInf` nonemptiness). -/
theorem cbudget_gt_of_all_long {L : ℕ} (f : BF n)
    (h : ∀ c : List (CGate n), computes c f → L < c.length)
    (hex : ∃ c : List (CGate n), computes c f) : L < cbudget f := by
  obtain ⟨c₀, hc₀⟩ := hex
  have hne : {s | ∃ c : List (CGate n), computes c f ∧ c.length = s}.Nonempty :=
    ⟨c₀.length, c₀, hc₀, rfl⟩
  have hmem : cbudget f ∈ {s | ∃ c : List (CGate n), computes c f ∧ c.length = s} :=
    Nat.sInf_mem hne
  obtain ⟨c, hc, hlen⟩ := hmem
  have := h c hc
  omega

/-- **A concrete instance (proved).**  Some 10-input function is computed by no circuit with at most
10 gates: `1992¹⁰ < 2^{1024}`, checked by kernel arithmetic. -/
theorem hard_function_exists_ten :
    ∃ f : BF 10, ∀ c : List (CGate 10), computes c f → 10 < c.length := by
  apply shannon_exists' 10 10
  have h1 : (10 + 2 + 4 * (10 + 1) + 16 * ((10 + 1) * (10 + 1))) ^ 10 < 2 ^ 110 := by norm_num
  have h2 : (2 : ℕ) ^ 110 ≤ 2 ^ 1024 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have h3 : (2 : ℕ) ^ 2 ^ 10 = 2 ^ 1024 := by norm_num
  omega

end PallLean.Paper93.DeepMath.PathB.SharingModelShannon

#print axioms PallLean.Paper93.DeepMath.PathB.SharingModelShannon.shannon_exists
#print axioms PallLean.Paper93.DeepMath.PathB.SharingModelShannon.cbudget_gt_of_all_long
#print axioms PallLean.Paper93.DeepMath.PathB.SharingModelShannon.hard_function_exists_ten
