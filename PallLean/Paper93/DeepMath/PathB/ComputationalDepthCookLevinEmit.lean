import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinReduce

/-!
# Cook–Levin M2 — the emitter's output: a faithful, poly-length bit-encoding of the tableau

The remaining obligation for a full `PolyReduces` is an actual `ComposableMachine` **transducer** that, on input `x`,
writes the tableau `tableauReduction M x clock` onto its tape in polynomial time.  Per `SCOPE_COOKLEVIN.md` that
emitter machine is a **second M1-scale construction** (in the faithful Boolean-tape model it must iterate the family
ranges, compute the `Nat.pair` variable indices on the tape, hard-wire `x`, and self-terminate — every piece hits the
same no-end-marker machinery M1 needed) and is **honestly deferred, not faked**.

What is genuine and self-contained is the emitter's **output specification**: the concrete `List Bool` the machine
must produce, and two facts about it that any emitter correctness proof rests on —

* **Faithfulness** (`decodeFormula_encodeFormula`): the emitted bits decode *back* to the exact formula, via an
  explicit self-delimiting codec.  So "the machine emits `encodeFormula φ`" faithfully means "it emits `φ`".
* **Polynomial output length** (`encodeFormula_length_le`, `tableauReduction_encode_length_le`): the bit-string is
  polynomially long — a *necessary* property of any poly-time transducer's output, and the bound the emitter's time
  bound would rest on.

This is the output half of the transducer, precise and proven.  It does **not** build the machine (the input→output
computation), which stays the research-scale gap; `EmitsTableau` states that gap exactly, unproved.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmit

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinReduce

/-! ## A self-delimiting codec `Formula ↔ List Bool` -/

/-- Encode a natural in unary: `n` ones then a terminating zero (self-delimiting). -/
def encodeNat (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- Decode the leading unary natural, returning it and the remaining bits. -/
def decodeNat : List Bool → ℕ × List Bool
  | [] => (0, [])
  | true :: bs => ((decodeNat bs).1 + 1, (decodeNat bs).2)
  | false :: bs => (0, bs)

theorem encodeNat_succ (n : ℕ) : encodeNat (n + 1) = true :: encodeNat n := by
  simp [encodeNat, List.replicate_succ]

theorem decodeNat_encodeNat (n : ℕ) (rest : List Bool) : decodeNat (encodeNat n ++ rest) = (n, rest) := by
  induction n with
  | zero => simp [encodeNat, decodeNat]
  | succ n ih =>
    rw [encodeNat_succ, List.cons_append]
    simp only [decodeNat, ih]

/-- Encode a literal: its variable (unary) then its sign bit. -/
def encodeLit (l : Lit) : List Bool := encodeNat l.1 ++ [l.2]

/-- Decode a literal. -/
def decodeLit (bs : List Bool) : Lit × List Bool :=
  (((decodeNat bs).1, (decodeNat bs).2.headD false), (decodeNat bs).2.tail)

theorem decodeLit_encodeLit (l : Lit) (rest : List Bool) : decodeLit (encodeLit l ++ rest) = (l, rest) := by
  obtain ⟨v, s⟩ := l
  simp only [encodeLit, decodeLit, List.append_assoc, List.singleton_append, decodeNat_encodeNat,
    List.headD_cons, List.tail_cons]

/-- Encode a clause: its literal count (unary) then the literals concatenated. -/
def encodeClause (c : Clause) : List Bool := encodeNat c.length ++ (c.map encodeLit).flatten

/-- Decode `k` literals in sequence. -/
def decodeLits : ℕ → List Bool → List Lit × List Bool
  | 0, bs => ([], bs)
  | k + 1, bs => ((decodeLit bs).1 :: (decodeLits k (decodeLit bs).2).1, (decodeLits k (decodeLit bs).2).2)

/-- Decode a clause. -/
def decodeClause (bs : List Bool) : Clause × List Bool := decodeLits (decodeNat bs).1 (decodeNat bs).2

theorem decodeLits_flatten (ls : List Lit) (rest : List Bool) :
    decodeLits ls.length ((ls.map encodeLit).flatten ++ rest) = (ls, rest) := by
  induction ls generalizing rest with
  | nil => simp [decodeLits]
  | cons l ls ih =>
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, decodeLits,
      decodeLit_encodeLit, ih]

theorem decodeClause_encodeClause (c : Clause) (rest : List Bool) :
    decodeClause (encodeClause c ++ rest) = (c, rest) := by
  simp only [encodeClause, decodeClause, List.append_assoc, decodeNat_encodeNat, decodeLits_flatten]

/-- Encode a formula: its clause count (unary) then the clauses concatenated. -/
def encodeFormula (φ : Formula) : List Bool := encodeNat φ.length ++ (φ.map encodeClause).flatten

/-- Decode `k` clauses in sequence. -/
def decodeClauses : ℕ → List Bool → List Clause × List Bool
  | 0, bs => ([], bs)
  | k + 1, bs =>
      ((decodeClause bs).1 :: (decodeClauses k (decodeClause bs).2).1, (decodeClauses k (decodeClause bs).2).2)

/-- Decode a whole formula. -/
def decodeFormula (bs : List Bool) : Formula := (decodeClauses (decodeNat bs).1 (decodeNat bs).2).1

theorem decodeClauses_flatten (φ : Formula) (rest : List Bool) :
    decodeClauses φ.length ((φ.map encodeClause).flatten ++ rest) = (φ, rest) := by
  induction φ generalizing rest with
  | nil => simp [decodeClauses]
  | cons c φ ih =>
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, decodeClauses,
      decodeClause_encodeClause, ih]

/-- **Faithfulness.**  The bit-encoding of a formula decodes back to exactly that formula: the emitter's output is a
faithful representation, so emitting `encodeFormula φ` *is* emitting `φ`. -/
theorem decodeFormula_encodeFormula (φ : Formula) : decodeFormula (encodeFormula φ) = φ := by
  have := decodeClauses_flatten φ []
  simp only [encodeFormula, decodeFormula, List.append_nil] at this ⊢
  rw [decodeNat_encodeNat, this]

/-! ## Polynomial output length -/

theorem encodeNat_length (n : ℕ) : (encodeNat n).length = n + 1 := by
  simp [encodeNat]

theorem encodeLit_length (l : Lit) : (encodeLit l).length = l.1 + 2 := by
  simp [encodeLit, encodeNat_length]

/-- A clause encodes to at most `(|c| + 1) + |c|·(V + 2)` bits when every literal's variable is `≤ V`. -/
theorem encodeClause_length_le (c : Clause) (V : ℕ) (hV : ∀ l ∈ c, l.1 ≤ V) :
    (encodeClause c).length ≤ (c.length + 1) + c.length * (V + 2) := by
  rw [encodeClause, List.length_append, encodeNat_length, List.length_flatten, List.map_map]
  have hsum : (c.map (List.length ∘ encodeLit)).sum ≤ (c.map (List.length ∘ encodeLit)).length • (V + 2) := by
    apply List.sum_le_card_nsmul
    intro y hy
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hy
    rw [Function.comp_apply, encodeLit_length]
    exact Nat.add_le_add_right (hV l hl) 2
  rw [List.length_map, smul_eq_mul] at hsum
  omega

/-- **Polynomial output length.**  A formula with clause count `F`, every clause `≤ L` literals, every variable `≤ V`
encodes to at most `(F + 1) + F·((L + 1) + L·(V + 2))` bits — polynomial in `F, L, V`. -/
theorem encodeFormula_length_le (φ : Formula) (V L : ℕ)
    (hL : ∀ c ∈ φ, c.length ≤ L) (hV : ∀ c ∈ φ, ∀ l ∈ c, l.1 ≤ V) :
    (encodeFormula φ).length ≤ (φ.length + 1) + φ.length * ((L + 1) + L * (V + 2)) := by
  rw [encodeFormula, List.length_append, encodeNat_length, List.length_flatten, List.map_map]
  have hsum : (φ.map (List.length ∘ encodeClause)).sum
      ≤ (φ.map (List.length ∘ encodeClause)).length • ((L + 1) + L * (V + 2)) := by
    apply List.sum_le_card_nsmul
    intro y hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
    rw [Function.comp_apply]
    exact le_trans (encodeClause_length_le c V (hV c hc))
      (by have := hL c hc; exact Nat.add_le_add (by omega) (Nat.mul_le_mul_right _ this))
  rw [List.length_map, smul_eq_mul] at hsum
  omega

/-! ## The remaining obligation, stated exactly -/

/-- **The exact remaining gap.**  A `ComposableMachine` transducer that emits the tableau bit-encoding of `x` in
polynomial time.  This is the emitter machine — a second M1-scale construction — and is **not** proved here; it is
the research-scale remainder of the observer-class `CookLevin` fence. -/
def EmitsTableau (M : Machine) (clock : ℕ → ℕ) : Prop :=
  PolyComputable (fun x => encodeFormula (tableauReduction M x (clock x.length)))

end PallLean.Paper93.DeepMath.PathB.CookLevinEmit
