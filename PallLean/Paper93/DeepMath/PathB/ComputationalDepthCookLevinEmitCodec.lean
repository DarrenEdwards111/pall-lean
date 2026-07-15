import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmit

/-!
# Cook–Levin M2 / emitter sub-project — E0: the emitter-friendly coordinate codec

First brick of the emitter sub-project (`SCOPE_EMITTER.md` §1, §3 E0).  The published codec
(`...CookLevinEmit.encodeFormula`) serialises a literal's variable as the **packed unary integer**
`3·Nat.pair(t,p)+tag`.  A machine emitting that must compute `Nat.pair` (a squaring/branch) and `×3` **for every
variable** — poly-many on-tape multiplications, the single largest arithmetic mountain in the emitter.

This file makes the decisive architectural choice that removes it: a **coordinate codec** `encodeFormula'` that
serialises each variable by its coordinate triple `(t, p, tag)` — three self-delimiting unary blocks — with a
**pure** decoder `decodeFormula'` reconstructing the ℕ-variable `3·Nat.pair(t,p)+tag`.  Proved here:

* **Faithfulness** (`decodeFormula'_encodeFormula'`): the coordinate bits decode back to the exact formula, so
  "the machine emits `encodeFormula' φ`" faithfully means "it emits `φ`".  The pair-arithmetic lives only in the
  pure decoder, never on the tape.
* **Emitter-friendliness** (`encodeVar'_coords`, `encodeLit'_cellVar/_headVar/_stateVar`): when the emitting loop
  holds the counters `(t, p, tag)` of a tableau variable, the codec's output for that variable is **literally the
  three unary counter blocks** — the emitter never computes `Nat.pair`.
* **Polynomial output length** (`encodeFormula'_length_le`): the coordinate form re-proves
  `encodeFormula_length_le` — coordinate blocks are at most `2V+5` bits for variables `≤ V`, still polynomial.
* **Correctness composes** (`satisfiable_decodeFormula'_encodeFormula'`): `Satisfiable` is a property of the
  abstract `Formula`, and `decodeFormula' (encodeFormula' (tableauReduction …)) = tableauReduction …`, so the
  decoded output is satisfiable iff `M` halts-and-accepts — via the existing unconditional
  `tableauReduction_correct`, no new hypothesis.

The remaining gap is restated in coordinate form as `EmitsTableau'` — the actual transducer machine (bricks
E1–E6 of `SCOPE_EMITTER.md`), still **not** built here.  The codec is a serialisation choice only: it changes the
bit-layout of the emitted object, not which formula is emitted (`codecs_agree`).  The observer-class `CookLevin`
fence stays undischarged until E6.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinReduce
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit

/-! ## The coordinate encoding of a variable

A tableau variable is `3·Nat.pair(t,p)+tag` with `tag ∈ {0,1,2}` (`cellVar`/`headVar`/`stateVar`).  The
coordinate codec recovers `(t, p, tag)` from any `v : ℕ` via the **pure** operations `Nat.unpair (v/3)` and
`v % 3`, and serialises them as three self-delimiting unary blocks (`encodeNat`, reused from the packed codec). -/

/-- Coordinate encoding of a variable: the three unary blocks `t`, `p`, `tag`, recovered purely from `v` as
`t = (v/3).unpair.1`, `p = (v/3).unpair.2`, `tag = v % 3`.  Well-defined on **any** `v : ℕ`, not only tableau
variables. -/
def encodeVar' (v : ℕ) : List Bool :=
  encodeNat (v / 3).unpair.1 ++ encodeNat (v / 3).unpair.2 ++ encodeNat (v % 3)

/-- Decode a coordinate-encoded variable: read three unary blocks `t`, `p`, `tag` and reconstruct the ℕ-variable
`3·Nat.pair(t,p)+tag`.  The pair-arithmetic lives **here**, in the pure decoder — never on the emitter's tape. -/
def decodeVar' (bs : List Bool) : ℕ × List Bool :=
  (3 * Nat.pair (decodeNat bs).1 (decodeNat (decodeNat bs).2).1
      + (decodeNat (decodeNat (decodeNat bs).2).2).1,
    (decodeNat (decodeNat (decodeNat bs).2).2).2)

theorem decodeVar'_encodeVar' (v : ℕ) (rest : List Bool) :
    decodeVar' (encodeVar' v ++ rest) = (v, rest) := by
  simp only [encodeVar', decodeVar', List.append_assoc, decodeNat_encodeNat, Nat.pair_unpair,
    Nat.div_add_mod]

/-- The coordinate encoding is injective (immediate from faithfulness): distinct variables have distinct
coordinate blocks, so the M1 SAT verifier consuming this output can test variable identity by
coordinate-tuple equality — also without computing `Nat.pair`. -/
theorem encodeVar'_injective : Function.Injective encodeVar' := by
  intro v w h
  have hv := decodeVar'_encodeVar' v []
  have hw := decodeVar'_encodeVar' w []
  rw [List.append_nil] at hv hw
  rw [h, hw] at hv
  exact (congrArg Prod.fst hv).symm

/-! ## Emitter-friendliness: coordinates in, coordinates out

The decisive property (`SCOPE_EMITTER.md` §1).  When the emitting loop reaches index tuple `(t, p)` and emits a
variable of tag `tag`, it *already holds* `t`, `p`, `tag` as unary counters — and the codec's output for that
variable is **literally those three counter blocks**.  No `Nat.pair`, no `×3`, no per-variable arithmetic. -/

/-- **Emitter-friendliness.**  For a tableau variable given by its coordinates, the coordinate encoding is
exactly the three unary counter blocks. -/
theorem encodeVar'_coords (t p tag : ℕ) (htag : tag < 3) :
    encodeVar' (3 * Nat.pair t p + tag) = encodeNat t ++ encodeNat p ++ encodeNat tag := by
  rw [encodeVar', show (3 * Nat.pair t p + tag) / 3 = Nat.pair t p from by omega,
    show (3 * Nat.pair t p + tag) % 3 = tag from by omega, Nat.unpair_pair]

theorem encodeVar'_cellVar (t p : ℕ) :
    encodeVar' (cellVar t p) = encodeNat t ++ encodeNat p ++ encodeNat 0 := by
  unfold cellVar
  have h := encodeVar'_coords t p 0 (by omega)
  rwa [Nat.add_zero] at h

theorem encodeVar'_headVar (t p : ℕ) :
    encodeVar' (headVar t p) = encodeNat t ++ encodeNat p ++ encodeNat 1 :=
  encodeVar'_coords t p 1 (by omega)

theorem encodeVar'_stateVar (t q : ℕ) :
    encodeVar' (stateVar t q) = encodeNat t ++ encodeNat q ++ encodeNat 2 :=
  encodeVar'_coords t q 2 (by omega)

/-! ## Literals, clauses, formulas — mirroring the packed codec structure -/

/-- Encode a literal: its variable's coordinate blocks then its sign bit. -/
def encodeLit' (l : Lit) : List Bool := encodeVar' l.1 ++ [l.2]

/-- Decode a literal. -/
def decodeLit' (bs : List Bool) : Lit × List Bool :=
  (((decodeVar' bs).1, (decodeVar' bs).2.headD false), (decodeVar' bs).2.tail)

theorem decodeLit'_encodeLit' (l : Lit) (rest : List Bool) :
    decodeLit' (encodeLit' l ++ rest) = (l, rest) := by
  obtain ⟨v, s⟩ := l
  simp only [encodeLit', decodeLit', List.append_assoc, List.singleton_append,
    decodeVar'_encodeVar', List.headD_cons, List.tail_cons]

/-- What E3's template emitters will write for a cell literal: the loop's counters, verbatim. -/
theorem encodeLit'_cellVar (t p : ℕ) (s : Bool) :
    encodeLit' (cellVar t p, s) = encodeNat t ++ encodeNat p ++ encodeNat 0 ++ [s] := by
  simp only [encodeLit', encodeVar'_cellVar]

/-- What E3's template emitters will write for a head literal: the loop's counters, verbatim. -/
theorem encodeLit'_headVar (t p : ℕ) (s : Bool) :
    encodeLit' (headVar t p, s) = encodeNat t ++ encodeNat p ++ encodeNat 1 ++ [s] := by
  simp only [encodeLit', encodeVar'_headVar]

/-- What E3's template emitters will write for a state literal: the loop's counters, verbatim. -/
theorem encodeLit'_stateVar (t q : ℕ) (s : Bool) :
    encodeLit' (stateVar t q, s) = encodeNat t ++ encodeNat q ++ encodeNat 2 ++ [s] := by
  simp only [encodeLit', encodeVar'_stateVar]

/-- Encode a clause: its literal count (unary) then the literals concatenated. -/
def encodeClause' (c : Clause) : List Bool := encodeNat c.length ++ (c.map encodeLit').flatten

/-- Decode `k` literals in sequence. -/
def decodeLits' : ℕ → List Bool → List Lit × List Bool
  | 0, bs => ([], bs)
  | k + 1, bs => ((decodeLit' bs).1 :: (decodeLits' k (decodeLit' bs).2).1, (decodeLits' k (decodeLit' bs).2).2)

/-- Decode a clause. -/
def decodeClause' (bs : List Bool) : Clause × List Bool := decodeLits' (decodeNat bs).1 (decodeNat bs).2

theorem decodeLits'_flatten (ls : List Lit) (rest : List Bool) :
    decodeLits' ls.length ((ls.map encodeLit').flatten ++ rest) = (ls, rest) := by
  induction ls generalizing rest with
  | nil => simp [decodeLits']
  | cons l ls ih =>
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, decodeLits',
      decodeLit'_encodeLit', ih]

theorem decodeClause'_encodeClause' (c : Clause) (rest : List Bool) :
    decodeClause' (encodeClause' c ++ rest) = (c, rest) := by
  simp only [encodeClause', decodeClause', List.append_assoc, decodeNat_encodeNat, decodeLits'_flatten]

/-- Encode a formula: its clause count (unary) then the clauses concatenated. -/
def encodeFormula' (φ : Formula) : List Bool := encodeNat φ.length ++ (φ.map encodeClause').flatten

/-- Decode `k` clauses in sequence. -/
def decodeClauses' : ℕ → List Bool → List Clause × List Bool
  | 0, bs => ([], bs)
  | k + 1, bs =>
      ((decodeClause' bs).1 :: (decodeClauses' k (decodeClause' bs).2).1,
        (decodeClauses' k (decodeClause' bs).2).2)

/-- Decode a whole formula. -/
def decodeFormula' (bs : List Bool) : Formula := (decodeClauses' (decodeNat bs).1 (decodeNat bs).2).1

theorem decodeClauses'_flatten (φ : Formula) (rest : List Bool) :
    decodeClauses' φ.length ((φ.map encodeClause').flatten ++ rest) = (φ, rest) := by
  induction φ generalizing rest with
  | nil => simp [decodeClauses']
  | cons c φ ih =>
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, decodeClauses',
      decodeClause'_encodeClause', ih]

/-- **Faithfulness.**  The coordinate bit-encoding of a formula decodes back to exactly that formula: the
emitter's output under the coordinate codec is a faithful representation, so emitting `encodeFormula' φ` *is*
emitting `φ`. -/
theorem decodeFormula'_encodeFormula' (φ : Formula) : decodeFormula' (encodeFormula' φ) = φ := by
  have := decodeClauses'_flatten φ []
  simp only [encodeFormula', decodeFormula', List.append_nil] at this ⊢
  rw [decodeNat_encodeNat, this]

/-- The two codecs carry the same abstract content: both decode their own encoding back to `φ`.  The coordinate
codec is a **serialisation choice only** — it changes the bit-layout, not which formula is emitted. -/
theorem codecs_agree (φ : Formula) :
    decodeFormula' (encodeFormula' φ) = decodeFormula (encodeFormula φ) := by
  rw [decodeFormula'_encodeFormula', decodeFormula_encodeFormula]

/-! ## Polynomial output length — the coordinate form of `encodeFormula_length_le` -/

/-- Exact length of a coordinate variable block, in terms of the coordinates: `t + p + tag + 3` bits.  This is
the per-variable tape cost E6's clock bound will account against (`≤ B + P + 5` inside the family loops). -/
theorem encodeVar'_coords_length (t p tag : ℕ) (htag : tag < 3) :
    (encodeVar' (3 * Nat.pair t p + tag)).length = t + p + tag + 3 := by
  rw [encodeVar'_coords t p tag htag]
  simp only [List.length_append, encodeNat_length]
  omega

/-- A coordinate variable block for `v ≤ V` is at most `2V + 5` bits: each of `t = (v/3).unpair.1` and
`p = (v/3).unpair.2` is `≤ v/3 ≤ V`, and `tag = v % 3 ≤ 2`.  Compare `v + 1` bits for the packed codec — the
coordinate form is at most a constant factor longer, still polynomial. -/
theorem encodeVar'_length_le (v V : ℕ) (hv : v ≤ V) : (encodeVar' v).length ≤ 2 * V + 5 := by
  have h1 : (v / 3).unpair.1 ≤ V :=
    le_trans (Nat.unpair_left_le _) (le_trans (Nat.div_le_self v 3) hv)
  have h2 : (v / 3).unpair.2 ≤ V :=
    le_trans (Nat.unpair_right_le _) (le_trans (Nat.div_le_self v 3) hv)
  have h3 : v % 3 ≤ 2 := by omega
  simp only [encodeVar', List.length_append, encodeNat_length]
  omega

theorem encodeLit'_length_le (l : Lit) (V : ℕ) (hv : l.1 ≤ V) :
    (encodeLit' l).length ≤ 2 * V + 6 := by
  have h := encodeVar'_length_le l.1 V hv
  simp only [encodeLit', List.length_append, List.length_cons, List.length_nil]
  omega

/-- A clause encodes to at most `(|c| + 1) + |c|·(2V + 6)` bits when every literal's variable is `≤ V` — the
coordinate form of `encodeClause_length_le`. -/
theorem encodeClause'_length_le (c : Clause) (V : ℕ) (hV : ∀ l ∈ c, l.1 ≤ V) :
    (encodeClause' c).length ≤ (c.length + 1) + c.length * (2 * V + 6) := by
  rw [encodeClause', List.length_append, encodeNat_length, List.length_flatten, List.map_map]
  have hsum : (c.map (List.length ∘ encodeLit')).sum
      ≤ (c.map (List.length ∘ encodeLit')).length • (2 * V + 6) := by
    apply List.sum_le_card_nsmul
    intro y hy
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hy
    rw [Function.comp_apply]
    exact encodeLit'_length_le l V (hV l hl)
  rw [List.length_map, smul_eq_mul] at hsum
  omega

/-- **Polynomial output length.**  A formula with clause count `F`, every clause `≤ L` literals, every variable
`≤ V` encodes under the coordinate codec to at most `(F + 1) + F·((L + 1) + L·(2V + 6))` bits — polynomial in
`F, L, V`, the coordinate form of `encodeFormula_length_le`. -/
theorem encodeFormula'_length_le (φ : Formula) (V L : ℕ)
    (hL : ∀ c ∈ φ, c.length ≤ L) (hV : ∀ c ∈ φ, ∀ l ∈ c, l.1 ≤ V) :
    (encodeFormula' φ).length ≤ (φ.length + 1) + φ.length * ((L + 1) + L * (2 * V + 6)) := by
  rw [encodeFormula', List.length_append, encodeNat_length, List.length_flatten, List.map_map]
  have hsum : (φ.map (List.length ∘ encodeClause')).sum
      ≤ (φ.map (List.length ∘ encodeClause')).length • ((L + 1) + L * (2 * V + 6)) := by
    apply List.sum_le_card_nsmul
    intro y hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
    rw [Function.comp_apply]
    exact le_trans (encodeClause'_length_le c V (hV c hc))
      (by have := hL c hc; exact Nat.add_le_add (by omega) (Nat.mul_le_mul_right _ this))
  rw [List.length_map, smul_eq_mul] at hsum
  omega

/-! ## Correctness composes through the coordinate codec -/

/-- **Correctness composes.**  `Satisfiable` is a property of the abstract `Formula`; since the coordinate codec
is faithful, the decoded emitter output is satisfiable iff `M` halts-and-accepts — directly from the existing
unconditional `tableauReduction_correct`, with no new hypothesis.  This is why the codec swap is free. -/
theorem satisfiable_decodeFormula'_encodeFormula' (M : Machine) (x : List Bool) (clock : ℕ) :
    Satisfiable (decodeFormula' (encodeFormula' (tableauReduction M x clock)))
      ↔ (HaltsBy M x clock ∧ decideOut M x clock = true) := by
  rw [decodeFormula'_encodeFormula']
  exact tableauReduction_correct M x clock

/-! ## The remaining obligation, restated in coordinate form -/

/-- **The exact remaining gap, coordinate form.**  A `ComposableMachine` transducer that emits the coordinate
bit-encoding of the tableau of `x` in polynomial time.  This is the emitter machine — bricks E1–E6 of
`SCOPE_EMITTER.md` — and is **not** proved here; it is the research-scale remainder of the observer-class
`CookLevin` fence.  Relative to `EmitsTableau`, only the serialisation differs (`codecs_agree`); the emitted
formula, its satisfiability, and its poly-size are identical. -/
def EmitsTableau' (M : Machine) (clock : ℕ → ℕ) : Prop :=
  PolyComputable (fun x => encodeFormula' (tableauReduction M x (clock x.length)))

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
