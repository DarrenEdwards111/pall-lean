import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSeparationTarget
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTraceSpaceKill

/-!
# S3b: the concrete SAT verifier — spec, witness bound, and encoded-input alignment

**Step 5, brick S3b.**  The brute-force arc (and every machine in it — restoring
lookup, evaluator, loop) is shaped by the verifier convention, so the convention is
fixed *first*, spec-side, before further machines:

* `satVerify` — the SAT verifier as a total function: decode the formula from the
  prefix (the codec is prefix-consuming, so the formula/witness split needs no
  delimiter), read the leftover as the assignment (`getD`, false-padded), evaluate.
* `satWb n := 3·n² + 3` — the polynomial witness bound, **proved** sufficient: a
  variable occurring in an encoded formula has its two `Nat.pair` coordinates spelled
  in unary inside the encoding (`encodeVar'`), so its value is at most quadratic in the
  encoding length (`lit_var_bound`, via `pair_le`); evaluation only reads occurring
  variables (`evalFormula_congr`), so a satisfying assignment restricts to a witness of
  length `satWb` (`satAccept_encode`).
* `satNPObs` — the NP-observer bundle, conditional on the one machine fence
  `SatVerifierInP : PLang satVerify` (the evaluator machine — the arc's target, NOT
  asserted).  `satNPObs_acceptBool_encode`: on encoded inputs its boundary language
  *is* `SATLang` — the route's `¬ PolyCollapse` and the minimal target `SAT_not_in_P`
  are aligned at the codec.

**The convention fork (open, Darren's call).**  On *garbage* inputs `x` (not an
`encodeFormula'` image), the decoder may consume past `x` into the witness, so
`acceptBool satNPObs` and `SATLang` can disagree off the encoded sublanguage.  Full
alignment needs either (a) a normalization reduction (map every `x` to a canonical
re-encoding first) or (b) restating the target on the encoded sublanguage.  Both are
honest; the choice shapes the Cook–Levin wiring and is left explicitly open here —
nothing below depends on it.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SATVerifierSpec

open Classical
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.SeparationTarget (SATLang SATLang_encode)
open PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-! ## The verifier and the witness bound -/

/-- What the prefix-consuming decoder leaves after the formula: the witness region. -/
def satRest (z : List Bool) : List Bool :=
  (decodeClauses' (decodeNat z).1 (decodeNat z).2).2

/-- **The SAT verifier**: decode the formula from the prefix, evaluate it under the
leftover bits read as an assignment (false-padded). -/
noncomputable def satVerify (z : List Bool) : Bool :=
  evalFormula (fun v => (satRest z).getD v false) (decodeFormula' z)

/-- The polynomial witness bound. -/
def satWb (n : ℕ) : ℕ := 3 * n * n + 3

theorem satWb_poly : PolyBounded satWb := by
  refine ⟨6, 2, fun n => ?_⟩
  show 3 * n * n + 3 ≤ 6 * (n + 1) ^ 2
  have e : 6 * (n + 1) ^ 2 = 6 * (n * n) + 12 * n + 6 := by ring
  have e2 : 3 * n * n = 3 * (n * n) := by ring
  omega

/-! ## Encoded-input evaluation -/

theorem satRest_encode (φ : Formula) (w : List Bool) :
    satRest (encodeFormula' φ ++ w) = w := by
  unfold satRest
  rw [encodeFormula', List.append_assoc, decodeNat_encodeNat, decodeClauses'_flatten]

theorem decodeFormula'_encode_append (φ : Formula) (w : List Bool) :
    decodeFormula' (encodeFormula' φ ++ w) = φ := by
  unfold decodeFormula'
  rw [encodeFormula', List.append_assoc, decodeNat_encodeNat, decodeClauses'_flatten]

/-- On encoded inputs the verifier is exactly formula evaluation at the witness. -/
theorem satVerify_encode (φ : Formula) (w : List Bool) :
    satVerify (encodeFormula' φ ++ w)
      = evalFormula (fun v => w.getD v false) φ := by
  unfold satVerify
  rw [satRest_encode, decodeFormula'_encode_append]

/-! ## Evaluation reads only occurring variables -/

theorem evalClause_congr {a b : ℕ → Bool} (c : Clause)
    (h : ∀ l ∈ c, a l.1 = b l.1) : evalClause a c = evalClause b c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    simp only [evalClause, List.any_cons]
    rw [show evalLit a l = evalLit b l from by
        unfold evalLit
        rw [h l (List.mem_cons_self ..)],
      show c.any (evalLit a) = c.any (evalLit b) from
        ih fun l hl => h l (List.mem_cons_of_mem _ hl)]

theorem evalFormula_congr {a b : ℕ → Bool} (φ : Formula)
    (h : ∀ c ∈ φ, ∀ l ∈ c, a l.1 = b l.1) : evalFormula a φ = evalFormula b φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    simp only [evalFormula, List.all_cons]
    rw [show evalClause a c = evalClause b c from
        evalClause_congr c fun l hl => h c (List.mem_cons_self ..) l hl,
      show φ.all (evalClause a) = φ.all (evalClause b) from
        ih fun c hc l hl => h c (List.mem_cons_of_mem _ hc) l hl]

theorem getD_range_map (a : ℕ → Bool) (B v : ℕ) (hv : v < B) :
    ((List.range B).map a).getD v false = a v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hv]
  rfl

/-! ## The variable bound from the coordinate encoding -/

theorem pair_le (a b : ℕ) : Nat.pair a b ≤ (a + b + 1) * (a + b + 1) := by
  have e : (a + b + 1) * (a + b + 1)
      = a * a + b * b + 2 * (a * b) + 2 * a + 2 * b + 1 := by ring
  unfold Nat.pair
  split
  · omega
  · omega

theorem encodeVar'_length (v : ℕ) :
    (encodeVar' v).length
      = (v / 3).unpair.1 + (v / 3).unpair.2 + v % 3 + 3 := by
  unfold encodeVar'
  simp only [List.length_append, encodeNat_length]
  omega

/-- **The occurring-variable bound**: a literal in an encoded formula has variable
index below the witness bound — its coordinates are spelled in unary inside the
encoding, and `Nat.pair` is quadratic in them. -/
theorem lit_var_bound (φ : Formula) (c : Clause) (l : Lit) (hc : c ∈ φ) (hl : l ∈ c) :
    l.1 + 1 ≤ satWb (encodeFormula' φ).length := by
  have h3 : (encodeVar' l.1).length ≤ (encodeLit' l).length := by
    unfold encodeLit'
    simp
  have h1 : (encodeLit' l).length ≤ (encodeClause' c).length := by
    unfold encodeClause'
    have hmem : (encodeLit' l).length ∈ (c.map encodeLit').map List.length :=
      List.mem_map_of_mem (List.mem_map_of_mem hl)
    have := List.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
    simp only [List.length_append, List.length_flatten]
    omega
  have h2 : (encodeClause' c).length ≤ (encodeFormula' φ).length := by
    unfold encodeFormula'
    have hmem : (encodeClause' c).length ∈ (φ.map encodeClause').map List.length :=
      List.mem_map_of_mem (List.mem_map_of_mem hc)
    have := List.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
    simp only [List.length_append, List.length_flatten]
    omega
  set u1 := (l.1 / 3).unpair.1 with hu1
  set u2 := (l.1 / 3).unpair.2 with hu2
  set L := (encodeFormula' φ).length with hL
  have hlen : u1 + u2 + l.1 % 3 + 3 ≤ L := by
    rw [← encodeVar'_length]
    omega
  have hval : l.1 = 3 * Nat.pair u1 u2 + l.1 % 3 := by
    rw [hu1, hu2, Nat.pair_unpair]
    omega
  have hpair : Nat.pair u1 u2 ≤ (u1 + u2 + 1) * (u1 + u2 + 1) := pair_le u1 u2
  have hmono : (u1 + u2 + 1) * (u1 + u2 + 1) ≤ L * L :=
    Nat.mul_le_mul (by omega) (by omega)
  show l.1 + 1 ≤ 3 * L * L + 3
  have e : 3 * L * L = 3 * (L * L) := by ring
  omega

/-! ## The alignment at encoded inputs -/

/-- **The NP-acceptance alignment**: a polynomially bounded witness verifies the
encoded formula iff the formula is satisfiable. -/
theorem satAccept_encode (φ : Formula) :
    (∃ w : List Bool, w.length ≤ satWb (encodeFormula' φ).length
        ∧ satVerify (encodeFormula' φ ++ w) = true)
      ↔ Satisfiable φ := by
  constructor
  · rintro ⟨w, _, hv⟩
    rw [satVerify_encode] at hv
    exact ⟨_, hv⟩
  · rintro ⟨a, ha⟩
    refine ⟨(List.range (satWb (encodeFormula' φ).length)).map a, by simp, ?_⟩
    rw [satVerify_encode]
    rw [show evalFormula
          (fun v => (((List.range (satWb (encodeFormula' φ).length)).map a).getD v false))
          φ
        = evalFormula a φ from
      evalFormula_congr φ fun c hc l hl =>
        getD_range_map a _ _ (by have := lit_var_bound φ c l hc hl; omega)]
    exact ha

/-! ## The observer bundle, modulo the evaluator fence -/

/-- **The machine fence** (the arc's target, NOT asserted): the verifier is decidable
in the model's P — the CNF-evaluator machine. -/
def SatVerifierInP : Prop := PLang satVerify

/-- The concrete SAT NP-observer, conditional on the evaluator fence. -/
noncomputable def satNPObs (h : SatVerifierInP) : NPObs :=
  ⟨satVerify, satWb, satWb_poly, h⟩

/-- **The target alignment at the codec**: on encoded inputs, the observer's boundary
language is `SATLang`.  The route's `¬ PolyCollapse (satNPObs h)` speaks about the
same satisfiability facts as the minimal target, formula by formula. -/
theorem satNPObs_acceptBool_encode (h : SatVerifierInP) (φ : Formula) :
    acceptBool (satNPObs h) (encodeFormula' φ) = SATLang (encodeFormula' φ) := by
  have h1 := acceptBool_iff (satNPObs h) (encodeFormula' φ)
  have h2 : AcceptNP (satNPObs h) (encodeFormula' φ) ↔ Satisfiable φ :=
    satAccept_encode φ
  have h3 := SATLang_encode φ
  have hiff : acceptBool (satNPObs h) (encodeFormula' φ) = true
      ↔ SATLang (encodeFormula' φ) = true := (h1.trans h2).trans h3.symm
  rcases Bool.eq_false_or_eq_true (SATLang (encodeFormula' φ)) with hS | hS
  · rw [hS]
    rw [hS] at hiff
    simpa using hiff.mpr rfl
  · rw [hS]
    rw [hS] at hiff
    rcases Bool.eq_false_or_eq_true (acceptBool (satNPObs h) (encodeFormula' φ)) with
      hA | hA
    · simp [hA] at hiff
    · exact hA

end PallLean.Paper93.DeepMath.PathB.SATVerifierSpec
