import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCbudgetConeBound

/-!
# Densifying the dependencies: `2n − O(1) ≤ cbudget (SATFamily n)` at every length

Third rung of the attack on `∀ k, ∃ n, n^k + k < cbudget (SATFamily n)`.  Rung 1
exhibited `m` critical bits in a length-`7m+1` slice; this file makes **every position
from `22` on** critical, at **every** slice length, filling the dependency base to its
ceiling.  Two structural facts do the work:

* a dependence witness may use a **different word per coordinate**
  (`DependsOn f i` is existential in the input); and
* the decoder ignores everything after the announced clause count, so a word may end
  in arbitrary zero padding.

For a target position `i`, the witness word is the encoding of

  `(¬x_{v(d)}) ∧ (x₀) ∧ (x₀)`   with `v(d) = cellVar d 0`, `d := i − 21`,

padded with zeros to length `N`.  The first clause is satisfied by `x_{v(d)} := false`
and exists only to **steer**: its variable block has length `d + 3`, placing the final
clause's sign bit at exactly position `i`.  Flipping that bit turns the last clause
into `(¬x₀)` — satisfiable flips to unsatisfiable.  Hence every `i ∈ [22, N)` is a
genuine dependence, and with the cone bound:

  `2·(N − 22) ≤ cbudget (SATFamily N) + 1`  for every `N`.

## Honest scope

This reaches the cone method's structural ceiling (`2n − 1`) up to an additive
constant, at every length.  Any further progress must raise the **multiplicative**
constant past `2` — genuine restriction-induction gate elimination (known mathematics
up to `~(3+ε)n`), and beyond that the open wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SATFamilyDenseFloor

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex

/-! ### Decoding through trailing padding -/

theorem decodeFormula'_encode_append (φ : Formula) (rest : List Bool) :
    decodeFormula' (encodeFormula' φ ++ rest) = φ := by
  rw [encodeFormula', decodeFormula', List.append_assoc, decodeNat_encodeNat,
    decodeClauses'_flatten]

theorem SATLang_append_sat (φ : Formula) (rest : List Bool) (h : Satisfiable φ) :
    SATLang (encodeFormula' φ ++ rest) = true := by
  rw [SATLang, decodeFormula'_encode_append, if_pos h]

theorem SATLang_append_unsat (φ : Formula) (rest : List Bool) (h : ¬ Satisfiable φ) :
    SATLang (encodeFormula' φ ++ rest) = false := by
  rw [SATLang, decodeFormula'_encode_append, if_neg h]

/-! ### The steering-clause formula family -/

/-- `(¬x_{cellVar d 0}) ∧ (x₀) ∧ (x₀ or ¬x₀)`: the first clause steers the last sign
bit into position; the last two clauses conflict exactly when `s = false`. -/
def phiD (d : ℕ) (s : Bool) : Formula :=
  [[(cellVar d 0, false)], [((0 : ℕ), true)], [((0 : ℕ), s)]]

theorem cellVar_ne_zero (d : ℕ) (hd : 1 ≤ d) : cellVar d 0 ≠ 0 := by
  intro h
  have h2 : Nat.pair d 0 = 0 := by
    unfold cellVar at h
    omega
  have h3 := congrArg Nat.unpair h2
  rw [Nat.unpair_pair, Nat.unpair_zero] at h3
  have := congrArg Prod.fst h3
  simp at this
  omega

theorem satisfiable_phiD (d : ℕ) (hd : 1 ≤ d) : Satisfiable (phiD d true) := by
  refine ⟨fun v => decide (v = 0), ?_⟩
  have hne := cellVar_ne_zero d hd
  simp [phiD, evalFormula, evalClause, evalLit, hne]

theorem unsat_phiD (d : ℕ) : ¬ Satisfiable (phiD d false) := by
  rintro ⟨a, ha⟩
  simp only [phiD, evalFormula, evalClause, evalLit, List.all_cons, List.all_nil,
    List.any_cons, List.any_nil, Bool.or_false, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq] at ha
  obtain ⟨-, h2, h3⟩ := ha
  rw [h2] at h3
  simp at h3

/-! ### The encoding, split at the final sign bit -/

/-- Everything before the last clause's sign bit. -/
def densePre (d : ℕ) : List Bool :=
  encodeNat 3 ++ (encodeClause' [(cellVar d 0, false)]
    ++ (encodeClause' [((0 : ℕ), true)] ++ (encodeNat 1 ++ encodeVar' 0)))

theorem encode_phiD (d : ℕ) (s : Bool) :
    encodeFormula' (phiD d s) = densePre d ++ [s] := by
  simp [phiD, densePre, encodeFormula', encodeClause', encodeLit', List.append_assoc]

theorem densePre_length (d : ℕ) : (densePre d).length = d + 21 := by
  rw [densePre]
  simp [encodeClause', encodeLit', encodeVar'_cellVar, encodeNat_length,
    show encodeVar' 0 = [false, false, false] from rfl]
  omega

theorem encode_phiD_length (d : ℕ) (s : Bool) :
    (encodeFormula' (phiD d s)).length = d + 22 := by
  rw [encode_phiD, List.length_append, densePre_length]
  simp

/-! ### The per-position witness word -/

/-- The witness word for position `i` in a length-`N` slice: the steering encoding
followed by zero padding. -/
def denseWord (N i : ℕ) : List Bool :=
  encodeFormula' (phiD (i - 21) true) ++ List.replicate (N - i - 1) false

theorem denseWord_length (N i : ℕ) (hi : 22 ≤ i) (hiN : i < N) :
    (denseWord N i).length = N := by
  rw [denseWord, List.length_append, encode_phiD_length, List.length_replicate]
  omega

/-- Setting a list element right after a prefix, position given by hypothesis. -/
theorem set_append_cons' {α : Type} (A : List α) (x y : α) (B : List α) (i : ℕ)
    (hi : i = A.length) : (A ++ x :: B).set i y = A ++ y :: B := by
  rw [hi, set_append_cons]

/-- **The one-bit flip identity at position `i`.** -/
theorem denseWord_set (N i : ℕ) (hi : 22 ≤ i) :
    (denseWord N i).set i false
      = encodeFormula' (phiD (i - 21) false) ++ List.replicate (N - i - 1) false := by
  rw [denseWord, encode_phiD, encode_phiD, List.append_assoc, List.singleton_append,
    set_append_cons' _ _ _ _ i (by rw [densePre_length]; omega),
    List.append_assoc, List.singleton_append]

/-! ### Every position from 22 on is a genuine dependence -/

theorem wordOfFin_getD_eq {N : ℕ} (w : List Bool) (hw : w.length = N) :
    wordOfFin (fun k : Fin N => w.getD k.val false) = w := by
  apply List.ext_getElem
  · rw [wordOfFin_length, hw]
  · intro k h1 h2
    have hkN : k < N := by rwa [wordOfFin_length] at h1
    rw [wordOfFin_getElem _ k h1 hkN]
    rw [List.getD_eq_getElem w false (by omega)]

theorem dense_mem_depSet (N i : ℕ) (hi : 22 ≤ i) (hiN : i < N) :
    (⟨i, hiN⟩ : Fin N) ∈ depSet (SATFamily N) := by
  rw [mem_depSet]
  have hWlen : (denseWord N i).length = N := denseWord_length N i hi hiN
  refine ⟨fun k : Fin N => (denseWord N i).getD k.val false, false, ?_⟩
  rw [SATFamily_apply, SATFamily_apply, wordOfFin_update,
    wordOfFin_getD_eq (denseWord N i) hWlen]
  show SATLang ((denseWord N i).set i false) ≠ SATLang (denseWord N i)
  rw [denseWord_set N i hi, denseWord,
    SATLang_append_unsat _ _ (unsat_phiD (i - 21)),
    SATLang_append_sat _ _ (satisfiable_phiD (i - 21) (by omega))]
  simp

theorem depSet_card_ge_dense (N : ℕ) : N - 22 ≤ (depSet (SATFamily N)).card := by
  rcases Nat.lt_or_ge N 23 with h | h
  · omega
  · have hbound : ∀ v ∈ (Finset.range (N - 22)).image (fun d => d + 22), v < N := by
      intro v hv
      rw [Finset.mem_image] at hv
      obtain ⟨d, hd, rfl⟩ := hv
      rw [Finset.mem_range] at hd
      omega
    have hsub : Finset.attachFin ((Finset.range (N - 22)).image (fun d => d + 22)) hbound
        ⊆ depSet (SATFamily N) := by
      intro i hii
      rw [Finset.mem_attachFin, Finset.mem_image] at hii
      obtain ⟨d, hd, hdi⟩ := hii
      rw [Finset.mem_range] at hd
      have hmem := dense_mem_depSet N (d + 22) (by omega) (hdi ▸ i.isLt)
      have he : (⟨d + 22, hdi ▸ i.isLt⟩ : Fin N) = i := Fin.ext hdi
      rwa [he] at hmem
    calc N - 22 = (Finset.range (N - 22)).card := (Finset.card_range _).symm
      _ = ((Finset.range (N - 22)).image (fun d => d + 22)).card :=
          (Finset.card_image_of_injective _ (fun a b hab => by omega)).symm
      _ = (Finset.attachFin _ hbound).card := (Finset.card_attachFin _ _).symm
      _ ≤ _ := Finset.card_le_card hsub

/-! ### THE DENSE FLOOR: the cone method filled to its ceiling, at every length -/

/-- **The dense floor (proved).**  At every slice length,
`2(N − 22) ≤ cbudget (SATFamily N) + 1`. -/
theorem cbudget_SATFamily_dense (N : ℕ) :
    2 * (N - 22) ≤ cbudget (SATFamily N) + 1 := by
  have h1 := depSet_card_ge_dense N
  have h2 := cone_bound (SATFamily N)
  omega

/-- Readable form: `2N ≤ cbudget (SATFamily N) + 45` — the unconditional floor on the
exact target is now `2n − O(1)` at every length. -/
theorem cbudget_SATFamily_two_n (N : ℕ) (hN : 22 ≤ N) :
    2 * N ≤ cbudget (SATFamily N) + 45 := by
  have := cbudget_SATFamily_dense N
  omega

end PallLean.Paper93.DeepMath.PathB.SATFamilyDenseFloor

#print axioms PallLean.Paper93.DeepMath.PathB.SATFamilyDenseFloor.depSet_card_ge_dense
#print axioms PallLean.Paper93.DeepMath.PathB.SATFamilyDenseFloor.cbudget_SATFamily_dense
#print axioms PallLean.Paper93.DeepMath.PathB.SATFamilyDenseFloor.cbudget_SATFamily_two_n
