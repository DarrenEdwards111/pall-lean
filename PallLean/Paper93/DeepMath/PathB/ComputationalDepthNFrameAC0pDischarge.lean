import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameAC0pApproximator
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameAC0pANDMOD
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

/-!
# The `loc` wiring: `ErrAdditive` and the RS circuit approximation (RS repair, step 4 — the close)

This plugs the input-level per-gate error bounds (`or_input_error_bound`, `and_input_error_bound`,
`modReadout_eq`) into the `List`-based approximator `approx`/`approxA` of `NFrameAC0pApproximator`, discharging
the `hAnd/hOr/hMod` hypotheses of `approx_ErrAdditive` and producing an actual Razborov–Smolensky circuit
approximation.

The approximator's local gate function `loc` is built with a *per-gate seed*: at an OR gate `(or l)` it applies
`orReadout` with a seed chosen (via `Classical.choose`) from `or_input_error_bound` for that gate's
children-value family; likewise AND; the MOD gate is exact (`modReadout`, no seed).  The `List`↔`Fin` bridges
(`any_eq_ORb_len`, `all_eq_ANDb_len`, and the sum bridge for MOD) connect the approximator's `List Bool`
children values `l.map (eval x ·)` to the `Fin l.length`-indexed families the input bounds are stated over.

Result (`rs_circuit_approximation`): there is a `loc` for which every `AC⁰[p]` circuit `C` is approximated by
`approxA loc` with

```text
  #{ x | approxA loc C x ≠ eval x C }  ≤  gateCount C · (2^n / p^t).
```

## Honest scope

A genuine Razborov–Smolensky low-degree-style circuit approximation over the `AC⁰[p]` datatype: a circuit of `s`
gates is approximated with total error `≤ s · 2^n / p^t`.  This is the classical RS ingredient, formalized — it
is **not** by itself a lower bound (that needs a hard function with no good low-degree approximant, and crucially
does not extend past a single prime — the composite-MOD wall of `NFrameCompositeMODWall` stands).  No ACC⁰ lower
bound.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameAC0pDischarge

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameFpDegree
open PallLean.Paper93.DeepMath.PathB.NFrameFpANDOR
open PallLean.Paper93.DeepMath.PathB.NFrameAC0pUnionBound
open PallLean.Paper93.DeepMath.PathB.NFrameAC0pUnionBound.AC0pCircuit
open PallLean.Paper93.DeepMath.PathB.NFrameAC0pInputError
open PallLean.Paper93.DeepMath.PathB.NFrameAC0pANDMOD
open PallLean.Paper93.DeepMath.PathB.NFrameAC0pApproximator

/-! ## `List`↔`Fin` bridges -/

/-- A general sum bridge: summing `f` over the `Fin m`-indexed `getD` family equals the list-map sum. -/
theorem sum_getD_eq {M : Type*} [AddCommMonoid M] (L : List Bool) (m : Nat) (hm : L.length = m)
    (f : Bool → M) : ∑ j : Fin m, f (L.getD j.val false) = (L.map f).sum := by
  subst hm
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hL : i < L.length := by simpa using h2
    rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem L false hL]

/-- `∃`-bridge for OR: the list's `any` equals the `Fin`-indexed `ORb`. -/
theorem any_eq_ORb_len (L : List Bool) (m : Nat) (hm : L.length = m) :
    L.any id = ORb (fun j : Fin m => L.getD j.val false) := by
  have key : (∃ x ∈ L, id x = true) ↔ (∃ j : Fin m, L.getD j.val false = true) := by
    constructor
    · rintro ⟨b, hb, hbt⟩
      obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp hb
      refine ⟨⟨i, hm ▸ hi⟩, ?_⟩
      rw [List.getD_eq_getElem L false hi, hgi]; simpa using hbt
    · rintro ⟨j, hj⟩
      have hji : j.val < L.length := hm ▸ j.isLt
      refine ⟨L[j.val], List.getElem_mem hji, ?_⟩
      simp only [id_eq]
      rw [← List.getD_eq_getElem L false hji]; exact hj
  rw [ORb, Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq]
  simpa using key

/-- `∀`-bridge for AND: the list's `all` equals the `Fin`-indexed `ANDb`. -/
theorem all_eq_ANDb_len (L : List Bool) (m : Nat) (hm : L.length = m) :
    L.all id = ANDb (fun j : Fin m => L.getD j.val false) := by
  have key : (∀ x ∈ L, id x = true) ↔ (∀ j : Fin m, L.getD j.val false = true) := by
    constructor
    · intro h j
      have hji : j.val < L.length := hm ▸ j.isLt
      rw [List.getD_eq_getElem L false hji]
      have := h L[j.val] (List.getElem_mem hji); simpa using this
    · intro h b hb
      obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp hb
      have := h ⟨i, hm ▸ hi⟩
      rw [List.getD_eq_getElem L false hi] at this
      rw [← hgi]; simpa using this
  rw [ANDb, Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_eq]
  simpa using key

/-- The `F_p`-sum of a Boolean list's images equals its `#trues` cast. -/
theorem list_boolToZMod_sum (p : Nat) [Fact p.Prime] (L : List Bool) :
    (L.map (boolToZMod p)).sum = ((L.filter id).length : ZMod p) := by
  induction L with
  | nil => simp
  | cons b t ih =>
    rw [List.map_cons, List.sum_cons, ih, List.filter_cons]
    cases b
    · simp [boolToZMod]
    · simp only [id_eq, boolToZMod, if_true, List.length_cons, Nat.cast_add, Nat.cast_one]
      ring

/-! ## The seeded `loc` -/

section
variable (p : Nat) [Fact p.Prime]

/-- Index a `List Bool` as a `Fin l.length`-indexed family (using the gate's arity `l.length`). -/
def idx {n : Nat} (l : List (AC0pCircuit p n)) (v : List Bool) : Fin l.length → Bool :=
  fun j => v.getD j.val false

/-- The children-value family of gate `l` as a function of the input. -/
def childVal {n : Nat} (l : List (AC0pCircuit p n)) (x : Fin n → Bool) : Fin l.length → Bool :=
  idx p l (l.map (fun c => eval x c))

/-- The per-gate OR seed chosen from `or_input_error_bound`. -/
noncomputable def seedOr {n : Nat} (t : Nat) (ht : 0 < t) (l : List (AC0pCircuit p n)) :
    Fin t → (Fin l.length → ZMod p) :=
  Classical.choose (or_input_error_bound p ht (childVal p l))

/-- The per-gate AND seed chosen from `and_input_error_bound`. -/
noncomputable def seedAnd {n : Nat} (t : Nat) (ht : 0 < t) (l : List (AC0pCircuit p n)) :
    Fin t → (Fin l.length → ZMod p) :=
  Classical.choose (and_input_error_bound p ht (childVal p l))

/-- The local gate function: OR/AND via the amplified readout with the per-gate seed, MOD exactly. -/
noncomputable def loc {n : Nat} (t : Nat) (ht : 0 < t) : AC0pCircuit p n → List Bool → Bool
  | .or l, v => orReadout p (seedOr p t ht l) (idx p l v)
  | .and l, v => andReadout p (seedAnd p t ht l) (idx p l v)
  | .mod l, v => modReadout p (idx p l v)
  | _, _ => false

/-! ## Discharging `hOr`, `hAnd`, `hMod` -/

theorem hOr {n : Nat} (t : Nat) (ht : 0 < t) (l : List (AC0pCircuit p n)) :
    localErr (loc p t ht) (.or l) (fun v => v.any id) l ≤ 2 ^ n / p ^ t := by
  have hp : 0 < p ^ t := pow_pos (Nat.Prime.pos Fact.out) t
  have hspec := Classical.choose_spec (or_input_error_bound p ht (childVal p l))
  have hloceq : localErr (loc p t ht) (.or l) (fun v => v.any id) l
      = (univ.filter (fun x => orReadout p (seedOr p t ht l) (childVal p l x)
          ≠ ORb (childVal p l x))).card := by
    simp only [localErr]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro x _
    have h1 : loc p t ht (.or l) (l.map (fun c => eval x c))
        = orReadout p (seedOr p t ht l) (childVal p l x) := rfl
    have h2 : (l.map (fun c => eval x c)).any id = ORb (childVal p l x) := by
      simp only [childVal]
      exact any_eq_ORb_len (l.map (fun c => eval x c)) l.length (by rw [List.length_map])
    rw [h1, h2]
  rw [Nat.le_div_iff_mul_le hp, Nat.mul_comm, hloceq]
  exact hspec

theorem hAnd {n : Nat} (t : Nat) (ht : 0 < t) (l : List (AC0pCircuit p n)) :
    localErr (loc p t ht) (.and l) (fun v => v.all id) l ≤ 2 ^ n / p ^ t := by
  have hp : 0 < p ^ t := pow_pos (Nat.Prime.pos Fact.out) t
  have hspec := Classical.choose_spec (and_input_error_bound p ht (childVal p l))
  have hloceq : localErr (loc p t ht) (.and l) (fun v => v.all id) l
      = (univ.filter (fun x => andReadout p (seedAnd p t ht l) (childVal p l x)
          ≠ ANDb (childVal p l x))).card := by
    simp only [localErr]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro x _
    have h1 : loc p t ht (.and l) (l.map (fun c => eval x c))
        = andReadout p (seedAnd p t ht l) (childVal p l x) := rfl
    have h2 : (l.map (fun c => eval x c)).all id = ANDb (childVal p l x) := by
      simp only [childVal]
      exact all_eq_ANDb_len (l.map (fun c => eval x c)) l.length (by rw [List.length_map])
    rw [h1, h2]
  rw [Nat.le_div_iff_mul_le hp, Nat.mul_comm, hloceq]
  exact hspec

theorem hMod {n : Nat} (t : Nat) (ht : 0 < t) (l : List (AC0pCircuit p n)) :
    localErr (loc p t ht) (.mod l) (fun v => decide ((v.filter id).length % p = 0)) l ≤ 2 ^ n / p ^ t := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have hz : localErr (loc p t ht) (.mod l) (fun v => decide ((v.filter id).length % p = 0)) l = 0 := by
    simp only [localErr, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _
    rw [not_not]
    show modReadout p (idx p l (l.map (fun c => eval x c)))
      = decide (((l.map (fun c => eval x c)).filter id).length % p = 0)
    rw [modReadout]
    have hsum : (∑ j, boolToZMod p (idx p l (l.map (fun c => eval x c)) j))
        = (((l.map (fun c => eval x c)).filter id).length : ZMod p) := by
      simp only [idx]
      rw [sum_getD_eq (l.map (fun c => eval x c)) l.length (by rw [List.length_map])]
      exact list_boolToZMod_sum p _
    rw [hsum]
    refine decide_eq_decide.mpr ?_
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_iff_mod_eq_zero
  rw [hz]; exact Nat.zero_le _

/-! ## The RS circuit approximation -/

/-- **Razborov–Smolensky circuit approximation over `AC⁰[p]`.**  There is a local gate function `loc` (built from
per-gate amplified-readout seeds) such that every circuit `C` is approximated by `approxA loc` with total error
at most `gateCount C · (2^n / p^t)`. -/
theorem rs_circuit_approximation {n : Nat} (t : Nat) (ht : 0 < t) (C : AC0pCircuit p n) :
    errCard (approxA (loc p t ht)) C ≤ gateCount C * (2 ^ n / p ^ t) :=
  approx_errCard_le (loc p t ht) (2 ^ n / p ^ t) (hAnd p t ht) (hOr p t ht) (hMod p t ht) C

end

end PallLean.Paper93.DeepMath.PathB.NFrameAC0pDischarge

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameAC0pDischarge.rs_circuit_approximation
