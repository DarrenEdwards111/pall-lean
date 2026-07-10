import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Smolensky
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4Assembly
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPCircuitComposition
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPParitySATDecider

/-!
# Interface discharge — brick 4's `RealAC0pParitySizeLowerBoundAt` from the prime capstone

Brick 4 (`no_small_ac0p_parityCNF_decider`) takes a parity `AC⁰[p]` size lower bound in the
`RealAC0pParitySizeLowerBoundAt` *interface* form as a hypothesis.  The prime capstone
(`Layer3.parity_function_lower_bound`) proves the bound in *subcircuit-count* form.  This file wires the two
together, discharging the interface hypothesis and thereby making the decider lower bound **unconditional**.

Three connectors are needed (all proved here):
* `subcircuits_card_le_size` : `#subcircuits C ≤ size C` (subcircuit-count is at most node-count);
* `boolParity_eq_decide_odd` : the repo's `parityFunction` equals the capstone's Odd-count parity form;
* `Layer4.hmod_of_isAC0p` : `IsAC0pSyntax p ⇒` all `MOD` gates in `subcircuits C` have modulus `p` (reused).

## Honest scope

Brick-4 interface discharge: turns `RealAC0pParitySizeLowerBoundAt` from a hypothesis into a theorem via the
Razborov–Smolensky capstone, giving an **unconditional** super-polynomial lower bound on `AC⁰[p]` circuits
that decide the parity-CNF family (`no_small_ac0p_parityCNF_decider_unconditional`).  This is a genuine
elementary result (`SAT`-family `∉ AC⁰[p]` at fixed depth), `sorry`-free.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPParityInterfaceDischarge

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.PvsNPCircuitComposition
open BoolCircuitSyntax

/-! ## `#subcircuits ≤ size` -/

/-- The size fold equals the initial accumulator plus the sum of child sizes. -/
theorem foldl_size_eq {n : Nat} (Cs : List (BoolCircuitSyntax n)) (a : Nat) :
    Cs.foldl (fun s C => s + C.size) a = a + (Cs.map BoolCircuitSyntax.size).sum := by
  induction Cs generalizing a with
  | nil => simp
  | cons c cs ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]; omega

/-- Length of `subcircuitsList` is the sum of the children's subcircuit-list lengths. -/
theorem subcircuitsList_length {n : Nat} (Cs : List (BoolCircuitSyntax n)) :
    (Layer3.subcircuitsList Cs).length
      = (Cs.map (fun c => (Layer3.subcircuits c).length)).sum := by
  induction Cs with
  | nil => simp [Layer3.subcircuitsList]
  | cons c cs ih =>
    rw [Layer3.subcircuitsList, List.length_append, ih, List.map_cons, List.sum_cons]

/-- **Subcircuit-count equals node-count.** -/
theorem subcircuits_length_eq_size {n : Nat} (C : BoolCircuitSyntax n) :
    (Layer3.subcircuits C).length = C.size := by
  induction C using rec_size with
  | const b => simp [Layer3.subcircuits, BoolCircuitSyntax.size]
  | input i => simp [Layer3.subcircuits, BoolCircuitSyntax.size]
  | not C ih => rw [Layer3.subcircuits, List.length_cons, ih, BoolCircuitSyntax.size]
  | andGate Cs ih =>
    have hmap : (Cs.map (fun c => (Layer3.subcircuits c).length)) = Cs.map BoolCircuitSyntax.size :=
      List.map_congr_left (fun c hc => ih c hc)
    rw [Layer3.subcircuits, List.length_cons, subcircuitsList_length, hmap,
      BoolCircuitSyntax.size, foldl_size_eq]
    omega
  | orGate Cs ih =>
    have hmap : (Cs.map (fun c => (Layer3.subcircuits c).length)) = Cs.map BoolCircuitSyntax.size :=
      List.map_congr_left (fun c hc => ih c hc)
    rw [Layer3.subcircuits, List.length_cons, subcircuitsList_length, hmap,
      BoolCircuitSyntax.size, foldl_size_eq]
    omega
  | modGate q r Cs ih =>
    have hmap : (Cs.map (fun c => (Layer3.subcircuits c).length)) = Cs.map BoolCircuitSyntax.size :=
      List.map_congr_left (fun c hc => ih c hc)
    rw [Layer3.subcircuits, List.length_cons, subcircuitsList_length, hmap,
      BoolCircuitSyntax.size, foldl_size_eq]
    omega

open Classical in
/-- **`#subcircuits ≤ size`.** -/
theorem subcircuits_card_le_size {n : Nat} (C : BoolCircuitSyntax n) :
    (Layer3.subcircuits C).toFinset.card ≤ C.size := by
  calc (Layer3.subcircuits C).toFinset.card
      ≤ (Layer3.subcircuits C).length := List.toFinset_card_le _
    _ = C.size := subcircuits_length_eq_size C

/-! ## `parityFunction` = Odd-count parity -/

/-- **The repo's `boolParity` is the capstone's Odd-count parity.** -/
theorem boolParity_eq_decide_odd : ∀ (n : Nat) (x : Fin n → Bool),
    boolParity x = decide (Odd (Finset.univ.filter (fun i => x i = true)).card)
  | 0, x => by simp [boolParity]
  | n + 1, x => by
    have hcard : (Finset.univ.filter (fun i : Fin (n + 1) => x i = true)).card
        = (if x 0 = true then 1 else 0)
          + (Finset.univ.filter (fun i : Fin n => x i.succ = true)).card := by
      rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
    rw [boolParity, boolParity_eq_decide_odd n (fun i => x i.succ), hcard]
    cases hx0 : x 0 with
    | false => simp
    | true =>
      simp only [if_true, Nat.add_comm 1, Nat.odd_add_one, decide_not, Bool.true_bne]

/-! ## Discharging the `RealAC0pParitySizeLowerBoundAt` interface -/

open Classical in
/-- **Interface discharge (PROVED unconditionally).**  The Razborov–Smolensky capstone
(`Layer3.parity_function_lower_bound`), in the `RealAC0pParitySizeLowerBoundAt` interface form: for odd prime
`p`, on `2m+1` inputs at depth `≤ d`, any `AC⁰[p]` circuit computing `PARITY` has size `≥ lower` whenever
`4·lower ≤ pᵗ` and `m` is in the RS window `8·((p-1)t)^d)² ≤ m`. -/
theorem realAC0p_parity_LB (p : ℕ) [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    (m d t : ℕ) (ht1 : 1 ≤ t) (hm : 8 * (((p - 1) * t) ^ d) ^ 2 ≤ m)
    (lower : ℕ) (hlow : 4 * lower ≤ p ^ t) :
    RealAC0pParitySizeLowerBoundAt p (2 * m + 1) d lower := by
  intro C hC hcomp hd
  have hmod := Layer4.hmod_of_isAC0p C hC
  have hpar : ∀ x : Fin (2 * m + 1) → Bool,
      C.eval x = decide (Odd (Finset.univ.filter (fun i => x i = true)).card) := by
    intro x
    rw [hcomp x]
    exact boolParity_eq_decide_odd (2 * m + 1) x
  have hcap := Layer3.parity_function_lower_bound p hp2 C hd t ht1 hpar hmod hm
  have hsub := subcircuits_card_le_size C
  omega

open Classical in
/-- **Brick 4, now unconditional.**  Combining the interface discharge with
`PvsNPParitySATDecider.no_small_ac0p_parityCNF_decider`: for odd prime `p`, any `AC⁰[p]` circuit `Dec` on
`2m+1` inputs that decides satisfiability of the parity-CNF family has size `≥ lower - 1`, where `lower` is any
value with `4·lower ≤ pᵗ` and `m` is in the RS window at depth `Dec.depth + 1`.  Taking `t ≈ m^{1/(2(d+1))}`
makes `lower` super-polynomial: **no small `AC⁰[p]` circuit decides the parity-CNF family** — a machine-checked
`SAT`-family `∉ AC⁰[p]` at fixed depth, with no remaining lower-bound hypothesis. -/
theorem no_small_ac0p_parityCNF_decider_unconditional
    (p : ℕ) [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    (m t : ℕ) (ht1 : 1 ≤ t)
    (Dec : BoolCircuitSyntax (2 * m + 1))
    (hm : 8 * (((p - 1) * t) ^ (Dec.depth + 1)) ^ 2 ≤ m)
    (hDec_ac0p : Dec.IsAC0pSyntax p)
    (hDec_sat : ∀ x : Fin (2 * m + 1) → Bool,
      Dec.eval x = true ↔ SATDepthMachine.Satisfiable
        (PvsNPParityToSAT.parityCNF (List.ofFn x)))
    (lower : ℕ) (hlow : 4 * lower ≤ p ^ t) :
    lower ≤ Dec.size + 1 := by
  have H := realAC0p_parity_LB p hp2 m (Dec.depth + 1) t ht1 hm lower hlow
  exact PvsNPParitySATDecider.no_small_ac0p_parityCNF_decider
    (2 * m + 1) p lower Dec hDec_ac0p hDec_sat H

end PallLean.Paper93.DeepMath.PathB.PvsNPParityInterfaceDischarge

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPParityInterfaceDischarge.subcircuits_card_le_size
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPParityInterfaceDischarge.boolParity_eq_decide_odd
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPParityInterfaceDischarge.realAC0p_parity_LB
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPParityInterfaceDischarge.no_small_ac0p_parityCNF_decider_unconditional
