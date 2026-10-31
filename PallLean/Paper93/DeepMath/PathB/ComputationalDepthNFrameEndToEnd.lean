import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameRAMEncoding

/-!
# N-Frame: the end-to-end capstone — a machine's real run, unconditionally through the pipeline

Every prior machine theorem took the dynamics (`hdec`) as a hypothesis.  This capstone **discharges it**: it proves the
scan-RAM's actual `R`-step run computes the parity of its memory, and pushes that through the whole pipeline to a fully
**unconditional** circuit bound for a concrete function family.  Any error in any brick — rebasing, layers, tableau,
assembly, embedding, RAM gadgets — would break this theorem; its clean compilation is the smoke test of the entire
simulation arc.

  `runAcc` / `scan_run` — **PROVED, the dynamics**: from any configuration with a one-hot pointer at `p`, accumulator
        `a`, and memory `x`, the machine's `T`-step run leaves the accumulator at `a ⊕ x[p] ⊕ x[p+1] ⊕ …` (`T` terms,
        cyclically) — an invariant induction over the actual `iterStep` semantics.
  `runAcc_eq_parity` — **PROVED, the arithmetic**: the `R`-step scan from pointer `0` accumulates exactly `parityFn R`.
  `ram_parity_cbudget` — **PROVED, UNCONDITIONAL**: `cbudget (parityFn R) ≤ (2R+1) + R·((2R+1)·(4R+3)) + 1` — no
        hypotheses; a concrete machine, its proven run, a concrete circuit bound.

## Honest scope

The bound is `O(R³)` — far from tight (the direct XOR chain gives `≤ 2R+1`); the point is not the constant but the
**zero-hypothesis end-to-end chain**: machine dynamics → tableau → circuit, every link proved.  This also demonstrates
that the `hdec`/`hinit`-style hypotheses of the machine theorems are genuinely dischargeable, not hidden sockets.  The
open target `NFrameCircuitLowerBoundTarget SAT` is untouched.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {R : ℕ}

/-! ### The reference dynamics -/

/-- The reference accumulator: `T` scan steps from absolute pointer position `p`. -/
def runAcc (x : Fin R → Bool) (hR : 0 < R) (a : Bool) : ℕ → ℕ → Bool
  | _, 0 => a
  | p, T + 1 => runAcc x hR (xor a (x ⟨p % R, Nat.mod_lt _ hR⟩)) (p + 1) T

/-- The scan-RAM's input embedding: pointer one-hot at `0`, accumulator `false`, memory = the input. -/
def scanInp (R : ℕ) (j : Fin (R + 1 + R)) : Sum (Fin R) Bool :=
  if hj : j.val < R then Sum.inr (decide (j.val = 0))
  else if h2 : j.val = R then Sum.inr false
  else Sum.inl ⟨j.val - (R + 1), by have := j.isLt; omega⟩

/-! ### The dynamics theorem -/

/-- **The scan-RAM's run (proved)**: from a one-hot pointer at `p % R`, accumulator `a`, memory `x`, the `T`-step run
leaves the accumulator at `runAcc x a p T` — the machine genuinely scans. -/
theorem scan_run (x : Fin R → Bool) (hR : 0 < R) :
    ∀ (T p : ℕ) (a : Bool) (cfg : Fin (R + 1 + R) → Bool),
      (∀ i : Fin R, cfg (aIdx i) = decide (i.val = p % R)) →
      cfg accIdx = a →
      (∀ i : Fin R, cfg (mIdx i) = x i) →
      iterStep (ramStep (R := R)) T cfg accIdx = runAcc x hR a p T := by
  intro T
  induction T with
  | zero =>
    intro p a cfg hA hacc hmem
    exact hacc
  | succ T ih =>
    intro p a cfg hA hacc hmem
    -- the stepped configuration satisfies the invariant at pointer p+1
    show iterStep (ramStep (R := R)) T (fun j => ramStep j cfg) accIdx = _
    have hA' : ∀ i : Fin R, ramStep (aIdx i) cfg = decide (i.val = (p + 1) % R) := by
      intro i
      have hilt := i.isLt
      have hplt : p % R < R := Nat.mod_lt _ hR
      unfold ramStep
      rw [dif_pos (show (aIdx i).val < R from hilt)]
      refine (hA _).trans ?_
      rw [decide_eq_decide]
      show (i.val + R - 1) % R = p % R ↔ i.val = (p + 1) % R
      have h2 : (p + 1) % R = (p % R + 1) % R := (Nat.mod_add_mod p R 1).symm
      by_cases hi0 : i.val = 0
      · have h1 : (i.val + R - 1) % R = R - 1 := by
          rw [hi0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
        rw [h1, hi0]
        by_cases hp : p % R = R - 1
        · have h3 : (p + 1) % R = 0 := by
            rw [h2, hp, show R - 1 + 1 = R from by omega, Nat.mod_self]
          rw [h3, hp]
          simp
        · have h3 : (p + 1) % R = p % R + 1 := by
            rw [h2, Nat.mod_eq_of_lt (by omega)]
          rw [h3]
          constructor
          · intro h; omega
          · intro h; omega
      · have h1 : (i.val + R - 1) % R = i.val - 1 := by
          rw [show i.val + R - 1 = (i.val - 1) + R from by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
        rw [h1]
        by_cases hp : p % R = R - 1
        · have h3 : (p + 1) % R = 0 := by
            rw [h2, hp, show R - 1 + 1 = R from by omega, Nat.mod_self]
          rw [h3]
          constructor
          · intro h; omega
          · intro h; omega
        · have h3 : (p + 1) % R = p % R + 1 := by
            rw [h2, Nat.mod_eq_of_lt (by omega)]
          rw [h3]
          constructor
          · intro h; omega
          · intro h; omega
    have hacc' : ramStep accIdx cfg = xor a (x ⟨p % R, Nat.mod_lt _ hR⟩) := by
      unfold ramStep
      rw [dif_neg (show ¬ ((accIdx (R := R)).val < R) from by
        show ¬ (R < R)
        omega)]
      rw [if_pos (show (accIdx (R := R)).val = R from rfl)]
      rw [hacc]
      congr 1
      -- the one-hot load reads exactly x[p % R]
      unfold loadVal
      cases hx : x ⟨p % R, Nat.mod_lt _ hR⟩ with
      | true =>
        apply List.any_eq_true.mpr
        refine ⟨⟨p % R, Nat.mod_lt _ hR⟩, List.mem_finRange _, ?_⟩
        rw [hA, hmem, hx]
        simp
      | false =>
        apply List.any_eq_false.mpr
        intro i _
        rw [hA, hmem]
        by_cases hip : i.val = p % R
        · have : i = (⟨p % R, Nat.mod_lt _ hR⟩ : Fin R) := Fin.ext hip
          rw [this, hx]
          simp
        · simp [hip]
    have hmem' : ∀ i : Fin R, ramStep (mIdx i) cfg = x i := by
      intro i
      have hival := i.isLt
      unfold ramStep
      rw [dif_neg (show ¬ ((mIdx i).val < R) from by
        show ¬ (R + 1 + i.val < R)
        omega)]
      rw [if_neg (show ¬ ((mIdx i).val = R) from by
        show ¬ (R + 1 + i.val = R)
        omega)]
      exact hmem i
    rw [ih (p + 1) (xor a (x ⟨p % R, Nat.mod_lt _ hR⟩)) (fun j => ramStep j cfg)
      hA' hacc' hmem']
    rfl

/-! ### The arithmetic: the scan is the parity -/

/-- The generic left-to-right XOR fold agrees with the right fold. -/
theorem foldl_xor_eq_foldr {α : Type*} (g : α → Bool) :
    ∀ (l : List α) (b : Bool),
      l.foldl (fun a i => xor a (g i)) b = xor b (l.foldr (fun i a => xor (g i) a) false) := by
  intro l
  induction l with
  | nil =>
    intro b
    show b = xor b false
    rw [Bool.xor_false]
  | cons i l ih =>
    intro b
    show l.foldl (fun a i => xor a (g i)) (xor b (g i)) = _
    rw [ih (xor b (g i))]
    show xor (xor b (g i)) _ = xor b (xor (g i) _)
    rw [Bool.xor_assoc]

/-- `runAcc` as a fold over the step indices. -/
theorem runAcc_foldl (x : Fin R → Bool) (hR : 0 < R) :
    ∀ (T p : ℕ) (a : Bool),
      runAcc x hR a p T
        = (List.range T).foldl (fun b k => xor b (x ⟨(p + k) % R, Nat.mod_lt _ hR⟩)) a := by
  intro T
  induction T with
  | zero => intro p a; rfl
  | succ T ih =>
    intro p a
    show runAcc x hR (xor a (x ⟨p % R, Nat.mod_lt _ hR⟩)) (p + 1) T = _
    rw [ih (p + 1) (xor a (x ⟨p % R, Nat.mod_lt _ hR⟩))]
    rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    have hfun : (fun (b : Bool) (k : ℕ) => xor b (x ⟨(p + 1 + k) % R, Nat.mod_lt _ hR⟩))
        = fun (b : Bool) (k : ℕ) => xor b (x ⟨(p + Nat.succ k) % R, Nat.mod_lt _ hR⟩) := by
      funext b k
      exact congrArg (xor b) (congrArg x (Fin.ext (by
        show (p + 1 + k) % R = (p + Nat.succ k) % R
        congr 1
        omega)))
    rw [hfun]
    rfl

/-- **The scan is the parity (proved)**: `R` steps from pointer `0` accumulate `parityFn R`. -/
theorem runAcc_eq_parity (x : Fin R → Bool) (hR : 0 < R) :
    runAcc x hR false 0 R = parityFn R x := by
  rw [runAcc_foldl]
  have h1 : (List.range R).foldl (fun b k => xor b (x ⟨(0 + k) % R, Nat.mod_lt _ hR⟩)) false
      = (List.finRange R).foldl (fun b i => xor b (x i)) false := by
    rw [show List.range R = (List.finRange R).map Fin.val from
      List.map_coe_finRange_eq_range.symm]
    rw [List.foldl_map]
    have hfun2 : (fun (b : Bool) (i : Fin R) => xor b (x ⟨(0 + i.val) % R, Nat.mod_lt _ hR⟩))
        = fun (b : Bool) (i : Fin R) => xor b (x i) := by
      funext b i
      exact congrArg (xor b) (congrArg x (Fin.ext (by
        show (0 + i.val) % R = i.val
        rw [Nat.zero_add, Nat.mod_eq_of_lt i.isLt])))
    rw [hfun2]
  rw [h1, foldl_xor_eq_foldr, Bool.false_xor]
  rfl

/-! ### The capstone -/

/-- **THE END-TO-END CAPSTONE (proved, UNCONDITIONAL).**  The scan-RAM's proven `R`-step run computes `parityFn R`, and
the whole pipeline — dynamics, embedding, tableau, verified compiler, assembly — yields
`cbudget (parityFn R) ≤ (2R+1) + R·((2R+1)·(4R+3)) + 1` with **no hypotheses**.  Every brick of the simulation arc is
load-bearing in this theorem. -/
theorem ram_parity_cbudget (hR : 0 < R) :
    cbudget (parityFn R) ≤ (R + 1 + R) + R * ((R + 1 + R) * (4 * R + 3)) + 1 := by
  apply ramScan_cbudget R accIdx (scanInp R) (parityFn R)
  intro x
  rw [scan_run x hR R 0 false (fun j => Sum.elim x id (scanInp R j)) ?hA ?hacc ?hmem]
  · exact runAcc_eq_parity x hR
  case hA =>
    intro i
    have := i.isLt
    show Sum.elim x id (scanInp R (aIdx i)) = decide (i.val = 0 % R)
    unfold scanInp
    rw [dif_pos (show (aIdx i).val < R from this)]
    show decide ((aIdx i).val = 0) = decide (i.val = 0 % R)
    rw [Nat.zero_mod]
    rfl
  case hacc =>
    show Sum.elim x id (scanInp R accIdx) = false
    unfold scanInp
    rw [dif_neg (show ¬ ((accIdx (R := R)).val < R) from by show ¬ (R < R); omega)]
    rw [dif_pos (show (accIdx (R := R)).val = R from rfl)]
    rfl
  case hmem =>
    intro i
    have hival := i.isLt
    show Sum.elim x id (scanInp R (mIdx i)) = x i
    unfold scanInp
    rw [dif_neg (show ¬ ((mIdx i).val < R) from by show ¬ (R + 1 + i.val < R); omega)]
    rw [dif_neg (show ¬ ((mIdx i).val = R) from by show ¬ (R + 1 + i.val = R); omega)]
    show x ⟨(mIdx i).val - (R + 1), _⟩ = x i
    apply congrArg
    apply Fin.ext
    show (R + 1 + i.val) - (R + 1) = i.val
    omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.scan_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.runAcc_eq_parity
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.ram_parity_cbudget
