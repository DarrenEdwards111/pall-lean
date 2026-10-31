import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0FullTowerEvalBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0FullTowerBool

/-!
# Acceptance characterization: the polynomial's `1`-residue = the accepting inputs (PROVED)

The cap of the polynomial half — the object Williams' fast-`#SAT` counts.  `eval_frep_bridge` gives
`eval x (frep t) ≡ bval t (mod p^{2^k})`; combined with `bval ∈ {0,1}` (on Boolean-evaluating leaves) and
`p^{2^k} ≥ 2`, the residue pins acceptance exactly:

  `accept_iff` — `(p^{2^k} ∣ eval x (frep t) − 1) ↔ bval p x t = 1`.

So the accepting inputs of the circuit are *exactly* the `x` at which the (degree-`K^depth`,
`(n+1)^{K^depth}`-sparse) polynomial `frep` has residue `1` mod `p^{2^k}`.  This is the precise statement a
`SYM∘AND` `#SAT`-counter operates on: counting accepting inputs = counting `x` with `frep`-residue `1`.

## What is proved (clean axioms, no `sorry`)

* `LeavesBoolAt` — leaves evaluate to `{0,1}` at `x` (true for Boolean inputs + coordinate leaves).
* `bval_mem_bool` — the circuit value is `{0,1}` on Boolean-evaluating leaves (mutual).
* `accept_iff` — acceptance `⟺` `frep`-residue `1` mod `p^{2^k}`.

## Honest scope

The acceptance characterization (the `#SAT` *object*).  The **fast** `#SAT` *algorithm* (counting these
`x` faster than `2^n` via the sparse `SYM∘AND` structure) and the `NEXP ⊄ ACC⁰` contradiction are the
algorithmic half — Williams-strength, **not** built.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0FullTowerSat

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ACC0FullTowerDegree (FTower frep)
open PallLean.Paper93.DeepMath.PathB.ACC0FullTowerEvalBridge (bval eval_frep_bridge)
open PallLean.Paper93.DeepMath.PathB.ACC0FullTowerBool (prod_bool)

variable {n : ℕ}

/-- Leaves of `t` evaluate to `{0,1}` at `x` (e.g. Boolean inputs with coordinate leaves). -/
def LeavesBoolAt (x : Fin n → ℤ) : FTower (Fin n) → Prop
  | .leaf q => eval x q = 0 ∨ eval x q = 1
  | .modN ts => ∀ t ∈ ts, LeavesBoolAt x t
  | .andN ts => ∀ t ∈ ts, LeavesBoolAt x t
  | .orN ts => ∀ t ∈ ts, LeavesBoolAt x t

mutual

/-- **The circuit value is Boolean (proved): `bval p x t ∈ {0,1}` on Boolean-evaluating leaves.** -/
theorem bval_mem_bool (p : ℕ) (x : Fin n → ℤ) :
    (t : FTower (Fin n)) → LeavesBoolAt x t → bval p x t = 0 ∨ bval p x t = 1
  | .leaf q, h => by rw [bval]; simp only [LeavesBoolAt] at h; exact h
  | .modN ts, _ => by rw [bval]; split <;> simp
  | .andN ts, h => by
      simp only [LeavesBoolAt] at h
      rw [bval]
      exact prod_bool _ (fun y hy => by
        simp only [List.mem_map] at hy; obtain ⟨t, ht, rfl⟩ := hy
        exact bval_mem_bool_list p x ts h t ht)
  | .orN ts, h => by
      simp only [LeavesBoolAt] at h
      rw [bval]
      have hp : (ts.map (fun t => 1 - bval p x t)).prod = 0 ∨ (ts.map (fun t => 1 - bval p x t)).prod = 1 :=
        prod_bool _ (fun y hy => by
          simp only [List.mem_map] at hy; obtain ⟨t, ht, rfl⟩ := hy
          rcases bval_mem_bool_list p x ts h t ht with hb | hb <;> simp [hb])
      rcases hp with hb | hb <;> simp [hb]

/-- List companion. -/
theorem bval_mem_bool_list (p : ℕ) (x : Fin n → ℤ) :
    (ts : List (FTower (Fin n))) → (∀ t ∈ ts, LeavesBoolAt x t) →
      ∀ t ∈ ts, bval p x t = 0 ∨ bval p x t = 1
  | [], _ => fun t ht => absurd ht (by simp)
  | a :: ts, h => fun t ht => by
      rcases List.mem_cons.mp ht with rfl | hmem
      · exact bval_mem_bool p x t (h t ht)
      · exact bval_mem_bool_list p x ts (fun t' ht' => h t' (List.mem_cons_of_mem _ ht')) t hmem

end

/-- **Acceptance characterization (proved): `frep`-residue `1` `⟺` the circuit accepts.**  The accepting
inputs are exactly the `x` where the sparse low-degree polynomial `frep` has residue `1` mod `p^{2^k}`. -/
theorem accept_iff (p k : ℕ) [Fact p.Prime] (x : Fin n → ℤ) (t : FTower (Fin n))
    (hbool : LeavesBoolAt x t) :
    ((p : ℤ) ^ (2 ^ k) ∣ (eval x (frep p k t) - 1)) ↔ bval p x t = 1 := by
  have hbridge := eval_frep_bridge p k x t
  have hp2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast (Fact.out : p.Prime).two_le
  have h2 : (2 : ℤ) ≤ (p : ℤ) ^ (2 ^ k) := by
    calc (2 : ℤ) = (2 : ℤ) ^ 1 := (pow_one 2).symm
      _ ≤ (p : ℤ) ^ 1 := by gcongr
      _ ≤ (p : ℤ) ^ (2 ^ k) := by
          apply pow_le_pow_right₀ (by linarith) (Nat.one_le_pow k 2 (by norm_num))
  constructor
  · intro h1
    -- p^(2^k) ∣ (bval - 1) from the two divisibilities; bval ∈ {0,1}; ≥ 2 forces bval = 1
    have hbv : (p : ℤ) ^ (2 ^ k) ∣ (bval p x t - 1) := by
      have := dvd_sub h1 hbridge
      rwa [show eval x (frep p k t) - 1 - (eval x (frep p k t) - bval p x t)
        = bval p x t - 1 from by ring] at this
    rcases bval_mem_bool p x t hbool with hb | hb
    · exfalso
      rw [hb, show (0 : ℤ) - 1 = -1 from by ring] at hbv
      have hd1 : (p : ℤ) ^ (2 ^ k) ∣ (1 : ℤ) := (dvd_neg).mp hbv
      have := Int.le_of_dvd (by norm_num) hd1
      linarith
    · exact hb
  · intro h1
    rw [show eval x (frep p k t) - 1 = (eval x (frep p k t) - bval p x t) + (bval p x t - 1) from by ring]
    refine dvd_add hbridge ?_
    rw [h1]; simp

end PallLean.Paper93.DeepMath.PathB.ACC0FullTowerSat
