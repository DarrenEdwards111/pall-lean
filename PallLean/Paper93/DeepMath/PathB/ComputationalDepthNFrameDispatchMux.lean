import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameBinaryDecoder

/-!
# N-Frame: the instruction-dispatch multiplexer — the last mechanical residue

A program-controlled RAM differs from the scan-RAM by one gadget: a **dispatch multiplexer** — a one-hot program counter
selects which of `K` instructions' step functions applies this cycle.  This file proves the generic dispatch theorem,
closing the last named mechanical residue of the machine arc.

  `dispatchStep` — the dispatched machine: coordinate `j` steps by `⋁ₖ (pcₖ ∧ Sₖ j)` — under a one-hot `pc`, exactly the
        active instruction's step.
  `dispatchTree` / `dispatchTree_eval` / `dispatchTree_volume` — **PROVED**: the mux tree computes the dispatched step,
        at volume `≤ (s+3)·K + 1` given per-instruction trees of volume `≤ s` — linear in the instruction count.
  `dispatch_cbudget` — **PROVED**: a `K`-instruction dispatched machine on `B` bits run `T` steps decides `f` with
        `cbudget f ≤ B + T·(B·((s+3)·K + 1)) + 1` — polynomial whenever the per-instruction circuits are.

With this, every machine-side gadget of the boundary route is proved: radius-1 steps (TM), pointer-addressed loads
(RAM), binary→one-hot decoding, and instruction dispatch.  A concrete ISA is now pure instantiation: supply the
per-instruction step trees and their sizes, and `dispatch_cbudget` yields the circuit bound; the pc-one-hot invariant is
a dynamics fact discharged per machine exactly as `scan_run` did for the scan-RAM.

## Honest scope

Generic and complete for the dispatch pattern; a specific ISA instantiation is routine instantiation of this theorem.
The open target `NFrameCircuitLowerBoundTarget SAT` is untouched.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {B K : ℕ}

/-- The dispatched step: coordinate `j` steps by `⋁ₖ (pcₖ ∧ Sₖ j)` — under a one-hot program counter, the active
instruction's step. -/
def dispatchStep (pcIdx : Fin K → Fin B) (steps : Fin K → Fin B → (Fin B → Bool) → Bool)
    (j : Fin B) (x : Fin B → Bool) : Bool :=
  (List.finRange K).any (fun k => x (pcIdx k) && steps k j x)

/-- The dispatch multiplexer tree over per-instruction coordinate trees. -/
def dispatchTree (pcIdx : Fin K → Fin B) (t : Fin K → Fin B → Trans B) (j : Fin B) : Trans B :=
  orChain ((List.finRange K).map fun k =>
    Trans.bin (· && ·) (Trans.var (pcIdx k)) (t k j))

/-- **The mux computes the dispatched step (proved).** -/
theorem dispatchTree_eval (pcIdx : Fin K → Fin B)
    (steps : Fin K → Fin B → (Fin B → Bool) → Bool) (t : Fin K → Fin B → Trans B)
    (ht : ∀ k j x, eval (t k j) x = steps k j x) (j : Fin B) (x : Fin B → Bool) :
    eval (dispatchTree pcIdx t j) x = dispatchStep pcIdx steps j x := by
  unfold dispatchTree dispatchStep
  rw [eval_orChain, List.any_map]
  rw [show ((fun tr => eval tr x) ∘ fun k =>
        Trans.bin (· && ·) (Trans.var (pcIdx k)) (t k j))
      = fun k => x (pcIdx k) && steps k j x from funext fun k => by
    show (x (pcIdx k) && eval (t k j) x) = _
    rw [ht k j x]]

/-- **The mux is small (proved)**: volume `≤ (s+3)·K + 1` for per-instruction trees of volume `≤ s`. -/
theorem dispatchTree_volume (pcIdx : Fin K → Fin B) (t : Fin K → Fin B → Trans B) (s : ℕ)
    (ht : ∀ k j, volume (t k j) ≤ s) (j : Fin B) :
    volume (dispatchTree pcIdx t j) ≤ (s + 3) * K + 1 := by
  unfold dispatchTree
  have h := volume_orChain_le ((List.finRange K).map fun k =>
      Trans.bin (· && ·) (Trans.var (pcIdx k)) (t k j)) (s + 2)
    (by
      intro tr htr
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp htr
      show 1 + volume (t k j) + 1 ≤ s + 2
      have := ht k j
      omega)
  rw [List.length_map, List.length_finRange] at h
  omega

/-- **The dispatched-machine circuit bound (proved).**  A `K`-instruction dispatched machine on `B` bits run `T` steps
decides `f` with `cbudget f ≤ B + T·(B·((s+3)·K + 1)) + 1`. -/
theorem dispatch_cbudget {n : ℕ} (pcIdx : Fin K → Fin B)
    (steps : Fin K → Fin B → (Fin B → Bool) → Bool) (t : Fin K → Fin B → Trans B) (s : ℕ)
    (hte : ∀ k j x, eval (t k j) x = steps k j x) (htv : ∀ k j, volume (t k j) ≤ s)
    (T : ℕ) (out : Fin B) (inp : Fin B → Sum (Fin n) Bool) (f : (Fin n → Bool) → Bool)
    (hdec : ∀ x : Fin n → Bool,
      iterStep (dispatchStep pcIdx steps) T (fun j => Sum.elim x id (inp j)) out = f x) :
    cbudget f ≤ B + T * (B * ((s + 3) * K + 1)) + 1 := by
  set cs : Fin B → List (CGate B) := fun j => compile 0 (dispatchTree pcIdx t j) with hcs
  have hcomp : ∀ j, computes (cs j) (dispatchStep pcIdx steps j) := by
    intro j x
    rw [hcs]
    have h1 := compile_computes (dispatchTree pcIdx t j) x
    rw [h1]
    exact dispatchTree_eval pcIdx steps t hte j x
  have hc0 : ∀ j, 0 < (cs j).length := by
    intro j
    rw [hcs, compile_length]
    exact volume_pos _
  have hsz : ∀ j, (cs j).length ≤ (s + 3) * K + 1 := by
    intro j
    rw [hcs, compile_length]
    exact dispatchTree_volume pcIdx t s htv j
  have hs0 : 0 < (s + 3) * K + 1 := by omega
  have hmc := machineCircuit_computes cs (dispatchStep pcIdx steps) ((s + 3) * K + 1) T out
    hsz hc0 hcomp hs0
  have hcomputes : computes
      ((machineCircuit cs ((s + 3) * K + 1) T out).map (retypeInpCB inp)) f := by
    intro x
    show (runFrom x [] ((machineCircuit cs ((s + 3) * K + 1) T out).map (retypeInpCB inp))).getD
        (((machineCircuit cs ((s + 3) * K + 1) T out).map (retypeInpCB inp)).length - 1) false
        = f x
    rw [List.length_map, runFrom_retypeInpCB inp x]
    have hmc2 := hmc (fun j => Sum.elim x id (inp j))
    unfold output at hmc2
    rw [hmc2]
    exact hdec x
  have hmem : cbudget f
      ≤ ((machineCircuit cs ((s + 3) * K + 1) T out).map (retypeInpCB inp)).length :=
    Nat.sInf_le ⟨_, hcomputes, rfl⟩
  have hlen : ((machineCircuit cs ((s + 3) * K + 1) T out).map (retypeInpCB inp)).length
      = B + T * (B * ((s + 3) * K + 1)) + 1 := by
    rw [List.length_map, machineCircuit_length cs ((s + 3) * K + 1) T out hsz]
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.dispatchTree_eval
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.dispatchTree_volume
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.dispatch_cbudget
