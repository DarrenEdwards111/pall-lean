import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW8
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthComposableMachine

/-!
# KRW brick 9: wiring the depth ceiling to `ComposableMachine.InP`

Connects the DeMorgan-formula depth framework to the project's faithful `P`
(`ComposableMachine.InP`, languages `List Bool → Bool` decided in poly time), and
reduces `P ⊄ NC¹` to ONE concrete socket: an explicit family in `P` that is
depth-hard.

* **`langSlice L n`** — the length-`n` slice of a language as a function on
  `Fin n` (`x ↦ L (List.ofFn x)`);
* **`NC1Depth L`** — `L`'s slices have `O(log n)` DeMorgan depth (the `NC¹`
  condition): `∃ c, ∀ n, dmdepth (langSlice L n) ≤ c·(log₂ n + 1)`;
* **`Realizes L F`** — `L` computes the family `F` at power-of-two lengths;
  **`realizes_slice`** — then `langSlice L (2^k) = F k`;
* **`DepthLogBounded F`** — `∃ c, ∀ k, dmdepth (F k) ≤ c·(k+1)`;
  **`hardFamily_not_DepthLogBounded` (proved, unconditional)** — the non-uniform
  hard family violates it;
* **`inP_not_nc1_of_realizes` (proved)** — if `L ∈ InP` realizes a depth-hard
  family, `L ∉ NC1Depth`;
* **`krw_separation_socket` (proved)** — an explicit-in-`P` depth-hard family gives
  `∃ L ∈ InP, L ∉ NC1Depth`, i.e. `P ⊄ NC¹`.

HONEST SCOPE.  `krw_separation_socket`'s hypothesis
`∃ F L, InP L ∧ Realizes L F ∧ ¬ DepthLogBounded F` is precisely the OPEN
requirement: an EXPLICIT (in `P`) depth-hard family.  `hardFamily_not_DepthLogBounded`
supplies the depth-hardness NON-UNIFORMLY (counting), so the residual gap is the
`InP L ∧ Realizes L F` conjunct — UNIFORMITY.  The KRW conjecture (`KRWConjectureDepth`,
KRW2) + the composition machinery (KRW4–6) is the tool for building such an `F`
from a weak explicit gadget; that construction stays open.  This brick FAKES
nothing: it is the machine-checked reduction `explicit-hard-P-family ⟹ P⊄NC¹`, with
the family a named socket.  Nothing here is `P ≠ NP`, and nothing closes KRW.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

open scoped Classical

/-- The length-`n` slice of a language, as a function on `Fin n`. -/
def langSlice (L : List Bool → Bool) (n : ℕ) : (Fin n → Bool) → Bool :=
  fun x => L (List.ofFn x)

/-- The `NC¹`-depth condition: slices have `O(log n)` DeMorgan formula depth. -/
def NC1Depth (L : List Bool → Bool) : Prop :=
  ∃ c, ∀ n, dmdepth (langSlice L n) ≤ c * (Nat.log 2 n + 1)

/-- `L` computes the family `F` at power-of-two input lengths. -/
def Realizes (L : List Bool → Bool) (F : (k : ℕ) → (Fin (2 ^ k) → Bool) → Bool) : Prop :=
  ∀ (k : ℕ) (x : Fin (2 ^ k) → Bool), L (List.ofFn x) = F k x

theorem realizes_slice (L : List Bool → Bool)
    (F : (k : ℕ) → (Fin (2 ^ k) → Bool) → Bool) (hR : Realizes L F) (k : ℕ) :
    langSlice L (2 ^ k) = F k := by
  funext x
  exact hR k x

/-- The family-level `O(log)`-depth condition. -/
def DepthLogBounded (F : (k : ℕ) → (Fin (2 ^ k) → Bool) → Bool) : Prop :=
  ∃ c, ∀ k, dmdepth (F k) ≤ c * (k + 1)

/-- **The non-uniform hard family is depth-hard (proved, unconditional)**. -/
theorem hardFamily_not_DepthLogBounded : ¬ DepthLogBounded hardFamily := by
  rintro ⟨c, hc⟩
  have hk : 4 ≤ c + 5 := by omega
  have hd := hardFamily_depth (c + 5) hk
  have he : (c + 5) - 1 = c + 4 := by omega
  rw [he] at hd
  have hle2 : dmdepth (hardFamily (c + 5)) ≤ c * (c + 6) := hc (c + 5)
  have hsq : (c + 4) ^ 2 ≤ 2 ^ (c + 4) := sq_le_two_pow (c + 4) (by omega)
  have hkey : c * (c + 6) + 1 < 2 ^ (c + 4) := by nlinarith [hsq]
  omega

/-- **The reduction (proved)**: an `InP` language realizing a depth-hard family is
not `NC¹`-depth. -/
theorem inP_not_nc1_of_realizes (F : (k : ℕ) → (Fin (2 ^ k) → Bool) → Bool)
    (L : List Bool → Bool) (hR : Realizes L F) (hHard : ¬ DepthLogBounded F) :
    ¬ NC1Depth L := by
  intro hNC
  apply hHard
  obtain ⟨c, hc⟩ := hNC
  refine ⟨c, fun k => ?_⟩
  have hslice : langSlice L (2 ^ k) = F k := realizes_slice L F hR k
  have hlog : Nat.log 2 (2 ^ k) = k := Nat.log_pow (by norm_num) k
  have hb := hc (2 ^ k)
  rw [hslice, hlog] at hb
  exact hb

/-- **`P ⊄ NC¹` from a named socket (proved)**: an explicit family in `P` that is
depth-hard yields a language in `InP` outside `NC1Depth`.  The hypothesis is the
open uniformity+hardness requirement; nothing here supplies it. -/
theorem krw_separation_socket
    (hSocket : ∃ (F : (k : ℕ) → (Fin (2 ^ k) → Bool) → Bool) (L : List Bool → Bool),
      ComposableMachine.InP L ∧ Realizes L F ∧ ¬ DepthLogBounded F) :
    ∃ L, ComposableMachine.InP L ∧ ¬ NC1Depth L := by
  obtain ⟨F, L, hInP, hR, hHard⟩ := hSocket
  exact ⟨L, hInP, inP_not_nc1_of_realizes F L hR hHard⟩

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.hardFamily_not_DepthLogBounded
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.inP_not_nc1_of_realizes
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.krw_separation_socket
