import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameBudgetCashout

/-!
# N-Frame: stacked bands — the trace spectrum, and the honest ceiling

The window argument of the final balance count spent a single band.  This file runs it at every
scale and states exactly what that yields — and what it provably does not.

  `sat3_wire_trace_law` — **PROVED, the scale law**: EVERY wire `w` below the root of a minimal
        SAT circuit, with variable scale `s := |varsOf w|` in the range `[2, m·v/12]`, satisfies
        `s ≤ (3m+3)·(|wireExits w| + 1) + 3v + 9` (or the escape `v ≤ 6(|exits|+3)`) — exit
        count grows linearly with variable scale, wire by wire, not just at one band.
  `sat3_band_wire` — **PROVED**: at every legal band `T` there is a balanced witness wire
        obeying the law, with exits ≤ `coneExcess + 1`.
  `sat3_stacked_bands` — **PROVED, the spectrum**: for any doubling family of bands
        `T₁ < T₂ < …`, there are **pairwise distinct** wires, one per band, each balanced at its
        scale and each obeying the trace law — logarithmically many simultaneous witnesses.
  `sat3_stack_excess` — **PROVED, the ceiling**: what the stack pins on the global excess is the
        MAXIMUM band, not the sum: every legal band `T` forces
        `T ≤ (3m+3)·(coneExcess + 2) + 3v + 9`.

## Honest scope — why the stack does NOT give superlinear excess

The per-band traces do not add.  The obstruction is concrete (the "flat bus"): a single family of
`Θ(m)` wires sitting inside the innermost cone and read from outside every cut can serve as the
trace of EVERY band simultaneously — each band needs only `O(m)` trace bits by our own row
bounds, and nothing in the row-capacity method forces different bands to use *fresh* wires.  So
`coneExcess = Θ(m)` is consistent with every theorem in this file, and the stack's aggregate is
the max, not the sum.  Superlinear excess is **not claimed**.

The named route past this ceiling (not built here — naming is not proving): the **multi-block
additive drag**.  The window's `m·j` empty-mass term arises because each block's data capacity is
compared against the whole trace separately.  If several data blocks can be read independently —
slot-0 selector columns in `S` as data, slot-1 columns outside `S` as per-block reading kits that
neutralize the other data blocks' clauses — the row family multiplies across blocks and the trace
must pay `j ≥ Σ_c d_c`, upgrading the law's `s/(3m)` to `Ω(s)` and the top band to
`coneExcess = Ω(m·v) = Ω(N)`, i.e. a constant-factor gate improvement past `2N`.  The rungs:
multi-block patch, multi-block eval, additive drag, rebuilt window.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **THE SCALE LAW (proved)**: every wire below the root pays exits proportional to its
variable scale — `s ≤ (3m+3)(|exits|+1) + 3v + 9`, or the escape `v ≤ 6(|exits|+3)`. -/
theorem sat3_wire_trace_law (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cc : List (CGate N)) (hcomp : computes cc (sat3Family N))
    (hmin : cc.length = cbudget (sat3Family N))
    (w : ℕ) (hw : w < cc.length - 1)
    (hs2 : 2 ≤ (varsOf cc w).card)
    (hlow : 12 * (varsOf cc w).card ≤ sat3M N * sat3V N) :
    (varsOf cc w).card
      ≤ (3 * sat3M N + 3) * ((wireExits cc w).card + 1) + 3 * sat3V N + 9
    ∨ sat3V N ≤ 6 * ((wireExits cc w).card + 3) := by
  classical
  obtain ⟨hcut, -⟩ := sat3_wire_cut_factorization N hv hm3 hk cc hcomp hmin w hw
  by_contra hcon
  push_neg at hcon
  obtain ⟨hwlaw1, hwlaw2⟩ := hcon
  set j := (wireExits cc w).card with hj
  have hv3 : sat3V N ≤ 3 * sat3M N + 3 := sat3V_le_three_sat3M_add_three N
  have hexp1 : (3 * sat3M N + 3) * (j + 1)
      = 3 * (sat3M N * j) + 3 * sat3M N + 3 * j + 3 := by ring
  have hsub : sat3M N * (sat3V N - j) + sat3M N * j = sat3M N * sat3V N := by
    rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
  have hmul : sat3M N * (6 * j + 19) ≤ sat3M N * sat3V N :=
    Nat.mul_le_mul_left _ (by omega)
  have hexp2 : sat3M N * (6 * j + 19)
      = 6 * (sat3M N * j) + 19 * sat3M N := by ring
  exact sat3_balanced_cut_impossible N hv hk hcut (by omega) (by omega)
    (le_refl (varsOf cc w).card) (by omega) (by omega) (by omega)

/-- **THE BAND WITNESS (proved)**: every legal band has a balanced wire obeying the scale law,
with exits bounded by the global excess. -/
theorem sat3_band_wire (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cc : List (CGate N)) (hcomp : computes cc (sat3Family N))
    (hmin : cc.length = cbudget (sat3Family N))
    (T : ℕ) (hT : 2 ≤ T)
    (hband : 2 * T - 1 ≤ (varsOf cc (cc.length - 1)).card)
    (hlow : 12 * (2 * T - 2) ≤ sat3M N * sat3V N) :
    ∃ w ∈ coneOf cc (cc.length - 1),
      T ≤ (varsOf cc w).card ∧ (varsOf cc w).card ≤ 2 * T - 2
      ∧ (T ≤ (3 * sat3M N + 3) * ((wireExits cc w).card + 1) + 3 * sat3V N + 9
         ∨ sat3V N ≤ 6 * ((wireExits cc w).card + 3))
      ∧ (wireExits cc w).card ≤ coneExcess cc (cc.length - 1) + 1 := by
  obtain ⟨w, hwcone, hwT, hw2T⟩ :=
    balanced_wire_exists cc (cc.length - 1) T hT (by omega)
  have hwne : w ≠ cc.length - 1 := by
    intro heq
    rw [heq] at hw2T
    omega
  have hwlt : w < cc.length - 1 :=
    lt_of_le_of_ne (cone_le cc (cc.length - 1) w hwcone) hwne
  have hlaw := sat3_wire_trace_law N hv hm3 hk cc hcomp hmin w hwlt (by omega)
    (le_trans (Nat.mul_le_mul_left _ hw2T) hlow)
  refine ⟨w, hwcone, hwT, hw2T, ?_,
    wireExits_card_le (sat3Family N) cc hcomp hmin w hwlt⟩
  rcases hlaw with h | h
  · left
    omega
  · right
    exact h

/-- **THE SPECTRUM (proved)**: a doubling family of bands yields pairwise distinct balanced
wires, one per scale, each obeying the trace law. -/
theorem sat3_stacked_bands (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cc : List (CGate N)) (hcomp : computes cc (sat3Family N))
    (hmin : cc.length = cbudget (sat3Family N))
    (k : ℕ) (Ts : Fin k → ℕ)
    (hT2 : ∀ i, 2 ≤ Ts i)
    (hmono : ∀ i j : Fin k, i < j → 2 * Ts i ≤ Ts j)
    (hband : ∀ i, 2 * Ts i - 1 ≤ (varsOf cc (cc.length - 1)).card)
    (hlow : ∀ i, 12 * (2 * Ts i - 2) ≤ sat3M N * sat3V N) :
    ∃ ws : Fin k → ℕ, Function.Injective ws ∧
      ∀ i, ws i ∈ coneOf cc (cc.length - 1)
        ∧ Ts i ≤ (varsOf cc (ws i)).card
        ∧ (varsOf cc (ws i)).card ≤ 2 * Ts i - 2
        ∧ (Ts i ≤ (3 * sat3M N + 3) * ((wireExits cc (ws i)).card + 1)
              + 3 * sat3V N + 9
           ∨ sat3V N ≤ 6 * ((wireExits cc (ws i)).card + 3))
        ∧ (wireExits cc (ws i)).card ≤ coneExcess cc (cc.length - 1) + 1 := by
  choose ws hcone hloB hhiB hlawB hexcB using fun i =>
    sat3_band_wire N hv hm3 hk cc hcomp hmin (Ts i) (hT2 i) (hband i) (hlow i)
  have hlt : ∀ i j : Fin k, i < j → ws i ≠ ws j := by
    intro i j hij heq
    have h1 := hhiB i
    have h2 := hloB j
    have h3 := hmono i j hij
    have h4 := hT2 i
    rw [heq] at h1
    omega
  refine ⟨ws, ?_, fun i => ⟨hcone i, hloB i, hhiB i, hlawB i, hexcB i⟩⟩
  intro a b hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hlt a b h hab
  · exact hlt b a h hab.symm

/-- **THE CEILING (proved)**: what the stack pins on the global excess is the maximum band, not
the sum — every legal band `T` forces `T ≤ (3m+3)(coneExcess + 2) + 3v + 9`. -/
theorem sat3_stack_excess (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cc : List (CGate N)) (hcomp : computes cc (sat3Family N))
    (hmin : cc.length = cbudget (sat3Family N))
    (T : ℕ) (hT : 2 ≤ T)
    (hband : 2 * T - 1 ≤ (varsOf cc (cc.length - 1)).card)
    (hlow : 12 * (2 * T - 2) ≤ sat3M N * sat3V N)
    (htop : 6 * (coneExcess cc (cc.length - 1) + 4) < sat3V N) :
    T ≤ (3 * sat3M N + 3) * (coneExcess cc (cc.length - 1) + 2)
      + 3 * sat3V N + 9 := by
  obtain ⟨w, -, -, -, hlaw, hexc⟩ :=
    sat3_band_wire N hv hm3 hk cc hcomp hmin T hT hband hlow
  set j := (wireExits cc w).card with hj
  set E := coneExcess cc (cc.length - 1) with hE
  have hmul : (3 * sat3M N + 3) * (j + 1) ≤ (3 * sat3M N + 3) * (E + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  rcases hlaw with h | h
  · omega
  · omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_wire_trace_law
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_stacked_bands
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_stack_excess
