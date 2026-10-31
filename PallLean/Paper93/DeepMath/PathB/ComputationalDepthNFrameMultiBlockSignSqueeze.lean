import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMultiBlockPrivateBudget

/-!
# N-Frame: the sign squeeze — the last refuge closes

Rung 17 of the multi-block arc (… → private budget → **sign squeeze**).  Rung 16 left exactly
one unpriced coordinate class: the sign columns (`Ω(m)` sign bits of one slot inside `S` kill
the pin machinery at `o(N)` cost).  Pressure-testing the planned "sign-data drag" showed it
already exists in the single-block corpus: `sat3_slot_dichotomy` (the min-form census) says a
slot's sign column is `(j+2)`-concentrated OR every block's slot-`t` selector column is nearly
full — and `sat3_full_mass` prices the nearly-full case at `|S| ≥ m(v − j)`, which a balanced
band forbids.  Composing:

  `sat3_sign_squeeze` — **PROVED, per slot**: for every cut factorization,
        `Q_t ≤ j + 2`, or `m·(v − j) ≤ |S|` (the full-mass horn), or `j` is already
        pool/position-scale (`m < 2j + 6` or `v < 2j + 1`).
  `sat3_private_cut_squeeze` — **PROVED, the assembled cut bound**: for every cut,
        `|S| ≤ 12·j + 3v + 9`, or `m·(v − j) ≤ |S|`, or an explicit `j = Ω(m)`/`Ω(v)` horn —
        NO sign terms remain: the `Q`-horns of the rung-16 budgets are capped at `j + 2` by the
        squeeze, and the ledger closes the accounting.
  `sat3_private_band_squeeze` — **PROVED, the closed flight**: at every band of a minimal SAT
        circuit,
        `T ≤ 12·(coneExcess + 1) + 3v + 9`, or `m·(v − (coneExcess + 1)) ≤ 2T − 2`, or
        `coneExcess + 1` is `Ω(m)`/`Ω(v)` outright.

Every horn now lower-bounds `coneExcess` in band parameters alone — no poison counts, no
cleanliness, no `hvars`-style side conditions beyond the band's existence.  At `T ≈ m·v/4` the
horns force `coneExcess = Ω(m) = Ω(√N)` with constant `~1/12` (the classical single-block route
gave `~1/32` conditionally); the full-mass horn degrades the bound at bands beyond `≈ m·v/2`,
which is the known structural cap of pin-based reading (pins and probes must survive inside
`Sᶜ`).

## Honest scope

The squeeze closes the sign refuge WITHIN the pin framework's `Ω(√N)` ceiling; it does not
lift the ceiling.  The `(2+c)·N` question now rests entirely on pricing beyond pool scale —
rows richer than `2^Θ(m)` — for which the rectangle/column extraction of rungs 8/11 (now
cleanliness-free via the private kit) is the remaining instrument, and the heavy-band regime
(`T ≥ m·v/2`, where `S` swallows the probes) is the true open frontier.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The sign squeeze -/

set_option maxHeartbeats 800000 in
/-- **THE SIGN SQUEEZE (proved)**: every slot's sign column is `(j+2)`-small, or the slot's
selector grid is nearly full (`m·(v−j) ≤ |S|`), or `j` is already pool/position-scale. -/
theorem sat3_sign_squeeze (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j) (t : Fin 3) :
    ((Finset.univ : Finset (Fin (sat3M N))).filter (fun c =>
      sat3Bit N c t (sat3V N) (by omega) ∈ S)).card ≤ j + 2
    ∨ sat3M N * (sat3V N - j) ≤ S.card
    ∨ sat3M N < 2 * j + 6
    ∨ sat3V N < 2 * j + 1 := by
  classical
  by_cases hm : 2 * j + 6 ≤ sat3M N
  · by_cases hvj : 2 * j + 1 ≤ sat3V N
    · have hk : (sat3M N - 2) + 1 ≤ sat3M N := by omega
      rcases sat3_slot_dichotomy N hv hk hcut t hm hvj with hout | ⟨-, hQ⟩
      · exact Or.inr (Or.inl (sat3_full_mass N t hout))
      · exact Or.inl hQ
    · exact Or.inr (Or.inr (Or.inr (by omega)))
  · exact Or.inr (Or.inr (Or.inl (by omega)))

/-! ### The assembled cut bound -/

set_option maxHeartbeats 1600000 in
/-- **THE ASSEMBLED CUT BOUND (proved)**: for every cut factorization,
`|S| ≤ 12·j + 3v + 9`, or the full-mass horn, or an explicit `j`-scale horn — no sign terms
remain anywhere. -/
theorem sat3_private_cut_squeeze (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j) :
    S.card ≤ 12 * j + 3 * sat3V N + 9
    ∨ sat3M N * (sat3V N - j) ≤ S.card
    ∨ sat3M N < 6 * j + 17
    ∨ sat3M N < 2 * j + 6
    ∨ sat3V N < 2 * j + 1 := by
  classical
  rcases sat3_sign_squeeze N hv hcut ⟨0, by omega⟩ with hQ0 | h | h | h
  · rcases sat3_sign_squeeze N hv hcut ⟨1, by omega⟩ with hQ1 | h | h | h
    · rcases sat3_sign_squeeze N hv hcut ⟨2, by omega⟩ with hQ2 | h | h | h
      · -- all sign columns small: run the budgets, pool horns capped at 6j+17
        rcases sat3_private_budget N hv hcut with h0 | h0
        · rcases sat3_private_budget_slot1 N hv hcut with h1 | h1
          · rcases sat3_private_budget_slot2 N hv hcut with h2 | h2
            · left
              have hled := sat3_grid_mass_ledger N S
              omega
            · exact Or.inr (Or.inr (Or.inl (by omega)))
          · exact Or.inr (Or.inr (Or.inl (by omega)))
        · exact Or.inr (Or.inr (Or.inl (by omega)))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-! ### The closed flight -/

set_option maxHeartbeats 1600000 in
/-- **THE CLOSED FLIGHT (proved)**: at every band of a minimal SAT circuit, every horn
lower-bounds `coneExcess` in band parameters alone — the sign refuge is closed. -/
theorem sat3_private_band_squeeze (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cc : List (CGate N)) (hcomp : computes cc (sat3Family N))
    (hmin : cc.length = cbudget (sat3Family N))
    (T : ℕ) (hT : 2 ≤ T)
    (hband : 2 * T - 1 ≤ (varsOf cc (cc.length - 1)).card) :
    T ≤ 12 * (coneExcess cc (cc.length - 1) + 1) + 3 * sat3V N + 9
    ∨ sat3M N * (sat3V N - (coneExcess cc (cc.length - 1) + 1)) ≤ 2 * T - 2
    ∨ sat3M N < 6 * (coneExcess cc (cc.length - 1) + 1) + 17
    ∨ sat3M N < 2 * (coneExcess cc (cc.length - 1) + 1) + 6
    ∨ sat3V N < 2 * (coneExcess cc (cc.length - 1) + 1) + 1 := by
  classical
  obtain ⟨S, hT1, hT2, j, hj, hcut⟩ :=
    sat3_balanced_cut N hv hm3 hk cc hcomp hmin T hT hband
  rcases sat3_private_cut_squeeze N hv hcut with h | h | h | h | h
  · left
    omega
  · right
    left
    have hmono : sat3M N * (sat3V N - (coneExcess cc (cc.length - 1) + 1))
        ≤ sat3M N * (sat3V N - j) :=
      Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hj _)
    omega
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by omega))))

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_sign_squeeze
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_private_cut_squeeze
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_private_band_squeeze
