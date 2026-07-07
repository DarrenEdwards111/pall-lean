import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDragCeiling

/-!
# N-Frame: the search for a non-rank certificate for `coneExcess` — the two failure modes

Three barriers (cut capacity, Mirwald–Schnorr, Uhlig) all reach exactly `rank ≤ N`.  A
super-linear lower bound needs a certificate for `coneExcess` that is NOT rank.  This file is the
honest result of that search: it reframes the question, and proves WHY the one known non-rank
route (formula/Nechiporuk bounds) also fails — collapsing to `log`.

## Reframing — there is no certificate for `coneExcess` in isolation

Every function has a FORMULA (a fan-out-1 circuit), and a formula has `coneExcess = 0`.  So NO
function forces `coneExcess > 0`: there is no lower bound on `coneExcess` per se.  The drag's
`coneExcess ≥ cut-rank` is not a bound on every circuit's `coneExcess`; it binds only SMALL
(shared) circuits.  The real object is the length↔coneExcess TRADEOFF: `length ≥ 2·|ESS| +
coneExcess`, so a certificate must lower-bound `coneExcess` OR give a length bound in the low-fanout
regime.  The low-fanout regime is exactly where formula (non-rank) bounds live.

## The two failure modes a working certificate must dodge

  RANK route (cut capacity): `coneExcess ≥ cut-rank`, and `cut-rank ≤ log₂|Y| ≤ N`
        (`rowFamily_card_le`).  Fails by the INPUT-DIMENSION cap: capped at `N`, linear.

  FORMULA route (Nechiporuk): a formula lower bound `F` (e.g. `N²/log N`) transfers to circuits
        only through the unfolding loss `formulaSize ≤ length · 2^{coneExcess}` (a circuit with
        excess fan-out `E` unfolds to a formula of size `≤ length·2^E`).  So it yields only
        `length ≥ F / 2^{coneExcess}` — which COLLAPSES:

  `formula_cert_collapse` — **PROVED**: at `coneExcess = ⌈log₂ F⌉` the transferred bound
        `F / 2^{coneExcess} ≤ 1` — the formula certificate gives nothing once fan-out reaches
        `log₂ F`.
  `formula_cert_ceiling` — **PROVED**: the best guaranteed `max(coneExcess, F/2^{coneExcess})`
        over the circuit designer's choice of fan-out is `≤ ⌈log₂ F⌉` — so the formula route
        certifies at most `length ≥ log₂ F`, LOGARITHMIC, even from a super-linear formula bound.

## Honest verdict — no working certificate found; the two failure modes, precisely characterized

I did NOT find a non-rank certificate that reaches super-linear — none is known; this is the
general super-linear circuit lower bound problem.  What the search PRODUCED is a precise
characterization of why: the two available non-rank routes fail in ORTHOGONAL ways —

  • the RANK route is capped at the input dimension `N` (a super-linear certificate must measure
    something NOT bounded by `N`);
  • the FORMULA route degrades as `2^{-coneExcess}` and collapses at `log₂ F` (a super-linear
    certificate must NOT lose under fan-out).

A working certificate must dodge BOTH simultaneously — uncapped by input dimension AND stable
under fan-out.  Every known technique has exactly one of these two failure modes, which is a
structural reason the problem is open.  This file freezes the formula-route collapse (the second
failure mode); the first is `rowFamily_card_le` in the drag-ceiling file.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameNonRankCert

/-- **THE FORMULA-CERTIFICATE COLLAPSE (proved)**: a formula lower bound `F`, transferred to
circuits through the unfolding loss `formulaSize ≤ length·2^{coneExcess}`, yields
`length ≥ F / 2^{coneExcess}` — and at `coneExcess = ⌈log₂ F⌉` this is `≤ 1`.  The formula
certificate gives nothing once fan-out reaches `log₂ F`. -/
theorem formula_cert_collapse (F : ℕ) (hF : 1 ≤ F) :
    F ≤ 2 ^ Nat.clog 2 F ∧ F / 2 ^ Nat.clog 2 F ≤ 1 := by
  have hle : F ≤ 2 ^ Nat.clog 2 F := Nat.le_pow_clog one_lt_two F
  refine ⟨hle, ?_⟩
  have hpos : 0 < 2 ^ Nat.clog 2 F := pow_pos (by norm_num) _
  calc F / 2 ^ Nat.clog 2 F
      ≤ 2 ^ Nat.clog 2 F / 2 ^ Nat.clog 2 F := Nat.div_le_div_right hle
    _ = 1 := Nat.div_self hpos

/-- **THE FORMULA-ROUTE CEILING (proved)**: over the circuit designer's choice of fan-out
`coneExcess = e`, the best guaranteed `max(e, F / 2^e)` is at most `⌈log₂ F⌉` — so a formula lower
bound `F`, however super-linear, certifies at most `length ≥ log₂ F` for circuits.  Logarithmic. -/
theorem formula_cert_ceiling (F : ℕ) (hF : 2 ≤ F) :
    ∃ e : ℕ, max e (F / 2 ^ e) ≤ Nat.clog 2 F := by
  refine ⟨Nat.clog 2 F, ?_⟩
  have h := formula_cert_collapse F (by omega)
  have hc1 : 1 ≤ Nat.clog 2 F := by
    rcases Nat.eq_zero_or_pos (Nat.clog 2 F) with h0 | h0
    · rw [h0] at h; simp at h; omega
    · exact h0
  rw [max_le_iff]
  exact ⟨le_refl _, h.2.trans hc1⟩

end PallLean.Paper93.DeepMath.PathB.NFrameNonRankCert

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameNonRankCert.formula_cert_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameNonRankCert.formula_cert_ceiling
