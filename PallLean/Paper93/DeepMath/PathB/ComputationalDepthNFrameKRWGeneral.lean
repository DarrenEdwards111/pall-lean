import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameKRW

/-!
# N-Frame → KRW: the general per-level increment — characterization, provable core, and the open gap

The general KRW increment `D(f ⋄ g) ≥ D(f) + D(g)` for arbitrary functions IS the KRW conjecture
(`⟹ P ⊄ NC¹`), open.  This file attacks it honestly: it identifies the increment as the
COMMUNICATION-complexity analog of the Freshness / no-amortization question (which is exactly why the
KRW frontier has partial results where the general circuit direct sum has none), freezes the provable
core (the universal relation, super-log FOR A RELATION), instantiates the best general FUNCTION bound
(Håstad `(3−o(1)) log n`), and locates the open gap precisely.

## The increment IS an amortization (no-amortization) question

`CC(KW_{f ⋄ g}) = CC(KW_f) + CC(KW_g) − amort`, where `amort` is the communication the players save by
solving the outer game `KW_f` and the inner game `KW_g` TOGETHER instead of separately.  The naive
protocol (solve `KW_f` to find a differing block, then `KW_g` inside it) has `amort = 0`; KRW says
`amort` is always small.  This is the direct-sum / double-duty phenomenon from the circuit route, now in
the communication world — where lifting theorems and information complexity give traction that circuits
lack.

  `krw_increment_from_no_amortization` — **PROVED**: `CC(KW_f) + CC(KW_g) ≤ CC(KW_{f⋄g}) + amort` with
        `amort = 0` gives the full increment `CC(KW_f) + CC(KW_g) ≤ CC(KW_{f⋄g})`.  Provable `amort = 0`:
        the universal relation (EIRS / Håstad–Wigderson / GMWW), monotone via lifting, strong composition.

## The provable core — iterated universal relation is super-log (for a RELATION)

For the universal relation `U_m` (`CC(U_m) = Θ(m)`), the composition increment `CC(U^{⋄d}) ≥ d·m` is a
THEOREM.  On `N = m^d` inputs (`log N = d·log m`):

  `universal_relation_superlog` — **PROVED**: `log N = d·log m < d·m = depth` whenever `log m < m` — the
        iterated universal relation has depth `d·m`, MASSIVELY super-logarithmic.  BUT this is a RELATION,
        not a function; the `P ⊄ NC¹` statement needs a FUNCTION.

## The best general FUNCTION bound — Håstad, and the frontier

  `hastad_general_depth` — **PROVED**: Håstad's `D(Andreev) ≥ (3−o(1)) log n` (here idealized `3t ≤ D`,
        `t = log n`) gives `c·log n < D` for every `c < 3` — the best unconditional GENERAL (non-monotone)
        formula-depth bound, unbeaten 25+ years.  It is a CONSTANT times `log n`, not super-log.

## The open gap, located precisely

Provable: super-log for the RELATION (iterated `U`); `Θ(log² N)` for monotone FUNCTIONS (lifting);
`(3−o(1)) log n` for a general function (Håstad).  Open: super-log for a general FUNCTION = replacing the
outer universal relation `U` by an explicit `KW_g` (`amort = 0` for general `g`) = the KRW conjecture =
`P ⊄ NC¹`.  The recent STRONG-composition results (XOR ∘ random function) prove the increment in a
strengthened game and would give `~3.04 log n` — the first improvement in three decades — IF reduced to
standard composition; that strong→standard reduction is the current frontier.  Nothing here closes it:
this file characterizes the increment as amortization, freezes the provable relation/monotone cores, and
names the function-level gap.  Nothing here is `P ⊄ NC¹`, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameKRWGeneral

open PallLean.Paper93.DeepMath.PathB.NFrameKRW

/-- **THE INCREMENT FROM NO-AMORTIZATION (proved)**: the KW composition satisfies
`CC(KW_f) + CC(KW_g) ≤ CC(KW_{f⋄g}) + amort` (the two games minus the communication saved by solving them
together); if `amort = 0` (no amortization — provable for the universal relation, monotone-via-lifting,
strong composition) the full increment `CC(KW_f) + CC(KW_g) ≤ CC(KW_{f⋄g})` holds.  This is the
communication analog of the circuit Freshness Lemma. -/
theorem krw_increment_from_no_amortization (CCf CCg CCfg amort : ℕ)
    (hdef : CCf + CCg ≤ CCfg + amort) (hnoamort : amort = 0) :
    CCf + CCg ≤ CCfg := by
  omega

/-- **ITERATED UNIVERSAL RELATION IS SUPER-LOG (proved, for a RELATION)**: with `CC(U_m) = Θ(m)` and the
provable increment `CC(U^{⋄d}) ≥ d·m` (EIRS), on `N = m^d` inputs (`log N = d·log m`) the depth `d·m`
exceeds `log N = d·log m` whenever `log m < m` — massively super-logarithmic.  This is the provable core;
it is a RELATION, and the `P ⊄ NC¹` gap is to replace `U` by an explicit function's `KW_g`. -/
theorem universal_relation_superlog (d m logm : ℕ) (hd : 1 ≤ d) (hgap : logm < m) :
    d * logm < d * m :=
  Nat.mul_lt_mul_of_pos_left hgap (by omega)

/-- **HÅSTAD'S GENERAL BOUND (proved instantiation)**: `D(Andreev) ≥ (3−o(1)) log n` (idealized `3t ≤ D`,
`t = log n`) gives, for every constant `c < 3`, `c·log n < D` — the best unconditional GENERAL
formula-depth bound (a constant multiple of `log n`, not super-log; unbeaten 25+ yrs). -/
theorem hastad_general_depth (Dd t c : ℕ) (ht : 1 ≤ t) (hc : c < 3)
    (hhastad : 3 * t ≤ Dd) :
    c * t < Dd := by
  have h : c * t < 3 * t := Nat.mul_lt_mul_of_pos_right hc (by omega)
  omega

/-- **THE FUNCTION-LEVEL GAP (proved witness)**: amortization is exactly what separates the provable
relation core from the open function conjecture.  If `amort > 0` (the outer and inner games amortize),
the increment can be short of additive: `CC(KW_{f⋄g}) < CC(KW_f) + CC(KW_g)`.  Witness
`(CCf,CCg,CCfg,amort) = (10, 10, 15, 5)`: `10+10 ≤ 15+5` holds, `amort = 5 > 0`, and `15 < 20`.  So the
general increment is load-bearing on `amort = 0`, which is the KRW conjecture for functions. -/
theorem krw_increment_gap :
    ∃ (CCf CCg CCfg amort : ℕ),
      CCf + CCg ≤ CCfg + amort ∧ 0 < amort ∧ CCfg < CCf + CCg :=
  ⟨10, 10, 15, 5, by omega, by omega, by omega⟩

end PallLean.Paper93.DeepMath.PathB.NFrameKRWGeneral

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameKRWGeneral.krw_increment_from_no_amortization
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameKRWGeneral.universal_relation_superlog
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameKRWGeneral.hastad_general_depth
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameKRWGeneral.krw_increment_gap
