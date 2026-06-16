import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PrimePowerGate

/-!
# Candidate #3 — the layered residue tower observer `x ↦ (x mod p, x mod p², …, x mod p^e)`

The observer-candidate analysis (`…ACC0PrimePowerObserverCandidates`) refuted the characteristic-`p` field family and
confirmed two information-sufficient observers (the ring `ZMod (p^e)`, the `p`-adic valuation).  This file analyses the
third candidate the tri-aspect boundary could select: the **layered residue tower** — the filtration

```
   ZMod p  ←  ZMod p²  ←  …  ←  ZMod p^e ,        x ↦ (x mod p, x mod p², …, x mod p^e).
```

Three honest facts are proved, and together they pin down exactly what the tower buys:

* **Graded ladder.**  Rung `i` decides `MOD_{p^i}`: `(x : ZMod (p^i)) = 0 ↔ p^i ∣ x`.  The whole tower is the ladder
  `{MOD_{p^i}}_{i=1}^{e}` — each level a sharper divisibility test.

* **Filtration (top determines all).**  Rung `i` is the *ring projection* of rung `e`: the canonical
  `ZMod (p^e) →+* ZMod (p^i)` (`ZMod.castHom`, exists since `p^i ∣ p^e`) sends the level-`e` residue to the level-`i`
  residue.  So the tower carries no information beyond its top rung `ZMod (p^e)` — it is a *presentation* of candidate
  #1, not a richer observer.

* **Depth exactly `e` is required.**  The tower *truncated below* level `e` cannot compute `MOD_{p^e}`: `0` and
  `p^{e-1}` agree on every rung `1 ≤ i ≤ e-1` (both `≡ 0 mod p^i`) yet `MOD_{p^e}` accepts `0` and rejects `p^{e-1}`.
  So the full depth `e` is necessary — the field observer is the case `e = 1` of the truncation, which is exactly why
  it fails.

## What is proved (clean axioms, no `sorry`)

* **`tower_level_decides`** — rung `i` decides `MOD_{p^i}` (`(s : ZMod (p^i)) = 0 ↔ p^i ∣ s`).
* **`tower_projection_compatible`** — rung `i` is the projection of rung `e` (`castHom` commutes with the residue).
* **`tower_truncation_insufficient`** — truncating below level `e` loses `MOD_{p^e}` (witness `0`, `p^{e-1}`).

## Honest scope

The tower is information-*equivalent* to the ring `ZMod (p^e)` (proved: top determines all), so it does **not** escape
the low-degree wall — its top rung is still a ring with zero divisors, where the Fermat indicator dies.  What the tower
adds is *structure*: it exposes the graded ladder `{MOD_{p^i}}` and proves the depth-`e` requirement (truncation
insufficient), localising precisely where the field observer (`e = 1`) loses the information.  No quasipolynomial
low-degree sparse representation is claimed — that remains the open `ACC⁰[composite]` crux.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerTowerObserver

/-- **Graded ladder (proved): rung `i` of the tower decides `MOD_{p^i}`.**  `(s : ZMod (p^i)) = 0 ↔ p^i ∣ s` — the
layered residue tower is exactly the ladder `{MOD_{p^i}}_{i=1}^{e}` of sharper and sharper divisibility tests. -/
theorem tower_level_decides (p i s : ℕ) :
    ((s : ZMod (p ^ i)) = 0) ↔ p ^ i ∣ s :=
  ACC0PrimePowerGate.modPrimePower_observer_decides p i s

/-- **Filtration (proved): rung `i` is the ring projection of rung `e`.**  The canonical projection
`ZMod (p^e) →+* ZMod (p^i)` (`ZMod.castHom`, valid because `p^i ∣ p^e`) sends the level-`e` residue of `s` to its
level-`i` residue.  Hence the top rung `ZMod (p^e)` determines the whole tower — the tower carries no information
beyond candidate #1. -/
theorem tower_projection_compatible (p i e s : ℕ) (h : p ^ i ∣ p ^ e) :
    (ZMod.castHom h (ZMod (p ^ i))) ((s : ℕ) : ZMod (p ^ e)) = ((s : ℕ) : ZMod (p ^ i)) :=
  map_natCast (ZMod.castHom h (ZMod (p ^ i))) s

/-- **Depth exactly `e` is required (proved): the tower truncated below level `e` cannot compute `MOD_{p^e}`.**  The
inputs `0` and `p^{e-1}` agree on every rung `1 ≤ i ≤ e-1` (both `≡ 0 mod p^i`), yet `MOD_{p^e}` accepts `0`
(`p^e ∣ 0`) and rejects `p^{e-1}` (`¬ p^e ∣ p^{e-1}`, since `e-1 < e`).  So no function of the truncated tower
(levels `1 … e-1`) computes `MOD_{p^e}`; the full depth `e` is necessary.  The field observer is the case `e = 1` of
this truncation — which is exactly why it fails for `e ≥ 2`. -/
theorem tower_truncation_insufficient (p e : ℕ) (hp : p.Prime) (he : 2 ≤ e) :
    (∀ i, 1 ≤ i → i ≤ e - 1 →
        ((p ^ (e - 1) : ℕ) : ZMod (p ^ i)) = ((0 : ℕ) : ZMod (p ^ i)))
      ∧ p ^ e ∣ 0 ∧ ¬ p ^ e ∣ p ^ (e - 1) := by
  refine ⟨?_, dvd_zero _, ?_⟩
  · intro i _ hie
    rw [Nat.cast_zero]
    exact (tower_level_decides p i (p ^ (e - 1))).mpr (pow_dvd_pow p hie)
  · intro h
    have hle := Nat.le_of_dvd (pow_pos hp.pos (e - 1)) h
    have hlt : p ^ (e - 1) < p ^ e := Nat.pow_lt_pow_right hp.one_lt (by omega)
    omega

end PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerTowerObserver

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerTowerObserver.tower_level_decides
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerTowerObserver.tower_projection_compatible
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerTowerObserver.tower_truncation_insufficient
