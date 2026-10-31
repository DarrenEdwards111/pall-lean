import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung4CircuitReal

/-!
# Layer 4 (Route A, piece 3 — the padding construction)

The circuit-side construction that produces, from a `MOD_q ∈ AC⁰[p]` circuit, the residue-indicator
circuits `C_j` computing `[#ones ≡ j]` — discharging `exists_indicator_approximant`'s hypothesis `hCind`
(`ComputationalDepthLayer4Approx`).  The idea: `[#ones(x) ≡ j (mod q)] = MOD_q(x ‖ (q-j)·⟨true⟩)`, i.e.
`MOD_q` on the input padded with `q-j` constant-`true` bits.

This file provides the **input-substitution** operation that implements padding, sorry-free:

* `padInputs f` — substitute each input `i` of a circuit by the circuit `f i` (a structural recursion
  through the `List`-children gates);
* `padInputs_eval` — its semantics: `(padInputs f C).eval x = C.eval (fun i => (f i).eval x)`;
* `padTrue` — the padding specialisation: hardwire the last `k` inputs to `const true`
  (`f i = input i` for `i < n`, `const true` otherwise);
* `padTrue_eval` — `(padTrue D).eval x = D.eval (extend x by trues)`;
* `padInputs_isAC0pSyntax` / `padTrue_isAC0pSyntax` — padding preserves `AC⁰[p]` (it only swaps
  input↔const leaves; gates, in particular the `MOD_p` gates, are unchanged) — discharging `hmod`;
* `padInputs_depth` / `padTrue_depth` — padding preserves depth (depth-`0` leaf substitution), so the
  Smolensky bound `((p-1)t)^{depth}` is unchanged;
* `ones_extend` (`#ones(extend x by k trues) = #ones(x) + k`) + `mod_shift`
  (`(a+(q-j))%q = 0 ↔ a%q = j`) ⇒ `padTrue_computes_indicator`: `padTrue` of a `MOD_q` circuit computes
  `[#ones ≡ j]` — **discharging `hCind`**.

**Remaining (honestly flagged, not faked):** only the **intersection bookkeeping** — to run the `q`
indicator circuits together on one set `G = ⋂_{j<q} G_j` one needs each `|G_jᶜ| ≤ 2ⁿ/(4q)`, i.e. the
tighter horizon `p^t ≥ 4q·s` (a parameterised `exists_large_agreement_set`).  Pure `Nat` counting.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer4

open PallLean.Paper93.DeepMath.PathB
open BoolCircuitSyntax

/-- **Input substitution.**  Replace each input `i` of a circuit by the circuit `f i`. -/
def padInputs {m n : ℕ} (f : Fin m → BoolCircuitSyntax n) : BoolCircuitSyntax m → BoolCircuitSyntax n
  | .const b => .const b
  | .input i => f i
  | .not C => .not (padInputs f C)
  | .andGate Cs => .andGate (Cs.map (padInputs f))
  | .orGate Cs => .orGate (Cs.map (padInputs f))
  | .modGate p r Cs => .modGate p r (Cs.map (padInputs f))

/-- **Substitution semantics:** `(padInputs f C).eval x = C.eval (fun i => (f i).eval x)`. -/
theorem padInputs_eval {m n : ℕ} (f : Fin m → BoolCircuitSyntax n) (x : Fin n → Bool) :
    ∀ (C : BoolCircuitSyntax m), (padInputs f C).eval x = C.eval (fun i => (f i).eval x)
  | .const b => by simp [padInputs, eval]
  | .input i => by simp [padInputs, eval]
  | .not C => by simp only [padInputs, eval, padInputs_eval f x C]
  | .andGate Cs => by
      simp only [padInputs, eval, List.map_map, Function.comp_def]
      rw [List.map_congr_left (fun C hC => padInputs_eval f x C)]
  | .orGate Cs => by
      simp only [padInputs, eval, List.map_map, Function.comp_def]
      rw [List.map_congr_left (fun C hC => padInputs_eval f x C)]
  | .modGate p r Cs => by
      simp only [padInputs, eval, List.map_map, Function.comp_def]
      rw [List.map_congr_left (fun C hC => padInputs_eval f x C)]

/-- **Padding:** hardwire the last `k` of `n+k` inputs to `const true` (keep the first `n`). -/
def padTrue {n k : ℕ} (D : BoolCircuitSyntax (n + k)) : BoolCircuitSyntax n :=
  padInputs (fun i : Fin (n + k) => if h : (i : ℕ) < n then .input ⟨i, h⟩ else .const true) D

/-- **Padding semantics:** `(padTrue D).eval x = D.eval (x extended by `true`s on the last `k` bits)`. -/
theorem padTrue_eval {n k : ℕ} (D : BoolCircuitSyntax (n + k)) (x : Fin n → Bool) :
    (padTrue D).eval x = D.eval (fun i => if h : (i : ℕ) < n then x ⟨i, h⟩ else true) := by
  rw [padTrue, padInputs_eval]
  congr 1
  funext i
  by_cases h : (i : ℕ) < n <;> simp [h, eval]

/-- **Padding preserves `AC⁰[p]`** (substituting inputs by `AC⁰[p]` leaves keeps the gate structure). -/
theorem padInputs_isAC0pSyntax {m n : ℕ} (p : ℕ) (f : Fin m → BoolCircuitSyntax n)
    (hf : ∀ i, IsAC0pSyntax p (f i)) :
    ∀ (C : BoolCircuitSyntax m), IsAC0pSyntax p C → IsAC0pSyntax p (padInputs f C)
  | .const b, _ => by simp only [padInputs, IsAC0pSyntax]
  | .input i, _ => by simp only [padInputs]; exact hf i
  | .not C, h => by
      simp only [padInputs, IsAC0pSyntax] at h ⊢; exact padInputs_isAC0pSyntax p f hf C h
  | .andGate Cs, h => by
      simp only [padInputs, IsAC0pSyntax, List.mem_map] at h ⊢
      rintro _ ⟨C, hC, rfl⟩; exact padInputs_isAC0pSyntax p f hf C (h C hC)
  | .orGate Cs, h => by
      simp only [padInputs, IsAC0pSyntax, List.mem_map] at h ⊢
      rintro _ ⟨C, hC, rfl⟩; exact padInputs_isAC0pSyntax p f hf C (h C hC)
  | .modGate p' r Cs, h => by
      simp only [padInputs, IsAC0pSyntax, List.mem_map] at h ⊢
      refine ⟨h.1, ?_⟩
      rintro _ ⟨C, hC, rfl⟩; exact padInputs_isAC0pSyntax p f hf C (h.2 C hC)

/-- `padTrue` preserves `AC⁰[p]` (the pad leaves `input`/`const true` are `AC⁰[p]`). -/
theorem padTrue_isAC0pSyntax {n k : ℕ} (p : ℕ) (D : BoolCircuitSyntax (n + k))
    (h : IsAC0pSyntax p D) : IsAC0pSyntax p (padTrue D) :=
  padInputs_isAC0pSyntax p _ (fun i => by by_cases hi : (i : ℕ) < n <;> simp [hi, IsAC0pSyntax]) D h

/-- `foldl`-max congruence: if `g` and `h` agree on the members, the depth folds coincide. -/
theorem foldl_max_congr {n : ℕ} (g h : BoolCircuitSyntax n → ℕ) :
    ∀ (Cs : List (BoolCircuitSyntax n)) (a : ℕ), (∀ C ∈ Cs, g C = h C) →
      Cs.foldl (fun acc C => max acc (g C)) a = Cs.foldl (fun acc C => max acc (h C)) a
  | [], _, _ => rfl
  | C :: Cs, a, hgh => by
      simp only [List.foldl_cons, hgh C (List.mem_cons_self ..)]
      exact foldl_max_congr g h Cs _ (fun C' hC' => hgh C' (List.mem_cons_of_mem _ hC'))

/-- **Padding preserves depth.**  Substituting inputs by depth-`0` leaves leaves the gate structure
intact (`(padInputs f C).depth = C.depth` when every `f i` has depth `0`). -/
theorem padInputs_depth {m n : ℕ} (f : Fin m → BoolCircuitSyntax n) (hf : ∀ i, (f i).depth = 0) :
    ∀ (C : BoolCircuitSyntax m), (padInputs f C).depth = C.depth
  | .const b => by simp [padInputs, depth]
  | .input i => by simp only [padInputs]; rw [hf i, depth]
  | .not C => by simp only [padInputs, depth, padInputs_depth f hf C]
  | .andGate Cs => by
      simp only [padInputs, depth, List.foldl_map]
      congr 1; exact foldl_max_congr _ _ Cs 0 (fun C hC => padInputs_depth f hf C)
  | .orGate Cs => by
      simp only [padInputs, depth, List.foldl_map]
      congr 1; exact foldl_max_congr _ _ Cs 0 (fun C hC => padInputs_depth f hf C)
  | .modGate p r Cs => by
      simp only [padInputs, depth, List.foldl_map]
      congr 1; exact foldl_max_congr _ _ Cs 0 (fun C hC => padInputs_depth f hf C)

/-- `padTrue` preserves depth: `(padTrue D).depth = D.depth` (the pad leaves have depth `0`).  So the
Smolensky degree bound `((p-1)t)^{depth}` is unchanged by padding. -/
theorem padTrue_depth {n k : ℕ} (D : BoolCircuitSyntax (n + k)) : (padTrue D).depth = D.depth :=
  padInputs_depth _ (fun i => by by_cases hi : (i : ℕ) < n <;> simp [hi]) D

/-- **`#ones` under padding.**  Extending `x` by `k` `true`s adds exactly `k` ones:
`#ones(extend x by k trues) = #ones(x) + k`.  (Split `Fin (n+k)` into the `castAdd`/`natAdd` halves.) -/
theorem ones_extend (n k : ℕ) (x : Fin n → Bool) :
    (Finset.univ.filter (fun i : Fin (n + k) =>
        (if h : (i : ℕ) < n then x ⟨i, h⟩ else true) = true)).card
      = (Finset.univ.filter (fun i : Fin n => x i = true)).card + k := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    have hlt : ((Fin.castAdd k i : Fin (n + k)) : ℕ) < n := by rw [Fin.coe_castAdd]; exact i.isLt
    have hcast : (⟨(Fin.castAdd k i : Fin (n + k)), hlt⟩ : Fin n) = i := Fin.ext (Fin.coe_castAdd k i)
    rw [dif_pos hlt, hcast]
  · refine (Finset.sum_congr rfl (fun i _ => ?_)).trans
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one])
    have hge : ¬ ((Fin.natAdd n i : Fin (n + k)) : ℕ) < n := by rw [Fin.val_natAdd]; omega
    rw [dif_neg hge, if_pos rfl]

/-- **The mod-`q` shift identity:** `(a + (q-j)) % q = 0 ↔ a % q = j` for `j < q` (so adding `q-j` to a
weight `≡ j` makes it `≡ 0`).  Via `ZMod q`. -/
theorem mod_shift {q : ℕ} (hq : 0 < q) (a j : ℕ) (hj : j < q) :
    (a + (q - j)) % q = 0 ↔ a % q = j := by
  haveI : NeZero q := ⟨hq.ne'⟩
  rw [← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff]
  push_cast [Nat.cast_sub hj.le]
  rw [ZMod.natCast_self, zero_sub, add_neg_eq_zero, ZMod.natCast_eq_natCast_iff, Nat.ModEq,
    Nat.mod_eq_of_lt hj]

/-- **`padTrue` of a `MOD_q` circuit computes the residue indicator.**  If `D` (on `n + (q-j)` bits)
computes `MOD_q` (residue `0`), then `padTrue D` (on `n` bits) computes `[#ones ≡ j (mod q)]`.  This is
exactly the hypothesis `hCind` of `exists_indicator_approximant` (`ComputationalDepthLayer4Approx`),
discharged: `(padTrue D).eval x = D.eval (extend) = [#ones+( q-j) ≡ 0] = [#ones ≡ j]`. -/
theorem padTrue_computes_indicator {n q j : ℕ} (hq : 0 < q) (hj : j < q)
    (D : BoolCircuitSyntax (n + (q - j)))
    (hD : ∀ y : Fin (n + (q - j)) → Bool,
      D.eval y = decide ((Finset.univ.filter (fun i => y i = true)).card % q = 0))
    (x : Fin n → Bool) :
    (padTrue D).eval x = decide ((Finset.univ.filter (fun i => x i = true)).card % q = j) := by
  rw [padTrue_eval, hD, ones_extend]
  exact decide_eq_decide.mpr (mod_shift hq _ j hj)

end PallLean.Paper93.DeepMath.PathB.Layer4

#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.padInputs_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.padTrue_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.padTrue_depth
#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.padTrue_isAC0pSyntax
#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.padTrue_computes_indicator
