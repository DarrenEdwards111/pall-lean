import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameExpanderDemand

/-!
# N-Frame: cross-scale demand sharing through the mixing layer — the firewall condition

The last surviving route to super-linear is COMPOSITION: `f_{2N}(x) = g(f_N(x₁), f_N(x₂))`, needing
`demand ≥ 2·demand(f_N) + cN`.  The `2·` needs the two `f_N` sub-instances to NOT share demand
through the mixing `g`.  Attacked whether `g` firewalls (forces each sub-instance) or collapses
(lets the single output short-circuit them).

## The firewall condition — `g(·, b)` injective (via restriction)

Fix `x₂ = c`, so `f_{2N}(·, c) = g(f_N(·), f_N(c))`.  If `g(·, b)` is INJECTIVE, this restriction
distinguishes every pair `x, x'` that `f_N` distinguishes — the sub-instance `f_N(x₁)` is forced.
If `g(·, b)` COLLAPSES two distinct sub-outputs, the restriction loses them — no firewall.

  `injective_mixing_preserves_distinct` — **PROVED**: `g(·, b)` injective ⟹ distinct sub-outputs
        stay distinct under mixing.
  `firewall_restriction_distinguishes` — **PROVED**: composed with `f_N` — the restriction
        `g(f_N(·), b)` distinguishes `x, x'` whenever `f_N` does.  So an injective mixing forces the
        sub-instance's distinguishing power (the `1×` demand).
  `noninjective_mixing_collapses` — **PROVED**: if `g` collapses `a ≠ a'` (`g a b = g a' b`), then
        `g(·, b)` is not injective — the firewall fails.

## The correction this forces — the mixing must be MULTI-OUTPUT

  `single_output_mixing_not_injective` — **PROVED**: for `M ≥ 2`, ANY single-output map
        `φ : (Fin M → ZMod 2) → ZMod 2` is non-injective (`2^M > 2`).  So a SINGLE-OUTPUT mixing
        (like the earlier `qform` sketch, `g : {0,1}^{2M} → {0,1}`) CANNOT firewall — it collapses
        `2^M` sub-outputs to one bit.  The mixing must be MULTI-output (`M`-bit) and injective in
        each argument — a bijection family, e.g. `a ↦ a ⊕ b` (`a ⊕ Bb`).  This corrects the
        recursion's `g`: it cannot be the single-output quadratic form; it must be a rank-preserving
        `M`-bit mixing.

## Honest verdict — firewall gives `1×`; the `2×` is the composition (KRW) crux

An injective multi-output mixing FIREWALLS in the restriction sense: each sub-instance's
distinguishing (hence demand) is forced — but that gives `1×` (one restriction re-uses the whole
circuit).  The `2×` — the two forced sub-demands being DISJOINT, not shared across scales — is NOT
delivered by `g`: it is exactly a composition-does-not-collapse statement, in the
Karchmer–Raz–Wigderson (KRW) family (`P` vs `NC¹`), which is OPEN.  So the attack (i) identifies a
necessary design constraint on `g` (multi-output, injective per argument — proved), (ii) shows an
injective `g` forces each sub-instance separately (`1×` — proved), and (iii) locates the remaining
`2×` as the KRW composition crux — open, not delivered by the firewall.  The single-shot routes are
all closed; the composition route now rests on one named open conjecture (KRW), with `g`'s
firewall requirement made precise and proved.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameMixingFirewall

/-- **THE FIREWALL ATOM (proved)**: an injective mixing `g(·, b)` keeps distinct sub-outputs
distinct — `a ≠ a' ⟹ g a b ≠ g a' b`. -/
theorem injective_mixing_preserves_distinct {M : ℕ} {C : Type*}
    (g : (Fin M → ZMod 2) → (Fin M → ZMod 2) → C) (b : Fin M → ZMod 2)
    (hg : Function.Injective (fun a => g a b))
    (a a' : Fin M → ZMod 2) (hne : a ≠ a') :
    g a b ≠ g a' b :=
  fun h => hne (hg h)

/-- **THE FIREWALL (proved)**: composing with `f_N`, an injective mixing makes the restriction
`g(f_N(·), b)` distinguish `x, x'` whenever `f_N` does — the sub-instance's distinguishing power
(its `1×` demand) is forced through the mixing. -/
theorem firewall_restriction_distinguishes {N M : ℕ} {C : Type*}
    (fN : (Fin N → ZMod 2) → (Fin M → ZMod 2))
    (g : (Fin M → ZMod 2) → (Fin M → ZMod 2) → C) (b : Fin M → ZMod 2)
    (hg : Function.Injective (fun a => g a b))
    (x x' : Fin N → ZMod 2) (hne : fN x ≠ fN x') :
    g (fN x) b ≠ g (fN x') b :=
  injective_mixing_preserves_distinct g b hg (fN x) (fN x') hne

/-- **COLLAPSE ⟺ NON-INJECTIVE (proved)**: if the mixing collapses two distinct sub-outputs
(`g a b = g a' b` with `a ≠ a'`), then `g(·, b)` is not injective — the firewall fails. -/
theorem noninjective_mixing_collapses {M : ℕ} {C : Type*}
    (g : (Fin M → ZMod 2) → (Fin M → ZMod 2) → C) (b : Fin M → ZMod 2)
    (a a' : Fin M → ZMod 2) (hne : a ≠ a') (hcollapse : g a b = g a' b) :
    ¬ Function.Injective (fun a => g a b) :=
  fun hinj => hne (hinj hcollapse)

/-- **SINGLE-OUTPUT MIXING CANNOT FIREWALL (proved)**: for `M ≥ 2`, ANY single-output map
`φ : (Fin M → ZMod 2) → ZMod 2` is non-injective — `2^M > 2` sub-outputs collapse to one bit.  So
the mixing `g` must be MULTI-output (`M`-bit) to firewall; a single-output quadratic form cannot. -/
theorem single_output_mixing_not_injective {M : ℕ} (hM : 2 ≤ M)
    (φ : (Fin M → ZMod 2) → ZMod 2) : ¬ Function.Injective φ := by
  intro hinj
  have hle := Fintype.card_le_of_injective φ hinj
  have hz : Fintype.card (ZMod 2) = 2 := by decide
  rw [Fintype.card_fun, hz, Fintype.card_fin] at hle
  have h4 : 4 ≤ 2 ^ M := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) hM
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameMixingFirewall

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameMixingFirewall.firewall_restriction_distinguishes
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameMixingFirewall.noninjective_mixing_collapses
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameMixingFirewall.single_output_mixing_not_injective
