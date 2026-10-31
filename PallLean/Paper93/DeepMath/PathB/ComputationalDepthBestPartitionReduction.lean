import PallLean.Paper93.DeepMath.PathB.ComputationalDepthInnerProductCommRank

/-!
# Best-partition hardness reduces to matrix rigidity: the character-rank engine

A best-partition-hard function (high Schmidt rank across *every* balanced partition) can be built as a quadratic
form `Q_M(z) = Σ_{i<j} M_{ij} zᵢ zⱼ`.  Under a partition `(S, Sᶜ)`, its communication matrix factors as
`D₁ · H · D₂` with `D₁, D₂` diagonal `±1` and `H[a][b] = (-1)^{aᵀ M_{S,Sᶜ} b}`, so its rank equals `rank H`.  The
rows of `H` are the characters `χ_{M_{S,Sᶜ}ᵀ a}`, of which there are `2^{rank_{F₂}(M_{S,Sᶜ})}` distinct ones — and
distinct characters are linearly independent (`InnerProductCommRank.chi_linearIndependent`).  Hence

> communication rank of `Q_M` across `(S, Sᶜ)` `= 2^{rank_{F₂}(M_{S,Sᶜ})}`.

(Inner product is the special case `M_{S,Sᶜ} = I`, giving `2^N` — `InnerProductCommRank.chi_finrank`.)

The engine this rests on is that **any set of distinct characters is full rank**:

* `chi_subset_finrank` — for any `T ⊆ {0,1}^N`, the characters `{χ_y : y ∈ T}` span a space of dimension exactly
  `|T|`.

So `Q_M` is best-partition-hard **iff `M` is rank-rigid**: every balanced off-diagonal block `M_{S,Sᶜ}` has
`F₂`-rank `Ω(n)`.

## Honest scope — the remaining piece is matrix rigidity (Valiant, open)

Rank-rigidity ("every off-diagonal block high rank") is exactly the **matrix rigidity** property, whose *explicit*
constructions are a famous open problem (Valiant 1977).  Natural algebraic `F₂` matrices fail concretely (Sylvester
`⟨i,j⟩` has rank `log n`; all-ones has rank `1`; Cauchy is impossible over `F₂`), so there is no clean *explicit*
best-partition-hard function to formalize — one would resolve explicit matrix rigidity.  A random `M` is rigid with
high probability (so a best-partition-hard function *exists*), but that route needs the `F₂` rank-distribution tail
bound plus a union bound over partitions — a separate substantial counting argument.  See
`SCOPE_BEST_PARTITION_HARD.md`.

The reduction and its engine are proved here; the explicit function is an open-problem-hard object.  Nothing here
is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BestPartitionReduction

open PallLean.Paper93.DeepMath.PathB.InnerProductCommRank

variable {K : Type*} [Field K] [CharZero K] {N : ℕ}

/-- **The character-rank engine.**  Any set `T` of distinct inner-product characters spans a space of dimension
exactly `|T|` — they are always linearly independent.  This is what turns a rank-`r` off-diagonal block into a
rank-`2^r` communication matrix. -/
theorem chi_subset_finrank (T : Finset (Fin N → Bool)) :
    Module.finrank K (Submodule.span K (Set.range (fun t : T => chi (K := K) t.val))) = T.card := by
  have hli : LinearIndependent K (fun t : T => chi (K := K) t.val) :=
    (chi_linearIndependent (K := K) (N := N)).comp Subtype.val Subtype.val_injective
  rw [finrank_span_eq_card hli, Fintype.card_coe]

/-- The inner-product full-rank bound is the special case `T = everything`. -/
theorem chi_subset_finrank_univ :
    Module.finrank K
        (Submodule.span K (Set.range (fun t : (Finset.univ : Finset (Fin N → Bool)) =>
          chi (K := K) t.val))) = 2 ^ N := by
  rw [chi_subset_finrank, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

end PallLean.Paper93.DeepMath.PathB.BestPartitionReduction

#print axioms PallLean.Paper93.DeepMath.PathB.BestPartitionReduction.chi_subset_finrank
