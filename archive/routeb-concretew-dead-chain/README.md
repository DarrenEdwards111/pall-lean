# Route B concreteW dead-chain archive

Archived 2026-05-15.

For the Lemma 31 / Property 1 row-containment proof, the fixed-canonical
`concreteW n hn4 (Fin.castLEEmb hn4)` target is diagnostic only.  It is not the
paper-faithful final target because variable-dependent Cook--Levin rows (already
visible for booleanity at nonzero variables) cannot be transported into the fixed
canonical chart unconditionally.

The active target is instead the coordinate/profile-local family

```lean
profileSubspace h (fun σ => interfaceSpace_compiledBasis B κ ℓ σ)
```

or the local `D.interfaceSpace` adapter that instantiates to that compiled-basis
family.

Files here are kept as pressure tests / historical diagnostics, not as the final
Route B closure path.
