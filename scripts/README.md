# Scripts notes

## Set-multilinear scripts

There are two different measures here:

- `setmultilinear_rank.py`:
  Set-multilinear **partial-derivative matrix rank** (Nisan/LST-style measure).
- `setmultilinear_spdp_shift_restricted.py`:
  **Shift-restricted SPDP** diagnostic where shifts are limited to block-multilinear monomials.

These are intentionally different and should not be compared as the same rank measure.

## Metacomplexity scripts

- `metacomplexity.py`:
  Exact formula-size MCSP-style diagnostic for all Boolean functions on `n=2,3`.
- `kt_complexity.py`:
  A tiny tape-machine `K^t` model plus a richer compositional `K^t` upper-bound
  model.  The richer model is intentionally machine-relative: it shows how
  adding substitution/composition primitives changes which truth tables are
  visible to a bounded observer.
- `mcsp_vs_kt.py`:
  Compares formula-size MCSP, tape-machine `K^t`, compositional `K^t`, and
  compositional `K^t + XOR` on the same `n=3` truth tables.  The intended
  reading is diagnostic, not a lower-bound proof: AND/OR compression improves
  with composition, while parity flips only when XOR is admitted.
