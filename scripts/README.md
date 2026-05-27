# Scripts notes

## Set-multilinear scripts

There are two different measures here:

- `setmultilinear_rank.py`:
  Set-multilinear **partial-derivative matrix rank** (Nisan/LST-style measure).
- `setmultilinear_spdp_shift_restricted.py`:
  **Shift-restricted SPDP** diagnostic where shifts are limited to block-multilinear monomials.

These are intentionally different and should not be compared as the same rank measure.
