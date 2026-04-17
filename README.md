# CBMC tests for find_witness_aux

Formal verification of `find_witness_aux()` using [CBMC](https://www.cprover.org/cbmc/).

`main.c` contains a self-contained extract of:
- `struct tnum` with `tnum_step`, `tnum_contains`
- `find_witness_aux` — given a 64-bit range `[a_min, a_max]`, a 32-bit
  range `[b_min, b_max]`, and a `tnum`, finds a value satisfying all
  three constraints

## Properties checked

**check_sound** — if a value `v` satisfies all constraints (64-bit range,
32-bit range, tnum membership), then `find_witness_aux` returns true.
Equivalently, if `find_witness_aux` returns false, no such value exists.

**check_complete** — if `find_witness_aux` returns true, the witness `w`
it outputs actually satisfies all three constraints.

Together these prove full correctness: `find_witness_aux` returns true
if and only if a valid witness exists, and when it does, the returned
witness is valid.

## Usage

    make                   # run both checks
    make check-sound       # run soundness only
    make check-complete    # run completeness only

Requires `cbmc` in PATH.
