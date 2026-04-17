# CBMC verification of find_witness

Formal verification of `find_witness()` — given a `struct bpf_reg_state`,
find a concrete value satisfying all bounds (u64, s64, u32, s32, tnum).

`main.c` contains a self-contained extract of:
- `struct tnum` with `tnum_step`, `tnum_contains`
- `struct bpf_reg_state` with range fields and `var_off`
- `find_witness_aux` — finds a witness in a 64-bit range intersected
  with a 32-bit range and tnum
- `find_witness32` — subdivides s32/u32 ranges at the sign boundary
- `find_witness` — subdivides s64/u64 ranges at the sign boundary,
  delegates to `find_witness32`

## Properties checked

### find_witness_aux (direct verification)

**check_sound** — if a witness exists, `find_witness_aux` returns true.

**check_complete** — if `find_witness_aux` returns true, the returned
witness satisfies all constraints.

### find_witness (modular verification via contracts)

**check_fw_sound** — if a value satisfies all `bpf_reg_state` bounds,
`find_witness` returns true.

**check_fw_complete** — if `find_witness` returns true, the returned
witness satisfies all `bpf_reg_state` bounds.

These use a `__CPROVER_ensures` contract on `find_witness_aux`,
verified once and then replaced at call sites via `goto-instrument
--replace-call-with-contract`.

## Usage

    make                     # run all checks
    make check-sound         # find_witness_aux soundness
    make check-complete      # find_witness_aux completeness
    make check-fw-sound      # find_witness soundness (modular)
    make check-fw-complete   # find_witness completeness (modular)

Requires `cbmc` in PATH. Modular checks require `goto-cc` and
`goto-instrument` (set `CBMC_BIN` in Makefile).
