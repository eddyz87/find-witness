#include <stdint.h>
#include <stdbool.h>

typedef uint64_t u64;
typedef int64_t  s64;
typedef uint32_t u32;
typedef int32_t  s32;

#define min(a, b)	((a) < (b) ? (a) : (b))
#define max(a, b)	((a) > (b) ? (a) : (b))

/* ---------- tnum (from include/linux/tnum.h, kernel/bpf/tnum.c) ---------- */

struct tnum {
	u64 value;
	u64 mask;
};

#define TNUM(_v, _m)	((struct tnum){.value = (_v), .mask = (_m)})

/* fls64: find last (most significant) set bit, 1-indexed; returns 0 if v==0 */
static int fls64(u64 v)
{
	int r = 0;

	if (!v)
		return 0;
	if (v & 0xFFFFFFFF00000000ULL) { r += 32; v >>= 32; }
	if (v & 0x00000000FFFF0000ULL) { r += 16; v >>= 16; }
	if (v & 0x000000000000FF00ULL) { r +=  8; v >>=  8; }
	if (v & 0x00000000000000F0ULL) { r +=  4; v >>=  4; }
	if (v & 0x000000000000000CULL) { r +=  2; v >>=  2; }
	if (v & 0x0000000000000002ULL) { r +=  1; v >>=  1; }
	return r + (int)v;
}

static u64 tnum_step(struct tnum t, u64 z)
{
	u64 tmax, d, carry_mask, filled, inc;

	tmax = t.value | t.mask;

	if (z >= tmax)
		return tmax;

	if (z < t.value)
		return t.value;

	d = z - t.value;
	carry_mask = (1ULL << fls64(d & ~t.mask)) - 1;
	filled = d | carry_mask | ~t.mask;
	inc = (filled + 1) & t.mask;
	return t.value | inc;
}

static bool tnum_contains(struct tnum t, u64 v)
{
	return (v & ~t.mask) == t.value;
}


/* ---------- bpf_reg_state (subset from include/linux/bpf_verifier.h) ----- */

struct bpf_reg_state {
	s64 smin_value;
	s64 smax_value;
	u64 umin_value;
	u64 umax_value;
	s32 s32_min_value;
	s32 s32_max_value;
	u32 u32_min_value;
	u32 u32_max_value;
	struct tnum var_off;
};

#define UPPER_HALF 0xffffFFFF00000000ull

static bool find_witness_aux(u64 a_min, u64 a_max, u32 b_min, u32 b_max, struct tnum tnum, u64 *out)
__CPROVER_assigns(*out)
__CPROVER_ensures(
	__CPROVER_return_value ==>
		(a_min <= *out && *out <= a_max &&
		 b_min <= (u32)*out && (u32)*out <= b_max &&
		 ((*out & ~tnum.mask) == tnum.value))
)
__CPROVER_ensures(
	!__CPROVER_return_value ==>
		__CPROVER_forall { u64 v;
			!(a_min <= v && v <= a_max) ||
			!(b_min <= (u32)v && (u32)v <= b_max) ||
			!((v & ~tnum.mask) == tnum.value)
		}
)
{
	/* The 64-bit range [a_min, a_max] may span multiple 32-bit blocks.
	 * In the first block, tnum may only partially overlap with
	 * [b_min, b_max] (due to clamping to a_min).  But for any middle
	 * block that intersects with tnum, the set of low-32 tnum values
	 * is identical, so checking one middle block is enough.
	 */
	u64 w, tmax;
	u32 b_lo;

	tmax = tnum.value | tnum.mask;
	if (tmax < a_min)
		return false;

	/* check if tnum intersects with b_min/b_max in the first 32-bit block,
	 * clamp lower bound to (u32)a_min since lower values would give w < a_min.
	 */
	b_lo = max((u32)a_min, b_min);
	if (b_lo > b_max)
		goto next_block;

	w = (a_min & UPPER_HALF) | b_lo;
	if (!tnum_contains(tnum, w))
		w = tnum_step(tnum, w);
	if (a_min <= w && w <= a_max && b_min <= (u32)w && (u32)w <= b_max) {
		*out = w;
		return true;
	}

next_block:
	/* true if there are no more 32-bit blocks */
	if ((a_min & UPPER_HALF) == UPPER_HALF)
		return false;
	/* find the next 32-bit block intersecting with tnum,
	 * w is a minimal value in tnum within this block.
	 */
	w = (a_min & UPPER_HALF) + (1ull << 32);
	if (!tnum_contains(tnum, w))
		w = tnum_step(tnum, w);
	/* if (u32)w is to the left of b_min/b_max, try first b_min within this 32-bit block */
	if ((u32)w < b_min)
		w = (w & UPPER_HALF) | b_min;
	if (!tnum_contains(tnum, w))
		w = tnum_step(tnum, w);
	if (w <= a_max && b_min <= (u32)w && (u32)w <= b_max) {
		*out = w;
		return true;
	}
	return false;
}

static bool find_witness32(u64 a_min, u64 a_max, struct bpf_reg_state *reg, u64 *out)
{
	u32 b_umin = reg->u32_min_value;
	u32 b_umax = reg->u32_max_value;
	u32 b_smin = (u32)reg->s32_min_value;
	u32 b_smax = (u32)reg->s32_max_value;
	u32 lo, hi;

	if (reg->s32_min_value >= 0 || reg->s32_max_value < 0) {
		lo = max(b_umin, b_smin);
		hi = min(b_umax, b_smax);
		if (lo > hi)
			return false;
		return find_witness_aux(a_min, a_max, lo, hi, reg->var_off, out);
	}

	/* s32 range crosses sign boundary:
	 * two u32 intervals [0, smax] and [smin, U32_MAX]
	 */

	/* interval 1: [0, smax] intersected with [b_umin, b_umax] */
	hi = min(b_umax, b_smax);
	if (b_umin <= hi && find_witness_aux(a_min, a_max, b_umin, hi, reg->var_off, out))
		return true;

	/* interval 2: [smin, U32_MAX] intersected with [b_umin, b_umax] */
	lo = max(b_umin, b_smin);
	if (lo <= b_umax && find_witness_aux(a_min, a_max, lo, b_umax, reg->var_off, out))
		return true;

	return false;
}

static bool find_witness(struct bpf_reg_state *reg, u64 *out)
{
	u64 umin = reg->umin_value;
	u64 umax = reg->umax_value;
	u64 smin = (u64)reg->smin_value;
	u64 smax = (u64)reg->smax_value;
	u64 lo, hi;

	if (reg->smin_value >= 0 || reg->smax_value < 0) {
		/* s64 range does not cross sign boundary:
		 * single u64 interval [smin, smax]
		 */
		lo = max(umin, smin);
		hi = min(umax, smax);
		if (lo > hi)
			return false;
		return find_witness32(lo, hi, reg, out);
	}

	/* s64 range crosses sign boundary:
	 * two u64 intervals [0, smax] and [smin, U64_MAX]
	 */

	/* interval 1: [0, smax] intersected with [umin, umax] */
	hi = min(umax, smax);
	if (umin <= hi && find_witness32(umin, hi, reg, out))
		return true;

	/* interval 2: [smin, U64_MAX] intersected with [umin, umax] */
	lo = max(umin, smin);
	if (lo <= umax && find_witness32(lo, umax, reg, out))
		return true;

	return false;
}

/* ---------- CBMC nondet primitives --------------------------------------- */

u64 nondet_u64(void);
s64 nondet_s64(void);
u32 nondet_u32(void);
s32 nondet_s32(void);

/* Well-formedness: value & mask == 0 (no bit both known and unknown) */
static bool tnum_well_formed(struct tnum t)
{
	return (t.value & t.mask) == 0;
}

static struct bpf_reg_state mk_reg(void)
{
	return (struct bpf_reg_state) {
		.umin_value    = nondet_u64(),
		.umax_value    = nondet_u64(),
		.smin_value    = nondet_s64(),
		.smax_value    = nondet_s64(),
		.u32_min_value = nondet_u32(),
		.u32_max_value = nondet_u32(),
		.s32_min_value = nondet_s32(),
		.s32_max_value = nondet_s32(),
		.var_off       = { .value = nondet_u64(), .mask = nondet_u64() },
	};
}

#define in_all(v, reg)							\
	(((reg)->umin_value    <= (u64)(v) && (u64)(v) <= (reg)->umax_value) &&	\
	 ((reg)->smin_value    <= (s64)(v) && (s64)(v) <= (reg)->smax_value) &&	\
	 ((reg)->u32_min_value <= (u32)(v) && (u32)(v) <= (reg)->u32_max_value) && \
	 ((reg)->s32_min_value <= (s32)(v) && (s32)(v) <= (reg)->s32_max_value) && \
	 tnum_contains((reg)->var_off, (v)))

/* ---------- checks ------------------------------------------------------- */

static void check_sound(void)
{
	struct tnum tnum = { nondet_u64(), nondet_u64() };
	u64 a_min = nondet_u64();
	u64 a_max = nondet_u64();
	u32 b_min = nondet_u32();
	u32 b_max = nondet_u32();
	u64 v = nondet_u64();
	u64 w;

	__CPROVER_assume(tnum_well_formed(tnum));
	__CPROVER_assume(a_min <= a_max);
	__CPROVER_assume(b_min <= b_max);

	__CPROVER_assume(a_min <= v && v <= a_max);
	__CPROVER_assume(b_min <= (u32)v && (u32)v <= b_max);
	__CPROVER_assume(tnum_contains(tnum, v));

	__CPROVER_assert(find_witness_aux(a_min, a_max, b_min, b_max, tnum, &w),
			 "should always find a witness if one exists");
}

static void check_complete(void)
{
	struct tnum tnum = { nondet_u64(), nondet_u64() };
	u64 a_min = nondet_u64();
	u64 a_max = nondet_u64();
	u32 b_min = nondet_u32();
	u32 b_max = nondet_u32();
	u64 w;

	__CPROVER_assume(tnum_well_formed(tnum));
	__CPROVER_assume(a_min <= a_max);
	__CPROVER_assume(b_min <= b_max);
	__CPROVER_assume(find_witness_aux(a_min, a_max, b_min, b_max, tnum, &w));

	__CPROVER_assert(a_min <= w && w <= a_max, "witness in 64-bit range");
	__CPROVER_assert(b_min <= (u32)w && (u32)w <= b_max, "witness in 32-bit range");
	__CPROVER_assert(tnum_contains(tnum, w), "witness in tnum");
}

static void assume_well_formed(struct bpf_reg_state *reg)
{
	__CPROVER_assume(tnum_well_formed(reg->var_off));
	__CPROVER_assume(reg->umin_value <= reg->umax_value);
	__CPROVER_assume(reg->smin_value <= reg->smax_value);
	__CPROVER_assume(reg->u32_min_value <= reg->u32_max_value);
	__CPROVER_assume(reg->s32_min_value <= reg->s32_max_value);
}

static void check_fw_sound(void)
{
	struct bpf_reg_state reg = mk_reg();
	u64 v = nondet_u64();
	u64 w;

	assume_well_formed(&reg);
	__CPROVER_assume(in_all(v, &reg));

	__CPROVER_assert(find_witness(&reg, &w),
			 "find_witness: should find a witness if one exists");
}

static void check_fw_complete(void)
{
	struct bpf_reg_state reg = mk_reg();
	u64 w;

	assume_well_formed(&reg);
	__CPROVER_assume(find_witness(&reg, &w));

	__CPROVER_assert(in_all(w, &reg),
			 "find_witness: returned witness must satisfy all bounds");
}

void main(void)
{
	check_sound();
	check_complete();
	check_fw_sound();
	check_fw_complete();
}
