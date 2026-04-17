#include <stdint.h>
#include <stdbool.h>

typedef uint64_t u64;
typedef uint32_t u32;

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


#define UPPER_HALF 0xffffFFFF00000000ull

static bool find_witness_aux(u64 a_min, u64 a_max, u32 b_min, u32 b_max, struct tnum tnum, u64 *out)
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

/* ---------- CBMC nondet primitives --------------------------------------- */

u64 nondet_u64(void);
u32 nondet_u32(void);

/* Well-formedness: value & mask == 0 (no bit both known and unknown) */
static bool tnum_well_formed(struct tnum t)
{
	return (t.value & t.mask) == 0;
}

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

void main(void)
{
	check_sound();
	check_complete();
}
