#include <cstring>

#include "builders_systask.h"
#include "helpers_eval_op.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(SysTask, ItoRConvertsIntToReal) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$itor", {MkInt(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 64u);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 42.0);
}

TEST(SysTask, RtoIConvertsRealToInt) {
  SysTaskFixture f;
  double dval = 3.7;
  uint64_t bits = 0;
  std::memcpy(&bits, &dval, sizeof(double));
  auto* real_arg = f.arena.Create<Expr>();
  real_arg->kind = ExprKind::kRealLiteral;
  real_arg->real_val = dval;
  auto* expr = MkSysCall(f.arena, "$rtoi", {real_arg});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
  EXPECT_EQ(result.ToUint64(), 3u);
}

TEST(SysTask, BitstorealReinterpretsBitsAsReal) {
  SysTaskFixture f;
  double expected = 42.0;
  uint64_t bits = 0;
  std::memcpy(&bits, &expected, sizeof(double));
  auto* expr = MkSysCall(f.arena, "$bitstoreal", {MkInt(f.arena, bits)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 64u);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 42.0);
}

TEST(SysTask, RealtobitsReinterpretsRealAsBits) {
  SysTaskFixture f;
  double dval = 42.0;
  auto* real_arg = f.arena.Create<Expr>();
  real_arg->kind = ExprKind::kRealLiteral;
  real_arg->real_val = dval;
  auto* expr = MkSysCall(f.arena, "$realtobits", {real_arg});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 64u);
  uint64_t expected_bits = 0;
  std::memcpy(&expected_bits, &dval, sizeof(double));
  EXPECT_EQ(result.ToUint64(), expected_bits);
}

// $shortrealtobits yields the 32-bit single-precision representation of the
// shortreal value.
TEST(SysTask, ShortrealtobitsReinterpretsShortrealAs32Bits) {
  SysTaskFixture f;
  double dval = 1.5;  // exactly representable in single precision
  uint64_t dbits = 0;
  std::memcpy(&dbits, &dval, sizeof(double));
  auto* expr = MkSysCall(f.arena, "$shortrealtobits", {MkInt(f.arena, dbits)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
  float fval = static_cast<float>(dval);
  uint32_t expected_bits = 0;
  std::memcpy(&expected_bits, &fval, sizeof(float));
  EXPECT_EQ(result.ToUint64() & 0xFFFFFFFFu, expected_bits);
}

// $bitstoshortreal turns a 32-bit pattern (as produced by $shortrealtobits)
// back into a shortreal value.
TEST(SysTask, BitstoshortrealReinterprets32BitsAsShortreal) {
  SysTaskFixture f;
  float fval = 1.5f;
  uint32_t fbits = 0;
  std::memcpy(&fbits, &fval, sizeof(float));
  auto* expr = MkSysCall(f.arena, "$bitstoshortreal", {MkInt(f.arena, fbits)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 64u);
  EXPECT_TRUE(result.is_real);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), 1.5);
}

// NOTE 1: conversions round the result to the nearest valid IEEE 754
// representation rather than truncating the mantissa. 0.1 is not exactly
// representable in single precision, so the narrowed value must match the
// round-to-nearest single-precision result.
TEST(SysTask, ShortrealtobitsRoundsToNearestRepresentation) {
  SysTaskFixture f;
  double dval = 0.1;
  uint64_t dbits = 0;
  std::memcpy(&dbits, &dval, sizeof(double));
  auto* expr = MkSysCall(f.arena, "$shortrealtobits", {MkInt(f.arena, dbits)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  float rounded = static_cast<float>(dval);
  uint32_t expected_bits = 0;
  std::memcpy(&expected_bits, &rounded, sizeof(float));
  EXPECT_EQ(result.ToUint64() & 0xFFFFFFFFu, expected_bits);
}

// $signed returns a value with the same size and value as the input, marked
// signed.
TEST(SysTask, SignedCastPreservesSizeAndValueAndMarksSigned) {
  SysTaskFixture f;
  auto in = EvalExpr(MkInt(f.arena, 0xABCDu), f.ctx, f.arena);
  auto* expr = MkSysCall(f.arena, "$signed", {MkInt(f.arena, 0xABCDu)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
  EXPECT_EQ(result.width, in.width);
  EXPECT_EQ(result.ToUint64(), in.ToUint64());
}

// $unsigned returns a value with the same size and value as the input, marked
// unsigned.
TEST(SysTask, UnsignedCastPreservesSizeAndValueAndMarksUnsigned) {
  SysTaskFixture f;
  auto in = EvalExpr(MkInt(f.arena, 0xABCDu), f.ctx, f.arena);
  auto* expr = MkSysCall(f.arena, "$unsigned", {MkInt(f.arena, 0xABCDu)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
  EXPECT_EQ(result.width, in.width);
  EXPECT_EQ(result.ToUint64(), in.ToUint64());
}

// $rtoi truncates rather than rounds, and truncation is toward zero: a
// negative real loses its fractional part without moving toward -infinity, so
// -3.7 becomes -3 (0xFFFFFFFD in the 32-bit result).
TEST(SysTask, RtoiTruncatesNegativeTowardZero) {
  SysTaskFixture f;
  auto* real_arg = f.arena.Create<Expr>();
  real_arg->kind = ExprKind::kRealLiteral;
  real_arg->real_val = -3.7;
  auto* expr = MkSysCall(f.arena, "$rtoi", {real_arg});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
  EXPECT_EQ(result.ToUint64(), 0xFFFFFFFDu);
}

// $bitstoreal recovers the original real value from a bit pattern produced by
// $realtobits, so chaining the two is an identity on the real value.
TEST(SysTask, BitstorealInvertsRealtobitsRoundTrip) {
  SysTaskFixture f;
  double dval = 3.14159;
  auto* real_arg = f.arena.Create<Expr>();
  real_arg->kind = ExprKind::kRealLiteral;
  real_arg->real_val = dval;
  auto* to_bits = MkSysCall(f.arena, "$realtobits", {real_arg});
  auto bits = EvalExpr(to_bits, f.ctx, f.arena);
  auto* from_bits =
      MkSysCall(f.arena, "$bitstoreal", {MkInt(f.arena, bits.ToUint64())});
  auto result = EvalExpr(from_bits, f.ctx, f.arena);
  EXPECT_EQ(result.width, 64u);
  EXPECT_DOUBLE_EQ(ResultToDouble(result), dval);
}

// The signedness casts change only the signedness, never the bit pattern, so
// the "same value" guarantee holds even when the most significant bit is set.
TEST(SysTask, CastFunctionsPreserveValueWithHighBitSet) {
  SysTaskFixture f;
  auto in = EvalExpr(MkInt(f.arena, 0xFFFFFFFFu), f.ctx, f.arena);

  auto* signed_expr =
      MkSysCall(f.arena, "$signed", {MkInt(f.arena, 0xFFFFFFFFu)});
  auto signed_res = EvalExpr(signed_expr, f.ctx, f.arena);
  EXPECT_TRUE(signed_res.is_signed);
  EXPECT_EQ(signed_res.width, in.width);
  EXPECT_EQ(signed_res.ToUint64(), in.ToUint64());

  auto* unsigned_expr =
      MkSysCall(f.arena, "$unsigned", {MkInt(f.arena, 0xFFFFFFFFu)});
  auto unsigned_res = EvalExpr(unsigned_expr, f.ctx, f.arena);
  EXPECT_FALSE(unsigned_res.is_signed);
  EXPECT_EQ(unsigned_res.width, in.width);
  EXPECT_EQ(unsigned_res.ToUint64(), in.ToUint64());
}

}  // namespace
