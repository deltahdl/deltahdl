#include <gtest/gtest.h>

#include <cstdint>
#include <cstring>
#include <string>

#include "builders_systask.h"
#include "common/arena.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

Expr* MkReal(Arena& arena, double val) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kRealLiteral;
  e->real_val = val;
  return e;
}

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

TEST(SysTask, ShortrealtobitsReinterpretsShortrealAs32Bits) {
  SysTaskFixture f;
  double dval = 1.5;
  auto* expr = MkSysCall(f.arena, "$shortrealtobits", {MkReal(f.arena, dval)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
  auto fval = static_cast<float>(dval);
  uint32_t expected_bits = 0;
  std::memcpy(&expected_bits, &fval, sizeof(float));
  EXPECT_EQ(result.ToUint64() & 0xFFFFFFFFu, expected_bits);
}

TEST(SysTask, BitstoshortrealReinterprets32BitsAsShortreal) {
  SysTaskFixture f;
  auto* expr =
      MkSysCall(f.arena, "$bitstoshortreal", {MkInt(f.arena, 0x3DCCCCCDu)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
  EXPECT_TRUE(result.is_real);
  EXPECT_EQ(result.ToUint64(), 0x3DCCCCCDu);
}

TEST(SysTask, ShortrealtobitsRoundsToNearestRepresentation) {
  SysTaskFixture f;
  double dval = 0.1;
  auto* expr = MkSysCall(f.arena, "$shortrealtobits", {MkReal(f.arena, dval)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  auto rounded = static_cast<float>(dval);
  uint32_t expected_bits = 0;
  std::memcpy(&expected_bits, &rounded, sizeof(float));
  EXPECT_EQ(result.ToUint64() & 0xFFFFFFFFu, expected_bits);
}

TEST(SysTask, ShortrealtobitsReadsAShortrealVariable) {
  auto b = RunAndGet(
      "module t;\n"
      "  shortreal s;\n"
      "  int b;\n"
      "  initial begin\n"
      "    s = 1.5;\n"
      "    b = $shortrealtobits(s);\n"
      "  end\n"
      "endmodule\n",
      "b");
  EXPECT_EQ(b, 0x3FC00000u);
}

TEST(SysTask, SignedCastPreservesSizeAndValueAndMarksSigned) {
  SysTaskFixture f;
  auto in = EvalExpr(MkInt(f.arena, 0xABCDu), f.ctx, f.arena);
  auto* expr = MkSysCall(f.arena, "$signed", {MkInt(f.arena, 0xABCDu)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
  EXPECT_EQ(result.width, in.width);
  EXPECT_EQ(result.ToUint64(), in.ToUint64());
}

TEST(SysTask, UnsignedCastPreservesSizeAndValueAndMarksUnsigned) {
  SysTaskFixture f;
  auto in = EvalExpr(MkInt(f.arena, 0xABCDu), f.ctx, f.arena);
  auto* expr = MkSysCall(f.arena, "$unsigned", {MkInt(f.arena, 0xABCDu)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
  EXPECT_EQ(result.width, in.width);
  EXPECT_EQ(result.ToUint64(), in.ToUint64());
}

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

TEST(SysTask, ItorAndBitstorealResultsAreReal) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  real r;\n"
                       "  initial begin\n"
                       "    r = $itor(5) + 1;\n"
                       "    $display(\"%f %f %f\", $itor(5), r,\n"
                       "             $bitstoreal(64'h3ff8000000000000));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "5.000000 6.000000 1.500000\n");
}

TEST(ConversionSim, RtoiResultIsASignedInteger) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  real b = -2.7;\n"
                       "  initial $display(\"%0d %0d %0d\", $rtoi(b), "
                       "$rtoi(-2.7), $rtoi(b) < 0);\n"
                       "endmodule\n",
                       f),
            "-2 -2 1\n");
}

TEST(ConversionSim, ConversionFunctionsGiveTheirStandardResultTypes) {
  struct Probe {
    const char* what;
    const char* expr;
    uint64_t expected;
  };
  const Probe kProbes[] = {
      {"$rtoi gives an integer", "type($rtoi(r)) == type(integer)", 1},
      {"$rtoi does not give an int", "type($rtoi(r)) == type(int)", 0},
      {"$itor gives a real", "type($itor(3)) == type(real)", 1},
      {"$bitstoreal gives a real", "type($bitstoreal(64'h0)) == type(real)", 1},
      {"$realtobits is unsigned", "$realtobits(-1.0) > 0", 1},
      {"$shortrealtobits is unsigned", "$shortrealtobits(-1.0) > 0", 1},
      {"$bitstoshortreal is 32 bits wide", "$bits($bitstoshortreal(32'h0))",
       32},
      {"$bitstoshortreal gives a shortreal",
       "type($bitstoshortreal(32'h0)) == type(shortreal)", 1},
      {"$bitstoshortreal does not give a real",
       "type($bitstoshortreal(32'h0)) == type(real)", 0},
      {"$bitstoshortreal round trips through $shortrealtobits",
       "$shortrealtobits($bitstoshortreal(32'h3DCCCCCD))", 0x3DCCCCCDu},
      {"$bitstoshortreal widens to the binary32's value",
       "$realtobits($bitstoshortreal(32'h3DCCCCCD))", 0x3FB99999A0000000u},
  };
  for (const Probe& probe : kProbes) {
    SCOPED_TRACE(probe.what);
    const std::string kSrc = std::string(
                                 "module t;\n"
                                 "  real r = 2.5;\n"
                                 "  bit [63:0] v;\n"
                                 "  initial v = ") +
                             probe.expr + ";\nendmodule\n";
    EXPECT_EQ(RunAndGet(kSrc, "v"), probe.expected);
  }
}

TEST(ConversionSim,
     BitPatternFunctionsGiveIeee754ValuesAtRunTimeAndAsConstants) {
  struct Probe {
    const char* what;
    const char* expr;
    uint64_t expected;
  };
  const Probe kProbes[] = {
      {"package parameter from $realtobits", "pk::A", 0x3FB999999999999Au},
      {"package parameter from $shortrealtobits", "pk::B", 0x3DCCCCCDu},
      {"package parameter from $bitstoreal", "$realtobits(pk::C)",
       0x3FB999999999999Au},
      {"package parameter from $bitstoshortreal", "$shortrealtobits(pk::D)",
       0x3DCCCCCDu},
      {"module localparam from $realtobits", "MA", 0x3FB999999999999Au},
      {"module localparam from $shortrealtobits", "MB", 0x3DCCCCCDu},
      {"module localparam from $bitstoreal", "$realtobits(MC)",
       0x3FB999999999999Au},
      {"module localparam from $bitstoshortreal", "$shortrealtobits(MD)",
       0x3DCCCCCDu},
      {"$itor folds to a real", "$realtobits(HALF)", 0x4004000000000000u},
      {"packed range bound from $rtoi", "$bits(v4)", 4},
      {"constant beyond the binary32 range", "INF", 0x7F800000u},
      {"constant binary32 subnormal", "$realtobits(SUB)", 0x36A0000000000000u},
      {"constant infinity round trip", "PINF", 0x7FF0000000000000u},
      {"run-time value beyond the binary32 range", "$shortrealtobits(big)",
       0x7F800000u},
      {"run-time negative value beyond the binary32 range",
       "$shortrealtobits(-big)", 0xFF800000u},
      {"run-time binary32 subnormal", "$realtobits($bitstoshortreal(32'h1))",
       0x36A0000000000000u},
      {"run-time infinity round trip",
       "$realtobits($bitstoreal(64'h7FF0000000000000))", 0x7FF0000000000000u},
  };
  for (const Probe& probe : kProbes) {
    SCOPED_TRACE(probe.what);
    const std::string kSrc =
        std::string(
            "package pk;\n"
            "  parameter logic [63:0] A = $realtobits(0.1);\n"
            "  parameter logic [31:0] B = $shortrealtobits(0.1);\n"
            "  parameter real C = $bitstoreal(64'h3FB999999999999A);\n"
            "  parameter shortreal D = $bitstoshortreal(32'h3DCCCCCD);\n"
            "endpackage\n"
            "module t;\n"
            "  localparam logic [63:0] MA = $realtobits(0.1);\n"
            "  localparam logic [31:0] MB = $shortrealtobits(0.1);\n"
            "  localparam real MC = $bitstoreal(64'h3FB999999999999A);\n"
            "  localparam shortreal MD = $bitstoshortreal(32'h3DCCCCCD);\n"
            "  localparam real HALF = $itor(5) / 2;\n"
            "  localparam logic [31:0] INF = $shortrealtobits(1e39);\n"
            "  localparam real SUB = $bitstoshortreal(32'h1);\n"
            "  localparam logic [63:0] PINF =\n"
            "      $realtobits($bitstoreal(64'h7FF0000000000000));\n"
            "  logic [$rtoi(3.9):0] v4;\n"
            "  real big = 1e39;\n"
            "  bit [63:0] v;\n"
            "  initial v = ") +
        probe.expr + ";\nendmodule\n";
    EXPECT_EQ(RunAndGet(kSrc, "v"), probe.expected);
  }
}

TEST(ConversionSim, ItorAndBitstorealResultsAreReals) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  real r;\n"
                 "  int k = 16;\n"
                 "  initial begin\n"
                 "    r = $itor(k);\n"
                 "    $display(\"%f %0d %0d\", r, $rtoi($sqrt($itor(k))), "
                 "$bitstoreal($realtobits(0.1)) == 0.1);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "16.000000 4 1\n");
}

TEST(ConversionSim, RealtobitsAndShortrealtobitsConvertTheirOperandByValue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int i = 3, n = -2;\n"
                       "  shortreal s = 3.0;\n"
                       "  real r = 0.1;\n"
                       "  initial $display(\"%h %h %h %h %h\", $realtobits(i), "
                       "$realtobits(n), $realtobits(s), $shortrealtobits(i), "
                       "$shortrealtobits(r));\n"
                       "endmodule\n",
                       f),
            "4008000000000000 c000000000000000 4008000000000000 40400000 "
            "3dcccccd\n");
}

TEST(ConversionSim, RtoiConvertsAnIntegralOperandByValue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int i = 7;\n"
                       "  byte signed b = -3;\n"
                       "  initial $display(\"%0d %0d\", $rtoi(i), $rtoi(b));\n"
                       "endmodule\n",
                       f),
            "7 -3\n");
}

TEST(ConversionSim, ItorConvertsItsOperandToAnIntegerByValue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  byte signed b = -3;\n"
                       "  real r = 2.5, q = -2.5;\n"
                       "  initial $display(\"%f %f %f\", $itor(b), $itor(r), "
                       "$itor(q));\n"
                       "endmodule\n",
                       f),
            "-3.000000 3.000000 -3.000000\n");
}

}  // namespace
