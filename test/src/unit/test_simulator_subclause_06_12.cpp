#include <string>

#include "fixture_real.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §6.12: shortreal is the same as a C float, while real is the same as a C
// double. The distinguishing consequence is precision: a value assigned to a
// shortreal is rounded to single precision, so widening it back to a real no
// longer equals the original double-precision literal. 0.1 has no exact binary
// representation, so float(0.1) != double(0.1). Driven through the full
// pipeline so the shortreal declaration (32-bit real storage) and the
// real<-shortreal widening are the production conversion path, not a stub.
TEST(RealDataType, ShortrealHasSinglePrecision) {
  auto v = RunAndGet(
      "module t;\n"
      "  shortreal s;\n"
      "  real rs, rr;\n"
      "  logic differs;\n"
      "  initial begin\n"
      "    s = 0.1;\n"
      "    rs = s;\n"
      "    rr = 0.1;\n"
      "    differs = (rs != rr);\n"
      "  end\n"
      "endmodule\n",
      "differs");
  EXPECT_EQ(v, 1u);
}

// §6.12: "The shortreal data type is the same as a C float", and footnote 19
// on the same page: "The real and shortreal types are represented as described
// by IEEE Std 754". A shortreal therefore holds a 32-bit single-precision
// pattern, and every reader of that storage has to decode it as a float. This
// case reads the value back out through a format specification, which is the
// decode path a user reaches with $display, $write and $sformat, and which is
// distinct from the real<-shortreal widening.
//
// Nothing above it covers that path. ShortrealHasSinglePrecision reads through
// `rs = s`, the one decode that is already width-aware, so it passes whatever
// the formatter does. VariableDeclaration.ShortrealDefaultIsZero in
// test/src/unit/test_simulator_subclause_06_08.cpp:159 asserts on the value 0,
// whose float pattern and double pattern are both an all-zero word, so it holds
// under either decoding and can never fail on this.
//
// float(0.1) rendered with %f's default six fractional digits is 0.100000.
TEST(RealDataType, ShortrealDisplaysItsStoredValue) {
  SimFixture f;
  std::string printed = RunCapture(
      "module t;\n"
      "  shortreal s;\n"
      "  string out;\n"
      "  initial begin\n"
      "    s = 0.1;\n"
      "    $sformat(out, \"%f\", s);\n"
      "    $display(\"%s\", out);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(printed, "0.100000\n");
}

// §6.12: real is the same as a C double, so a value carried through a real
// keeps full double precision and stays equal to the same double-precision
// literal. This is the accepting counterpart to ShortrealHasSinglePrecision.
TEST(RealDataType, RealKeepsDoublePrecision) {
  auto v = RunAndGet(
      "module t;\n"
      "  real r1, r2;\n"
      "  logic differs;\n"
      "  initial begin\n"
      "    r1 = 0.1;\n"
      "    r2 = 0.1;\n"
      "    differs = (r1 != r2);\n"
      "  end\n"
      "endmodule\n",
      "differs");
  EXPECT_EQ(v, 0u);
}

TEST(RealDataType, RealVarStorage) {
  RealFixture f;
  f.CreateRealVar("x", 1.5);
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_NEAR(VecToDouble(var->value), 1.5, 1e-10);
}

TEST(RealDataType, IsRealVariable) {
  RealFixture f;
  f.CreateRealVar("r", 0.0);
  EXPECT_TRUE(f.ctx.IsRealVariable("r"));
  f.ctx.CreateVariable("i", 32);
  EXPECT_FALSE(f.ctx.IsRealVariable("i"));
}

}  // namespace
