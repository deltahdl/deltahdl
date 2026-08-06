#include "fixture_real.h"
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
