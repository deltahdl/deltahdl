#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(VectorSpecification, Modulo2nWrap) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial v = 5'b10001;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  LowerAndRun(design, f);

  auto* var = f.ctx.FindVariable("v");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64() & 0xF, 1u);
}

TEST(VectorSpecification, OverflowAdditionWraps) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial v = 4'd15 + 4'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  LowerAndRun(design, f);

  auto* var = f.ctx.FindVariable("v");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64() & 0xF, 0u);
}

// §6.9.1: vectors obey modulo-2**n arithmetic, so subtracting past zero wraps
// around to the top of the range rather than going negative.
TEST(VectorSpecification, UnderflowSubtractionWraps) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial v = 4'd0 - 4'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  LowerAndRun(design, f);

  auto* var = f.ctx.FindVariable("v");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64() & 0xF, 15u);
}

TEST(VectorSpecification, MaxValueFitsInVector) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  initial v = 255;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  LowerAndRun(design, f);

  auto* var = f.ctx.FindVariable("v");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64() & 0xFF, 255u);
}

}  // namespace
