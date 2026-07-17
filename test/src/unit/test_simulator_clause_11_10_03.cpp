#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(EmptyStringLiteralSim, EmptyStringLiteralIsZero) {
  SimFixture f;
  auto* expr = ParseExprFrom("\"\"", f);
  ASSERT_NE(expr, nullptr);
  auto val = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(val.ToUint64(), 0u);
  EXPECT_EQ(val.width, 8u);
}

TEST(EmptyStringLiteralSim, EmptyStringEqualsNul) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic result;\n"
      "  initial result = (\"\" == 8'd0);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(EmptyStringLiteralSim, EmptyStringDiffersFromStringZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic result;\n"
      "  initial result = (\"\" == \"0\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(EmptyStringLiteralSim, StringZeroHasAsciiValue) {
  SimFixture f;
  auto* expr = ParseExprFrom("\"0\"", f);
  ASSERT_NE(expr, nullptr);
  auto val = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(val.ToUint64(), 0x30u);
}

TEST(EmptyStringLiteralSim, EmptyStringEqualsExplicitNulEscape) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic result;\n"
      "  initial result = (\"\" == \"\\0\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(EmptyStringLiteralSim, ExplicitNulEscapeIsZero) {
  SimFixture f;
  auto* expr = ParseExprFrom("\"\\0\"", f);
  ASSERT_NE(expr, nullptr);
  auto val = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(val.ToUint64(), 0u);
  EXPECT_EQ(val.width, 8u);
}

TEST(EmptyStringLiteralSim, EmptyStringAssignedToVector) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [7:0] v;\n"
      "  initial v = \"\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("v");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(EmptyStringLiteralSim, EmptyStringIsFalsyInConditional) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    result = 1;\n"
      "    if (\"\") result = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §11.10.3: an empty string literal is one NUL byte, not nothing. Placed in the
// interior of a concatenation (§11.4.12 / §11.10.1), it must occupy a full
// zero-valued byte position: {"A", "", "B"} packs to the 24-bit value
// 0x41_00_42. Had the empty literal contributed zero bits, the result would
// instead be the 16-bit 0x4142 (0x004142 in the target), so this distinguishes
// the NUL-byte rule from a width-zero interpretation. The concatenation input
// is built from real source syntax and driven through the full pipeline.
TEST(EmptyStringLiteralSim, EmptyStringOccupiesNulByteInConcatenation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*3:1] v;\n"
      "  initial v = {\"A\", \"\", \"B\"};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("v");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x410042u);
}

}  // namespace
