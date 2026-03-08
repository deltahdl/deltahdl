#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §11.10.3: Empty string literal has value zero.
TEST(SimA11103, EmptyStringLiteralIsZero) {
  SimFixture f;
  auto* expr = ParseExprFrom("\"\"", f);
  ASSERT_NE(expr, nullptr);
  auto val = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(val.ToUint64(), 0u);
  EXPECT_EQ(val.width, 8u);
}

// §11.10.3: Empty string literal equals ASCII NUL (\0).
TEST(SimA11103, EmptyStringEqualsNul) {
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

// §11.10.3: Empty string literal is different from string "0".
TEST(SimA11103, EmptyStringDiffersFromStringZero) {
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
  // "" = 8'h00, "0" = 8'h30 — they are not equal.
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §11.10.3: "0" has value 0x30 (ASCII code for '0').
TEST(SimA11103, StringZeroHasAsciiValue) {
  SimFixture f;
  auto* expr = ParseExprFrom("\"0\"", f);
  ASSERT_NE(expr, nullptr);
  auto val = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(val.ToUint64(), 0x30u);
}

// §11.10.3: Empty string assigned to vector produces zero.
TEST(SimA11103, EmptyStringAssignedToVector) {
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

}  // namespace
