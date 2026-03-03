// §9.4.2.2: Implicit event_expression list

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// 1. always @* with simple combinational AND gate: y = a & b.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarSimpleAnd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always @* y = a & b;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    b = 8'h3C;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0x30u);
}

// ---------------------------------------------------------------------------
// 2. always @* with if-else selects the true branch.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarIfElseTrueBranch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b, y;\n"
      "  always @*\n"
      "    if (sel) y = a;\n"
      "    else y = b;\n"
      "  initial begin\n"
      "    a = 8'hAA;\n"
      "    b = 8'hBB;\n"
      "    sel = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xAAu);
}

// ---------------------------------------------------------------------------
// 3. always @* with case statement selects the correct arm.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarCaseStatement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] y;\n"
      "  always @*\n"
      "    case (sel)\n"
      "      2'b00: y = 8'h10;\n"
      "      2'b01: y = 8'h20;\n"
      "      2'b10: y = 8'h30;\n"
      "      default: y = 8'hFF;\n"
      "    endcase\n"
      "  initial begin\n"
      "    sel = 2'b10;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0x30u);
}

// ---------------------------------------------------------------------------
// 4. always @* sensitivity includes all RHS signals (a, b, c).
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarAllRhsSensitive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c, y;\n"
      "  always @* y = a + b + c;\n"
      "  initial begin\n"
      "    a = 8'h10;\n"
      "    b = 8'h20;\n"
      "    c = 8'h03;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // 0x10 + 0x20 + 0x03 = 0x33.
  EXPECT_EQ(y->value.ToUint64(), 0x33u);
}

// ---------------------------------------------------------------------------
// 5. always @* does NOT include LHS signal 'y' in sensitivity.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarLhsNotSensitive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, y;\n"
      "  always @* y = a + 1;\n"
      "  initial begin\n"
      "    a = 8'h09;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // y = 0x09 + 1 = 0x0A. No infinite loop from self-triggering.
  EXPECT_EQ(y->value.ToUint64(), 0x0Au);
}

// ---------------------------------------------------------------------------
// 6. always @(*) form (with parentheses) is equivalent to @*.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarParenForm) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always @(*) y = a | b;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    b = 8'h0F;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xFFu);
}

}  // namespace
