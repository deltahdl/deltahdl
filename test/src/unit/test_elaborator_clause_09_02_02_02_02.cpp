// Non-LRM tests

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §9.2.2.2.2: always @* elaborates as kAlways, not kAlwaysComb.
TEST(ElabClause09_02_02_02_02, AlwaysStarIsAlwaysKind) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, y;\n"
      "  always @* y = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  EXPECT_EQ(proc.kind, RtlirProcessKind::kAlways);
}

// §9.2.2.2.2: always @* allows multiple processes to assign same variable.
TEST(ElabClause09_02_02_02_02, AlwaysStarNoMultiDriverError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b, y;\n"
      "  always @* y = a;\n"
      "  always @* y = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.2.2.2.2: always @* can contain timing controls (no error).
TEST(ElabClause09_02_02_02_02, AlwaysStarAllowsTimingControl) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, a;\n"
      "  always @(posedge clk) a = ~a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.2.2.2.2: always_comb rejects timing controls (contrast with always @*).
TEST(ElabClause09_02_02_02_02, AlwaysCombRejectsTimingControl) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic a;\n"
      "  always_comb #5 a = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SimCh9, AlwaysCombExecutesAtTimeZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial a = 8'd0;\n"
      "  always_comb begin\n"
      "    result = a + 8'd1;\n"
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

TEST(SimCh9, AlwaysCombNotGate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 8'h0F;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = (~a) & 8'hFF;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xF0u);
}

TEST(SimCh9, AlwaysCombMuxIfElse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b, result;\n"
      "  initial begin\n"
      "    sel = 1;\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "  end\n"
      "  always_comb begin\n"
      "    if (sel)\n"
      "      result = a;\n"
      "    else\n"
      "      result = b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(SimCh9, AlwaysCombIfElseBranch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b, result;\n"
      "  initial begin\n"
      "    sel = 0;\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "  end\n"
      "  always_comb begin\n"
      "    if (sel)\n"
      "      result = a;\n"
      "    else\n"
      "      result = b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(SimCh9, AlwaysCombCaseDecode) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] result;\n"
      "  initial sel = 2'd2;\n"
      "  always_comb begin\n"
      "    case (sel)\n"
      "      2'd0: result = 8'd10;\n"
      "      2'd1: result = 8'd20;\n"
      "      2'd2: result = 8'd30;\n"
      "      2'd3: result = 8'd40;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(SimCh9b, AlwaysCombConstAssignTime0) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] y;\n"
      "  always_comb y = 42;\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 42u);
}

TEST(SimCh9b, AlwaysCombZeroAssignTime0) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] y;\n"
      "  always_comb y = 0;\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0u);
}

TEST(SimCh9b, AlwaysCombOutputAfterRun) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  always_comb result = 100;\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* result = f.ctx.FindVariable("result");
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result->value.ToUint64(), 100u);
}

// §9.2.2.2.2: always_comb auto-executes at time zero, result is set.
TEST(SimClause09_02_02_02_02, AlwaysCombTimeZeroExecution) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] y;\n"
      "  always_comb y = 8'd77;\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 77u);
}

// §9.2.2.2.2: Case with variable reads in branches triggers on those inputs.
TEST(SimClause09_02_02_02_02, CaseBranchSensitivity) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] a, b, y;\n"
      "  always_comb\n"
      "    case (sel)\n"
      "      2'd0: y = a;\n"
      "      default: y = b;\n"
      "    endcase\n"
      "  initial begin\n"
      "    sel = 2'd0;\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "    #1 sel = 2'd1;\n"
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
  EXPECT_EQ(y->value.ToUint64(), 20u);
}

TEST(SimCh9d, AlwaysStarEquivAlwaysComb) {
  SimFixture f_star;
  auto* d_star = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always @* y = a ^ b;\n"
      "  initial begin\n"
      "    a = 8'hAA;\n"
      "    b = 8'h55;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f_star);
  ASSERT_NE(d_star, nullptr);

  Lowerer lowerer_star(f_star.ctx, f_star.arena, f_star.diag);
  lowerer_star.Lower(d_star);
  f_star.scheduler.Run();

  SimFixture f_comb;
  auto* d_comb = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always_comb y = a ^ b;\n"
      "  initial begin\n"
      "    a = 8'hAA;\n"
      "    b = 8'h55;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f_comb);
  ASSERT_NE(d_comb, nullptr);

  Lowerer lowerer_comb(f_comb.ctx, f_comb.arena, f_comb.diag);
  lowerer_comb.Lower(d_comb);
  f_comb.scheduler.Run();

  auto* y_star = f_star.ctx.FindVariable("y");
  auto* y_comb = f_comb.ctx.FindVariable("y");
  ASSERT_NE(y_star, nullptr);
  ASSERT_NE(y_comb, nullptr);
  EXPECT_EQ(y_star->value.ToUint64(), y_comb->value.ToUint64());
}

// §9.4.2: Event control in always_comb is an error.
TEST(ElabClause09_04_02, EventControlInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a;\n"
      "  always_comb @(posedge clk) a = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.4.3: Wait in always_comb is an error (timing control).
TEST(ElabClause09_04_03, WaitInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic ready, a;\n"
      "  always_comb wait (ready) a = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.6.1: Wait fork is a timing control, error in always_comb.
TEST(ElabClause09_06_01, WaitForkInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  always_comb begin\n"
      "    wait fork;\n"
      "    a = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
