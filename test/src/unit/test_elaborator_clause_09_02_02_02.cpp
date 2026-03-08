#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §9.2.2.2: always_comb with delay control produces an error.
TEST(ElabClause09_02_02_02, TimingControlInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  always_comb #5 a = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.2.2.2: always_comb with event control produces an error.
TEST(ElabClause09_02_02_02, EventControlInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a;\n"
      "  always_comb @(posedge clk) a = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.2.2.2: always_comb with wait statement produces an error.
TEST(ElabClause09_02_02_02, WaitInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always_comb begin\n"
      "    wait (a) b = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.2.2.2: always_comb with fork-join produces an error.
TEST(ElabClause09_02_02_02, ForkJoinInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always_comb begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.2.2.2: always_comb with incomplete if warns about latched behavior.
TEST(ElabClause09_02_02_02, IncompleteIfWarnsLatch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic sel, a, y;\n"
      "  always_comb\n"
      "    if (sel) y = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// §9.2.2.2: always_comb with complete if/else does not warn.
TEST(ElabClause09_02_02_02, CompleteIfElseNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic sel, a, b, y;\n"
      "  always_comb\n"
      "    if (sel) y = a;\n"
      "    else y = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// §9.2.2.2: always_comb with case without default warns about latched behavior.
TEST(ElabClause09_02_02_02, CaseWithoutDefaultWarnsLatch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic y;\n"
      "  always_comb\n"
      "    case (sel)\n"
      "      2'b00: y = 0;\n"
      "      2'b01: y = 1;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// §9.2.2.2: always_comb with case + default does not warn.
TEST(ElabClause09_02_02_02, CaseWithDefaultNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic y;\n"
      "  always_comb\n"
      "    case (sel)\n"
      "      2'b00: y = 0;\n"
      "      2'b01: y = 1;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// §9.2.2.2: Multi-driver: same variable in two always_comb blocks.
TEST(ElabClause09_02_02_02, MultiDriverTwoAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b, y;\n"
      "  always_comb y = a;\n"
      "  always_comb y = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.2.2.2: Multi-driver: always_comb + continuous assignment on same variable.
TEST(ElabClause09_02_02_02, MultiDriverCombAndContAssignErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b, y;\n"
      "  assign y = a;\n"
      "  always_comb y = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.2.2.2: Different variables in separate always_comb blocks is fine.
TEST(ElabClause09_02_02_02, DifferentVarsInSeparateCombOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, x, y;\n"
      "  always_comb x = a;\n"
      "  always_comb y = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.2.2.2: always_comb elaborates to kAlwaysComb process kind.
TEST(ElabClause09_02_02_02, AlwaysCombElaboratesToCorrectKind) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always_comb a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  bool found = false;
  for (auto& p : design->top_modules[0]->processes) {
    if (p.kind == RtlirProcessKind::kAlwaysComb) found = true;
  }
  EXPECT_TRUE(found);
}

// §9.2.2.2: always_comb without timing control is fine (no zero-delay warning).
TEST(ElabClause09_02_02_02, AlwaysCombNoTimingControlNoZeroDelayWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always_comb a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(SimCh9, MultipleAlwaysCombBlocks) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, sum, diff;\n"
      "  initial begin\n"
      "    a = 8'd15;\n"
      "    b = 8'd5;\n"
      "  end\n"
      "  always_comb begin\n"
      "    sum = a + b;\n"
      "  end\n"
      "  always_comb begin\n"
      "    diff = a - b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* s = f.ctx.FindVariable("sum");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->value.ToUint64(), 20u);
  auto* d = f.ctx.FindVariable("diff");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->value.ToUint64(), 10u);
}

TEST(SimCh9, AlwaysCombMultipleOutputs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] doubled, incremented;\n"
      "  initial a = 8'd25;\n"
      "  always_comb begin\n"
      "    doubled = a << 1;\n"
      "    incremented = a + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* dbl = f.ctx.FindVariable("doubled");
  ASSERT_NE(dbl, nullptr);
  EXPECT_EQ(dbl->value.ToUint64(), 50u);
  auto* inc = f.ctx.FindVariable("incremented");
  ASSERT_NE(inc, nullptr);
  EXPECT_EQ(inc->value.ToUint64(), 26u);
}

TEST(SimCh9, AlwaysCombExplicitZeros) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    b = 8'd0;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = a | b;\n"
      "  end\n"
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

TEST(SimCh9b, MultipleAlwaysCombTime0) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  always_comb x = 8'h11;\n"
      "  always_comb y = 8'h22;\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 0x11u}, {"y", 0x22u}});
}

TEST(SimCh9b, AlwaysCombMultiBitAdd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a, b, y;\n"
      "  always_comb y = a + b;\n"
      "  initial begin\n"
      "    a = 16'h1234;\n"
      "    b = 16'h4321;\n"
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
  EXPECT_EQ(y->value.ToUint64(), 0x5555u);
}

TEST(SimCh9b, AlwaysCombBlockMultipleOutputs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, sum, diff;\n"
      "  always_comb begin\n"
      "    sum = a + b;\n"
      "    diff = a - b;\n"
      "  end\n"
      "  initial begin\n"
      "    a = 8'h20;\n"
      "    b = 8'h05;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* sum = f.ctx.FindVariable("sum");
  auto* diff = f.ctx.FindVariable("diff");
  ASSERT_NE(sum, nullptr);
  ASSERT_NE(diff, nullptr);
  EXPECT_EQ(sum->value.ToUint64(), 0x25u);
  EXPECT_EQ(diff->value.ToUint64(), 0x1Bu);
}

// §9.3.2: fork/join in always_comb is an error.
TEST(ElabClause09_03_02, ForkInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always_comb begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.4.1: Delay in always_comb is an error.
TEST(ElabClause09_04_01, DelayInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always_comb #5 a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AlwaysCombProcessInteraction, ProcessInteractionMultipleTimeSteps) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, doubled;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    #5 a = 8'd4;\n"
      "    #5 a = 8'd8;\n"
      "  end\n"
      "  always_comb doubled = a * 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("doubled");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

TEST(AlwaysCombStructFieldAccess, AlwaysCombStructFieldAccess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] hi;\n"
      "    logic [7:0] lo;\n"
      "  } pair_t;\n"
      "  pair_t p;\n"
      "  logic [7:0] result;\n"
      "  initial p = 16'hABCD;\n"
      "  always_comb begin\n"
      "    result = p.lo;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

TEST(AlwaysCombAndGate, AlwaysCombAndGate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always_comb y = a & b;\n"
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

TEST(AlwaysCombOrGate, AlwaysCombOrGate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always_comb y = a | b;\n"
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

TEST(AlwaysCombXorGate, AlwaysCombXorGate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always_comb y = a ^ b;\n"
      "  initial begin\n"
      "    a = 8'hAA;\n"
      "    b = 8'h55;\n"
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

TEST(AlwaysCombNotGate, AlwaysCombNotGate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, y;\n"
      "  always_comb y = ~a;\n"
      "  initial begin\n"
      "    a = 8'hA5;\n"
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

  EXPECT_EQ(y->value.ToUint64() & 0xFFu, 0x5Au);
}

TEST(AlwaysCombIfElse, AlwaysCombIfElseTrueBranch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b, y;\n"
      "  always_comb\n"
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

TEST(AlwaysCombIfElseFalseBranch, AlwaysCombIfElseFalseBranch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b, y;\n"
      "  always_comb\n"
      "    if (sel) y = a;\n"
      "    else y = b;\n"
      "  initial begin\n"
      "    a = 8'hAA;\n"
      "    b = 8'hBB;\n"
      "    sel = 0;\n"
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
  EXPECT_EQ(y->value.ToUint64(), 0xBBu);
}

// §9.2.2.2.2: always_comb elaborates to kAlwaysComb.
TEST(AlwaysCombIsAlwaysCombKind, AlwaysCombIsAlwaysCombKind) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, y;\n"
      "  always_comb y = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  EXPECT_EQ(proc.kind, RtlirProcessKind::kAlwaysComb);
}

TEST(AlwaysCombMuxIfElse, AlwaysCombMuxIfElse) {
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

TEST(AlwaysCombIfElse, AlwaysCombIfElseBranch) {
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

TEST(AlwaysCombCaseDecode, AlwaysCombCaseDecode) {
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

TEST(AlwaysCombZeroAssignTime, AlwaysCombZeroAssignTime0) {
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

}  // namespace
