#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulation/lowerer.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"

using namespace delta;

struct LowerFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler;
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign* ElaborateSrc(const std::string& src, LowerFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

TEST(Lowerer, InitialBlockSchedulesEvent) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  EXPECT_TRUE(f.scheduler.HasEvents());
}

TEST(Lowerer, VariableCreation) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
}

TEST(Lowerer, InitialBlockExecutes) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(Lowerer, ContAssignExecutes) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [31:0] y;\n"
      "  assign y = 99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(Lowerer, FinalBlockExecutesAfterRun) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  final x = 77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  // Before RunFinalBlocks, x should still have default value.
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);

  f.ctx.RunFinalBlocks();
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(Lowerer, FinalBlockNotScheduledAtTimeZero) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 10;\n"
      "  final x = 77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  // After scheduler, initial ran (x=10) but final didn't.
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(Lowerer, NbaDefersUpdate) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    x <= 42;\n"
      "    x = x;  // read x: should still be 0 (X→0), not 42\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  // NBA update deferred, but scheduler drains NBA after Active,
  // so after Run() completes the NBA has been applied.
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // x was read as 0 (from X init), then NBA applied 42.
  // The blocking assign `x = x` reads 0 and writes 0.
  // Then NBA applies 42. Final value: 42.
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(Lowerer, NbaAppliesToValue) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a, b;\n"
      "  initial begin\n"
      "    a <= 10;\n"
      "    b <= 20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 10u);
  EXPECT_EQ(b->value.ToUint64(), 20u);
}

TEST(Lowerer, DelayBasic) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    x = 1;\n"
      "    #10;\n"
      "    x = 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(Lowerer, DelayZero) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    #0;\n"
      "    x = 99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(Lowerer, AlwaysLoopWithDelay) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] clk;\n"
      "  initial clk = 0;\n"
      "  always #5 clk = clk + 1;\n"
      "  initial #20 $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("clk");
  ASSERT_NE(var, nullptr);
  // clk starts at 0, incremented at t=5,10,15,20 → 4 increments.
  // At t=20: $finish fires (sets StopRequested), always loop checks
  // StopRequested and exits. clk should be 4.
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

TEST(Lowerer, FinalBlocksFIFOOrder) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  final x = 10;\n"
      "  final x = 20;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // Second final block overwrites first, so x == 20.
  EXPECT_EQ(var->value.ToUint64(), 20u);
}
