// §9.4.5

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabClause09_04_05, BlockingIntraDelayElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial a = #5 b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabClause09_04_05, NonblockingIntraDelayElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial a <= #5 b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabClause09_04_05, BlockingIntraEventElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  initial a = @(posedge clk) b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabClause09_04_05, NonblockingIntraEventElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, q, d;\n"
      "  initial q <= @(posedge clk) d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabClause09_04_05, RepeatEventBlockingElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  initial a = repeat(3) @(posedge clk) b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabClause09_04_05, RepeatEventNonblockingElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, q, d;\n"
      "  initial q <= repeat(5) @(posedge clk) d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BlockingIntraAssignDelay, BlockingIntraAssignDelay) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    b = 8'd42;\n"
      "    a = #5 b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 42u);
}

TEST(BlockingIntraAssignDelay, DelayBlocksSubsequentStatements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    b = 8'd10;\n"
      "    a = #5 b;\n"
      "    c = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 10u);
  EXPECT_EQ(c->value.ToUint64(), 99u);
}

TEST(BlockingIntraAssignDelayRHSCapture, BlockingIntraAssignDelayCapturesRHS) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    b = 8'd10;\n"
      "    a = #5 b;\n"
      "  end\n"
      "  initial begin\n"
      "    #2 b = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);

  EXPECT_EQ(a->value.ToUint64(), 10u);
}

TEST(NbaIntraAssignDelay, NbaIntraAssignDelay) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    b = 8'd42;\n"
      "    a <= #5 b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(NbaIntraAssignDelay, NbaIntraAssignDelayNonBlocking) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    b = 8'd10;\n"
      "    a <= #5 b;\n"
      "    c = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(c, nullptr);

  EXPECT_EQ(a->value.ToUint64(), 10u);
  EXPECT_EQ(c->value.ToUint64(), 99u);
}

TEST(NbaIntraAssignDelayCapturesRHS, NbaIntraAssignDelayCapturesRHS) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    b = 8'd10;\n"
      "    a <= #5 b;\n"
      "  end\n"
      "  initial begin\n"
      "    #2 b = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);

  EXPECT_EQ(a->value.ToUint64(), 10u);
}

}  // namespace
