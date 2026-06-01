#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

TEST(WhiteSpaceSim, WhitespaceSameResultMinimal) {
  auto result = RunAndGet(
      "module t;logic [7:0] result;initial result=8'd55;endmodule", "result");
  EXPECT_EQ(result, 55u);
}

TEST(WhiteSpaceSim, WhitespaceSameResultExcessive) {
  auto result = RunAndGet(
      "  \t\n  module   \t  t  \n  ;  \n"
      "  logic   [  7  :  0  ]   result  ;  \n"
      "  initial   result   =   8'd77   ;  \n"
      "  endmodule  \n\n  ",
      "result");
  EXPECT_EQ(result, 77u);
}

TEST(WhiteSpaceSim, WhitespaceMixedInExpression) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] a, b, c, result;\n"
      "  initial begin\n"
      "    a = 8'd3;\n"
      "    b = 8'd4;\n"
      "    c = 8'd5;\n"
      "    result =  a \t + \n b  \f +  c ;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 12u);
}

TEST(WhiteSpaceSim, WhitespaceStringLiteralPreserved) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [63:0] s;\n"
      "  initial s = \"a b\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);

  uint64_t val = var->value.ToUint64();
  EXPECT_EQ(val & 0xFF, 0x62u);
  EXPECT_EQ((val >> 8) & 0xFF, 0x20u);
  EXPECT_EQ((val >> 16) & 0xFF, 0x61u);
}

TEST(WhiteSpaceSim, WhitespaceStringLiteralTabPreserved) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [63:0] s;\n"
      "  initial s = \"a\tb\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);

  uint64_t val = var->value.ToUint64();
  EXPECT_EQ(val & 0xFF, 0x62u);
  EXPECT_EQ((val >> 8) & 0xFF, 0x09u);
  EXPECT_EQ((val >> 16) & 0xFF, 0x61u);
}

TEST(WhiteSpaceSim, WhitespaceSeparatesKeywords) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial begin result = 8'd1; end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 1u);
}

TEST(WhiteSpaceSim, WhitespaceAlwaysCombWithFormfeed) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] a, result;\n"
      "  initial a = 8'd7;\n"
      "  always_comb begin\f"
      "    result = a + 8'd3;\f"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 10u);
}

TEST(WhiteSpaceSim, WhitespaceInConcatenation) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 4'hA;\n"
      "    b = 4'h5;\n"
      "    result = { \t a \n , \f b \t };\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 0xA5u);
}

TEST(WhiteSpaceSim, WhitespaceAroundTernary) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 1'b1 \t ? \n 8'd100 \f : \t 8'd200;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 100u);
}

TEST(WhiteSpaceSim, WhitespaceVerticalTabInSource) {
  auto result = RunAndGet(
      "module t;\v"
      "logic [7:0] result;\v"
      "initial result = 8'd11;\v"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 11u);
}

TEST(WhiteSpaceSim, WhitespaceCrlfLineEndings) {
  auto result = RunAndGet(
      "module t;\r\n"
      "  logic [7:0] result;\r\n"
      "  initial result = 8'd22;\r\n"
      "endmodule\r\n",
      "result");
  EXPECT_EQ(result, 22u);
}

TEST(WhiteSpaceSim, WhitespaceMultipleStatements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd10; \t \n b = 8'd20; \f\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 10u}, {"b", 20u}});
}
