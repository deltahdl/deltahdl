#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

TEST(LexicalTokenSim, LexicalTokenFreeFormatIdenticalResult) {
  auto compact = RunAndGet(
      "module t;logic [7:0] result;initial result=8'd42;endmodule", "result");
  auto spread = RunAndGet(
      "module\nt\n;\nlogic\n[7:0]\nresult\n;\ninitial\nresult\n=\n8'd42\n;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(compact, spread);
  EXPECT_EQ(compact, 42u);
}

TEST(LexicalTokenSim, LexicalTokenCommentsDoNotAffectSimulation) {
  auto result = RunAndGet(
      "module /* block */ t; // line\n"
      "  logic [7:0] /* type */ result /* name */;\n"
      "  initial /* proc */ begin\n"
      "    result /* lhs */ = /* rhs */ 8'd88 /* val */;\n"
      "  end // done\n"
      "endmodule /* eof */\n",
      "result");
  EXPECT_EQ(result, 88u);
}

TEST(LexicalTokenSim, LexicalTokenAllCategoriesInSimulation) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] a, b, result;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "    result = (a > b) ? a : b;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 20u);
}

TEST(LexicalTokenSim, LexicalTokenMultilineExpression) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial\n"
      "    result\n"
      "      =\n"
      "        8'd3\n"
      "          +\n"
      "        8'd7\n"
      "      ;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 10u);
}

TEST(LexicalTokenSim, LexicalTokenMultipleStatementsOneLine) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin a = 8'd1; b = 8'd2; c = a + b; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 3u);
}

TEST(LexicalTokenSim, LexicalTokenBlockCommentAsSeparator) {
  auto result = RunAndGet(
      "module/**/t;logic/**/[7:0]/**/result;initial/**/result=8'd66;"
      "endmodule",
      "result");
  EXPECT_EQ(result, 66u);
}

TEST(LexicalTokenSim, LexicalTokenLineCommentTerminatesAtNewline) {
  auto result = RunAndGet(
      "module t; // this is a comment\n"
      "  logic [7:0] result; // another comment\n"
      "  initial result = 8'd44; // value\n"
      "endmodule // end\n",
      "result");
  EXPECT_EQ(result, 44u);
}

TEST(LexicalTokenSim, LexicalTokenFreeFormatAlwaysComb) {
  auto result = RunAndGet(
      "module t; logic [7:0] a, result;\n"
      "initial a = 8'd5;\n"
      "always_comb result\n=\na\n+\n8'd10\n;\nendmodule\n",
      "result");
  EXPECT_EQ(result, 15u);
}

TEST(LexicalTokenSim, LexicalTokenExcessiveWhitespace) {
  auto result = RunAndGet(
      "  module   t  ;   logic   [7:0]   result  ;   initial   result  =  "
      "8'd33  ;   endmodule  ",
      "result");
  EXPECT_EQ(result, 33u);
}

TEST(LexicalTokenSim, LexicalTokenTabsAsSeparators) {
  auto result = RunAndGet(
      "module\tt;\tlogic\t[7:0]\tresult;\tinitial\tresult\t=\t8'd77;\t"
      "endmodule",
      "result");
  EXPECT_EQ(result, 77u);
}

TEST(LexicalTokenSim, LexicalTokenCrlfLineEndings) {
  auto result = RunAndGet(
      "module t;\r\n"
      "  logic [7:0] result;\r\n"
      "  initial result = 8'd55;\r\n"
      "endmodule\r\n",
      "result");
  EXPECT_EQ(result, 55u);
}
