#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "preprocessor/preprocessor.h"
#include "simulator/variable.h"

using namespace delta;

TEST(CommentSim, CommentLineCommentStripped) {
  auto result = RunAndGet(
      "module t; // module declaration\n"
      "  logic [7:0] result; // variable\n"
      "  initial result = 8'd77; // assignment\n"
      "endmodule // end\n",
      "result");
  EXPECT_EQ(result, 77u);
}

TEST(CommentSim, CommentBlockCommentStripped) {
  auto result = RunAndGet(
      "module /* module */ t /* name */;\n"
      "  logic /* type */ [7:0] /* width */ result /* var */;\n"
      "  initial /* process */ result = /* assign */ 8'd55 /* val */;\n"
      "endmodule /* end */\n",
      "result");
  EXPECT_EQ(result, 55u);
}

TEST(CommentSim, CommentBlockNotNested) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial /* outer /* inner */ result = 8'd33;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 33u);
}

TEST(CommentSim, CommentLineInsideBlockNoEffect) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  /* // this is not a line comment\n"
      "     still inside block comment */\n"
      "  initial result = 8'd99;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 99u);
}

TEST(CommentSim, CommentBlockInsideLineNoEffect) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  // /* this does not start a block comment\n"
      "  initial result = 8'd22;\n"
      "  // */ this does not end a block comment\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 22u);
}

TEST(CommentSim, CommentMixedInExpression) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] a, b, result;\n"
      "  initial begin\n"
      "    a = 8'd10; // ten\n"
      "    b = /* twenty */ 8'd20;\n"
      "    result = a /* plus */ + /* b */ b; // sum\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 30u);
}

TEST(CommentSim, CommentMultilineBlockSpan) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    /* This block comment\n"
      "       spans multiple\n"
      "       lines */\n"
      "    result = 8'd11;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 11u);
}

TEST(CommentSim, CommentBlockAsSeparator) {
  auto result = RunAndGet(
      "module/**/t;logic/**/[7:0]/**/result;initial/**/result=8'd71;"
      "endmodule",
      "result");
  EXPECT_EQ(result, 71u);
}

TEST(CommentSim, CommentLineCommentAtEofNoNewline) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd44;\n"
      "endmodule // no newline at end",
      "result");
  EXPECT_EQ(result, 44u);
}

TEST(CommentSim, CommentEmptyBlockComment) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = /**/ 8'd88;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 88u);
}

TEST(CommentSim, CommentLineFollowedByBlock) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  // line comment\n"
      "  /* block comment */\n"
      "  initial result = 8'd66;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 66u);
}
