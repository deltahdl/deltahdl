#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA60701, AssignmentPatternExprList) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = '{1, 2, 3};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(ParserA60701, AssignmentPatternStructKeys) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = '{x: 1, y: 2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA60701, AssignmentPatternReplication) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = '{4{0}};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA60701, AssignmentPatternDefault) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = '{default: 0};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA60701, AssignmentPatternWithType) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct { int x; int y; } point_t;\n"
      "  initial begin\n"
      "    point_t p = point_t'{x: 1, y: 2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA60701, AssignmentPatternIntegerAtomType) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int a = int'{1};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA60701, AssignmentPatternNetLvalue) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign '{a, b} = c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA60701, AssignmentPatternVariableLvalue) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    '{a, b} = '{1, 2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA60701, CaseMatchesPattern) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (x) matches\n"
      "      .a: $display(\"a\");\n"
      "      .b: $display(\"b\");\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA60701, CondPatternMatches) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (x matches 42) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}
