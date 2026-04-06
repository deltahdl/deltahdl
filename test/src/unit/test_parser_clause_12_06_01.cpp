#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(CaseMatchesItemParsing, CasePatternItemWithGuard) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) matches\n"
      "      .n &&& (n > 0): y = n;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CaseMatchesItemParsing, CasePatternTaggedWithGuard) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(instr) matches\n"
      "      tagged Add '{.r1, .r2, .rd} &&& (rd != 0): x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CaseMatchesItemParsing, CaseMatchesParse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(v) matches\n"
      "      5: y = 8'd10;\n"
      "      default: y = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
}

TEST(CaseMatchesItemParsing, CaseMatchesDefault) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) matches\n"
      "      5: y = 1;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_EQ(stmt->case_items.size(), 2u);
  EXPECT_TRUE(stmt->case_items[1].is_default);
}

TEST(CaseMatchesItemParsing, CaseMatchesMultipleItems) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) matches\n"
      "      1: y = 10;\n"
      "      2: y = 20;\n"
      "      3: y = 30;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->case_items.size(), 4u);
}


TEST(CaseMatchesItemParsing, CaseMatchesPattern) {
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

TEST(CaseMatchesItemParsing, CaseMatchesCommaSeparatedPatterns) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) matches\n"
      "      1, 2, 3: y = 10;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_GE(stmt->case_items.size(), 1u);
  EXPECT_EQ(stmt->case_items[0].patterns.size(), 3u);
}

}  // namespace
