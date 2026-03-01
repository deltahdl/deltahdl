// §12.6.1: Pattern matching in case statements

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.6.7.1 Patterns — Parsing tests
// =============================================================================
// ---------------------------------------------------------------------------
// pattern ::= constant_expression
// ---------------------------------------------------------------------------
// §12.6: pattern as constant expression in case-matches
TEST(ParserA60701, PatternConstantExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) matches\n"
      "      5: y = 8'd10;\n"
      "      10: y = 8'd20;\n"
      "      default: y = 8'd30;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// pattern ::= tagged member_identifier [ pattern ]
// ---------------------------------------------------------------------------
// §12.6: tagged union pattern
TEST(ParserA60701, PatternTagged) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(v) matches\n"
      "      tagged Valid .n: x = n;\n"
      "      tagged Invalid: x = 0;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §12.6: tagged pattern with nested assignment pattern
TEST(ParserA60701, PatternTaggedWithAssignmentPattern) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(instr) matches\n"
      "      tagged Add '{.r1, .r2, .rd}: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §12.6: tagged pattern with parenthesized nested tagged pattern
TEST(ParserA60701, PatternTaggedNested) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(instr) matches\n"
      "      tagged Jmp (tagged JmpU .a): pc = a;\n"
      "      default: pc = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §12.6: tagged void member (no nested pattern)
TEST(ParserA60701, PatternTaggedVoidMember) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(v) matches\n"
      "      tagged Invalid: x = 0;\n"
      "      default: x = 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
}

// §10.9: assignment pattern with dot-identifier pattern bindings
TEST(ParserA60701, PatternAssignmentWithDotBindings) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(s) matches\n"
      "      '{.a, .b}: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// case_pattern_item ::= pattern [ &&& expression ] : statement_or_null
// ---------------------------------------------------------------------------
// §12.6.1: case pattern item with &&& guard
TEST(ParserA60701, CasePatternItemWithGuard) {
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

// §12.6.1: case-matches with tagged pattern and &&& guard
TEST(ParserA60701, CasePatternTaggedWithGuard) {
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

// ---------------------------------------------------------------------------
// case_statement ::=
//   [ unique_priority ] case_keyword ( case_expression ) matches
//     case_pattern_item { case_pattern_item } endcase
// ---------------------------------------------------------------------------
// §12.6.1: case-matches variant
TEST(ParserA607, CaseMatchesParse) {
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

// §12.6.1: case-matches with default item
TEST(ParserA60701, CaseMatchesDefault) {
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

// §12.6.1: case-matches with multiple pattern items
TEST(ParserA60701, CaseMatchesMultipleItems) {
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

}  // namespace
