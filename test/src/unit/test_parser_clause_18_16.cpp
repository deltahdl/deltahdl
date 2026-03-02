// §18.16: Random weighted case—randcase

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// randcase_statement ::= randcase randcase_item { randcase_item } endcase
// randcase_item ::= expression : statement_or_null
// ---------------------------------------------------------------------------
// §18.16: randcase statement
TEST(ParserA607, RandcaseParse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randcase\n"
      "      50: x = 1;\n"
      "      30: x = 2;\n"
      "      20: x = 3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandcase);
  EXPECT_EQ(stmt->randcase_items.size(), 3u);
}

// §18.16: randcase with block bodies
TEST(ParserA607, RandcaseWithBlocks) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randcase\n"
      "      50: begin x = 1; y = 2; end\n"
      "      50: begin x = 3; y = 4; end\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandcase);
  EXPECT_EQ(stmt->randcase_items.size(), 2u);
}

// §18.16: randcase_statement
TEST(ParserA604, StmtItemRandcaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1: a = 1;\n"
      "      1: a = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandcase);
}

using CheckerParseTest = ProgramTestParse;

// --- Randcase statement (§18.16) ---
TEST(ParserSection18, RandcaseStmt) {
  auto r = Parse(
      "module top;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1 : $display(\"one\");\n"
      "      2 : $display(\"two\");\n"
      "      3 : $display(\"three\");\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

}  // namespace
