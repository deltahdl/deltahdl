#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(OptionalSystemTaskParserParsing, Save) {
  auto r = Parse(
      "module m;\n"
      "  initial begin $save(\"s.sav\"); $restart(\"s.sav\"); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(OptionalSystemTaskExtendedParsing, IncsaveParse) {
  auto r = Parse(
      "module m;\n"
      "  initial $incsave(\"incremental.sav\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

TEST(OptionalSystemTaskExtendedParsing, IncsaveExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial $incsave(\"incremental.sav\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
}

}  // namespace
