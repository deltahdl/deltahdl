// §13.5: Subroutine calls and argument passing

#include "fixture_parser.h"

using namespace delta;

namespace {

// tf_call without parentheses (task call — footnote 42)
TEST(ParserA609, TfCallNoParens) {
  auto r = Parse(
      "module m;\n"
      "  task foo; endtask\n"
      "  initial foo;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

}  // namespace
