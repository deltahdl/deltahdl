#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §20.10.1 — a severity task that appears at module-item level (outside any
// procedural code) parses as an elaboration severity system task.
TEST(ElabSeverityTaskParsing, FatalAtModuleLevelIsElabSystemTask) {
  auto r = Parse(
      "module m;\n"
      "  $fatal(1, \"abort\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->modules.empty());
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kElabSystemTask));
}

// §20.10.1 — when called from within a procedure (here, an initial block),
// the same severity task name becomes a run-time severity system task; it
// must not be parsed as an elaboration severity task module item.
TEST(ElabSeverityTaskParsing, FatalInsideInitialIsRunTime) {
  auto r = Parse(
      "module m;\n"
      "  initial $fatal(1, \"runtime\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->modules.empty());
  EXPECT_FALSE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kElabSystemTask));
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
}

// §20.10.1 — all four severity task names are recognized at module-item
// level as elaboration severity tasks.
TEST(ElabSeverityTaskParsing, AllFourSeverityNamesRecognized) {
  auto r = Parse(
      "module m;\n"
      "  $fatal;\n"
      "  $error;\n"
      "  $warning;\n"
      "  $info;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->modules.empty());
  EXPECT_EQ(CountItemsByKind(r.cu->modules[0]->items,
                             ModuleItemKind::kElabSystemTask),
            4u);
}

}  // namespace
