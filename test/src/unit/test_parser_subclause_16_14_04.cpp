#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(RestrictStatementParsing, FormWithoutActionBlock) {
  auto r = Parse(
      "module m;\n"
      "  logic clk;\n"
      "  logic ctr;\n"
      "  restrict property (@(posedge clk) ctr == '0);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kRestrictProperty) {
      found = true;
      EXPECT_NE(item->assert_expr, nullptr);
      EXPECT_EQ(item->assert_pass_stmt, nullptr);
      EXPECT_EQ(item->assert_fail_stmt, nullptr);
    }
  }
  EXPECT_TRUE(found);
  EXPECT_FALSE(r.has_errors);
}

TEST(RestrictStatementParsing, RejectsActionBlock) {
  auto r = Parse(
      "module m;\n"
      "  logic clk;\n"
      "  logic ctr;\n"
      "  restrict property (@(posedge clk) ctr == '0) $display(\"x\");\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got system identifier", 4,
                            "16.14.4"));
}

TEST(RestrictStatementParsing, RejectsElseClause) {
  auto r = Parse(
      "module m;\n"
      "  logic clk;\n"
      "  logic ctr;\n"
      "  restrict property (@(posedge clk) ctr == '0) else $error(\"x\");\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got 'else'", 4, "16.14.4"));
}

}  // namespace
