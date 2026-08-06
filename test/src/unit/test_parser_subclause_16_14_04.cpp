#include "fixture_parser.h"

using namespace delta;

namespace {

// §16.14.4: the restrict statement has the form
// `restrict property ( property_spec ) ;` and carries no action block, so it
// parses to a restrict-property item whose pass and fail statements are absent.
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
      // §16.14.4: there is no action block — neither a pass nor a fail
      // statement.
      EXPECT_EQ(item->assert_pass_stmt, nullptr);
      EXPECT_EQ(item->assert_fail_stmt, nullptr);
    }
  }
  EXPECT_TRUE(found);
  EXPECT_FALSE(r.has_errors);
}

// §16.14.4: because the statement has no action block, a pass statement placed
// after the property_spec is not accepted — the form ends at the semicolon.
TEST(RestrictStatementParsing, RejectsActionBlock) {
  EXPECT_FALSE(ParseOk(
      "module m;\n"
      "  logic clk;\n"
      "  logic ctr;\n"
      "  restrict property (@(posedge clk) ctr == '0) $display(\"x\");\n"
      "endmodule\n"));
}

// §16.14.4: the statement has no action block at all, so neither does it accept
// a fail action — an else clause after the property_spec is rejected, unlike an
// assert or assume statement.
TEST(RestrictStatementParsing, RejectsElseClause) {
  EXPECT_FALSE(ParseOk(
      "module m;\n"
      "  logic clk;\n"
      "  logic ctr;\n"
      "  restrict property (@(posedge clk) ctr == '0) else $error(\"x\");\n"
      "endmodule\n"));
}

}  // namespace
