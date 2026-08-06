#include "fixture_parser.h"

using namespace delta;

namespace {

// Locate the single assert property item parsed from a one-module source.
ModuleItem* FindAssertItem(const ParseResult& r) {
  if (!r.cu || r.cu->modules.size() != 1u) return nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAssertProperty) return item;
  }
  return nullptr;
}

// §16.14.1: an assert statement carries a property and, per para 1, an
// action_block whose pass statements run on success and fail statements run on
// failure. The full form supplies both branches: a pass statement and an else
// (fail) statement.
TEST(AssertionSemanticsParsing, AssertActionBlocks) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b)\n"
      "    $display(\"PASS\");\n"
      "  else\n"
      "    $error(\"FAIL\");\n"
      "endmodule\n");
  auto* item = FindAssertItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_expr, nullptr);
  // Both action_block branches are captured from the source.
  EXPECT_NE(item->assert_pass_stmt, nullptr);
  EXPECT_NE(item->assert_fail_stmt, nullptr);
}

// §16.14.1 para 2: the else clause may be omitted, in which case only the pass
// statement is present and there is no fail action — this is the input form on
// which the tool's default-$error-on-failure behavior keys.
TEST(AssertionSemanticsParsing, AssertElseClauseOmitted) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b)\n"
      "    $display(\"PASS\");\n"
      "endmodule\n");
  auto* item = FindAssertItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_pass_stmt, nullptr);
  // No else clause: the fail branch is absent, so the default $error applies.
  EXPECT_EQ(item->assert_fail_stmt, nullptr);
}

// §16.14.1 para 1: a simple boolean concurrent property (no temporal operator)
// is another admitted property input form for the assert statement. It takes
// the parser's simple-concurrent path, which synthesizes the assert body; the
// pass and fail action_block branches are captured onto that body.
TEST(AssertionSemanticsParsing, SimpleConcurrentPropertyCapturesActionBlock) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a)\n"
      "    $display(\"PASS\");\n"
      "  else\n"
      "    $error(\"FAIL\");\n"
      "endmodule\n");
  auto* item = FindAssertItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_expr, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_NE(item->body->assert_pass_stmt, nullptr);
  EXPECT_NE(item->body->assert_fail_stmt, nullptr);
}

// §16.14.1 para 2: when no action is needed a null statement (a bare ;) is
// specified, so neither action_block branch is present.
TEST(AssertionSemanticsParsing, AssertNullStatementActionBlock) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  auto* item = FindAssertItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_expr, nullptr);
  EXPECT_EQ(item->assert_pass_stmt, nullptr);
  EXPECT_EQ(item->assert_fail_stmt, nullptr);
}

}  // namespace
