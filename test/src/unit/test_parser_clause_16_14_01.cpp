// §16.14.1: Assert statement

#include "fixture_parser.h"

using namespace delta;

static ModuleItem* FindItemByKind(const std::vector<ModuleItem*>& items,
                                  ModuleItemKind kind) {
  for (auto* item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

namespace {

// =============================================================================
// §A.2.10 Production #1: concurrent_assertion_item
// concurrent_assertion_item ::=
//     [ block_identifier : ] concurrent_assertion_statement
//   | checker_instantiation
// =============================================================================
TEST(ParserA210, ConcurrentAssertionItem_AssertProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->loc.IsValid());
}

// =============================================================================
// §A.2.10 Production #3: assert_property_statement
// assert_property_statement ::= assert property ( property_spec ) action_block
// =============================================================================
TEST(ParserA210, AssertProperty_WithActionBlock) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b)\n"
      "    $display(\"pass\"); else $display(\"fail\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_pass_stmt, nullptr);
  EXPECT_NE(item->assert_fail_stmt, nullptr);
}

TEST(ParserA210, AssertProperty_PassOnly) {
  auto r = Parse(
      "module m;\n"
      "  assert property (a) $display(\"ok\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_pass_stmt, nullptr);
  EXPECT_EQ(item->assert_fail_stmt, nullptr);
}

TEST(ParserA210, AssertProperty_FailOnly) {
  auto r = Parse(
      "module m;\n"
      "  assert property (a |-> b) else $error(\"fail\");\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->assert_pass_stmt, nullptr);
  EXPECT_NE(item->assert_fail_stmt, nullptr);
}

struct ParseResult16c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult16c Parse(const std::string& src) {
  ParseResult16c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

using VerifyParseTest = ProgramTestParse;

// =============================================================================
// Section 16.5.1 -- Concurrent assertion statements: assert property
// =============================================================================
// Assert property with a simple property expression (no clock, no implication).
TEST(ParserSection16, Sec16_5_1_AssertPropertySimple) {
  auto r = Parse(
      "module m;\n"
      "  assert property (a && b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_expr, nullptr);
}

}  // namespace
