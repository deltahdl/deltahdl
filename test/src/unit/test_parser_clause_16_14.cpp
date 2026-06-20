#include "fixture_parser.h"

using namespace delta;

namespace {

// Locate the first module item of a given kind in a parsed compilation unit.
const ModuleItem* FindItem(const ParseResult& r, ModuleItemKind kind) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

// §16.14 Syntax 16-18: concurrent_assertion_statement has five alternatives.
// Each of the next five tests observes the parser selecting the matching
// alternative and producing the corresponding module-item kind.

// assert_property_statement ::= assert property ( property_spec ) action_block
TEST(ConcurrentAssertionStatementSyntax, AssertPropertyStatement) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  const ModuleItem* item = FindItem(r, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_expr, nullptr);
}

// assume_property_statement ::= assume property ( property_spec ) action_block
TEST(ConcurrentAssertionStatementSyntax, AssumePropertyStatement) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  const ModuleItem* item = FindItem(r, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_expr, nullptr);
}

// cover_property_statement ::= cover property ( property_spec )
// statement_or_null
TEST(ConcurrentAssertionStatementSyntax, CoverPropertyStatement) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  const ModuleItem* item = FindItem(r, ModuleItemKind::kCoverProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_expr, nullptr);
}

// cover_sequence_statement ::=
//   cover sequence ( [clocking_event] [disable iff (...)] sequence_expr )
//   statement_or_null
TEST(ConcurrentAssertionStatementSyntax, CoverSequenceStatement) {
  auto r = Parse(
      "module m;\n"
      "  cover sequence (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  const ModuleItem* item = FindItem(r, ModuleItemKind::kCoverSequence);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_expr, nullptr);
}

// restrict_property_statement ::= restrict property ( property_spec ) ;
TEST(ConcurrentAssertionStatementSyntax, RestrictPropertyStatement) {
  auto r = Parse(
      "module m;\n"
      "  restrict property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  const ModuleItem* item = FindItem(r, ModuleItemKind::kRestrictProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_expr, nullptr);
}

// §16.14: "A concurrent assertion statement can be referenced by its optional
// name." Syntax 16-18 spells this as the leading block_identifier of a
// concurrent_assertion_item. The parser captures the label into the item name.
TEST(ConcurrentAssertionItemNaming, BlockIdentifierNamesAssert) {
  auto r = Parse(
      "module m;\n"
      "  a1: assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  const ModuleItem* item = FindItem(r, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "a1");
}

// restrict_property_statement is one of the concurrent_assertion_statement
// alternatives, so a concurrent_assertion_item may name it too. This covers the
// case the label dispatch previously dropped.
TEST(ConcurrentAssertionItemNaming, BlockIdentifierNamesRestrict) {
  auto r = Parse(
      "module m;\n"
      "  r1: restrict property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  const ModuleItem* item = FindItem(r, ModuleItemKind::kRestrictProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "r1");
}

// §A.6.10 procedural_assertion_statement ::= concurrent_assertion_statement
// | ... — a concurrent assertion statement may appear directly in procedural
// code. The parser flags such a statement as procedural-concurrent rather than
// treating it as an immediate assertion.
TEST(ProceduralConcurrentAssertion, ConcurrentAssertInAlways) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk) assert property (a |-> b);\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  const ModuleItem* always = FindItem(r, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(always, nullptr);
  ASSERT_NE(always->body, nullptr);
  EXPECT_TRUE(always->body->is_procedural_concurrent);
}

// §16.14: a concurrent assertion statement may be specified in a module, an
// interface, or a program (among other contexts). The parser accepts the
// construct in each of these design-element contexts.
TEST(ConcurrentAssertionPlacement, AcceptedInModuleInterfaceProgram) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a |-> b);\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("interface i;\n"
              "  assert property (@(posedge clk) a |-> b);\n"
              "endinterface\n"));
  EXPECT_TRUE(
      ParseOk("program p;\n"
              "  assert property (@(posedge clk) a |-> b);\n"
              "endprogram\n"));
}

// §16.14: "A property on its own is never evaluated ... It shall be used within
// an assertion statement." A property declaration alone parses as a declaration
// and does not by itself produce a concurrent assertion item; evaluation only
// occurs once the property is named inside an assertion statement.
TEST(ConcurrentAssertionPlacement, PropertyDeclarationIsNotAnAssertion) {
  auto r = Parse(
      "module m;\n"
      "  property pr;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "  assert property (pr);\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  EXPECT_NE(FindItem(r, ModuleItemKind::kPropertyDecl), nullptr);
  EXPECT_NE(FindItem(r, ModuleItemKind::kAssertProperty), nullptr);
}

// Syntax 16-18: the action_block of an assert_property_statement permits the
// else-only form ([statement] else statement_or_null). The parser records a
// fail branch and leaves the pass branch empty.
TEST(ConcurrentAssertionStatementSyntax, AssertWithElseOnlyActionBlock) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b)\n"
      "    else $error(\"fail\");\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  const ModuleItem* item = FindItem(r, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->assert_pass_stmt, nullptr);
  EXPECT_NE(item->assert_fail_stmt, nullptr);
}

// The action_block also permits a pass statement followed by an else fail
// statement; the parser records both branches.
TEST(ConcurrentAssertionStatementSyntax, AssumeWithPassAndElseActionBlock) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) a |-> b)\n"
      "    $info(\"pass\");\n"
      "  else $error(\"fail\");\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  const ModuleItem* item = FindItem(r, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_pass_stmt, nullptr);
  EXPECT_NE(item->assert_fail_stmt, nullptr);
}

// cover_sequence_statement allows an optional disable iff (expression_or_dist)
// ahead of the sequence_expr. The parser accepts the guarded form and still
// classifies the item as a cover-sequence.
TEST(ConcurrentAssertionStatementSyntax, CoverSequenceWithDisableIff) {
  auto r = Parse(
      "module m;\n"
      "  cover sequence (@(posedge clk) disable iff (rst) a ##1 b);\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  EXPECT_NE(FindItem(r, ModuleItemKind::kCoverSequence), nullptr);
}

// restrict_property_statement terminates with a semicolon and carries no
// action_block. Supplying an else action block is a parse error.
TEST(ConcurrentAssertionStatementSyntax, RestrictRejectsActionBlock) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  restrict property (@(posedge clk) a |-> b)\n"
              "    else $error(\"fail\");\n"
              "endmodule\n"));
}

// The optional block_identifier of a concurrent_assertion_item names a cover
// statement just as it names assert and restrict.
TEST(ConcurrentAssertionItemNaming, BlockIdentifierNamesCover) {
  auto r = Parse(
      "module m;\n"
      "  c1: cover property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  const ModuleItem* item = FindItem(r, ModuleItemKind::kCoverProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "c1");
}

// §16.14 also lists generate blocks and checkers among the contexts where a
// concurrent assertion statement may appear. The parser accepts the construct
// in both.
TEST(ConcurrentAssertionPlacement, AcceptedInGenerateBlockAndChecker) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  generate\n"
              "    if (1) begin\n"
              "      assert property (@(posedge clk) a |-> b);\n"
              "    end\n"
              "  endgenerate\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  checker c;\n"
              "    assert property (@(posedge clk) a |-> b);\n"
              "  endchecker\n"
              "endmodule\n"));
}

}  // namespace
