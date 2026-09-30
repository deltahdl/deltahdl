#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

TEST(AssertionSemanticsParsing, FirstMatch) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) first_match(a ##[1:4] b));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// §16.9.8 (Syntax 16-10): the first_match production admits a trailing list of
// sequence_match_items placed inside the same parentheses that enclose the
// operand, i.e. first_match(seq {, sequence_match_item}). Here the local
// variable assignment x = e is attached to the operand.
TEST(AssertionSemanticsParsing, FirstMatchWithSequenceMatchItem) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) first_match(a ##[1:4] b, x = e));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// §16.9.8: attaching the match items to the operand is equivalent to enclosing
// the operand and its match items in their own parentheses, so
// first_match(seq, x = e) and first_match((seq, x = e)) both parse.
TEST(AssertionSemanticsParsing, FirstMatchMatchItemGroupingEquivalence) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) first_match((a ##[1:4] b, x = e)));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// §16.9.8 (Syntax 16-10): the sequence_match_item part of the production is a
// repeated list, so more than one match item can be attached to the operand.
TEST(AssertionSemanticsParsing, FirstMatchWithMultipleSequenceMatchItems) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) first_match(a ##[1:4] b, x = e, y = f));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// §16.9.8 with §16.12.7: `first_match(seq)` is a sequence_expr, so it stands
// as the antecedent of an implication, read into the implication's sequence
// with its first_match mark rather than leaving the spec unread.
TEST(AssertionSemanticsParsing, FirstMatchAsTheAntecedentOfAnImplication) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, a, b, c;\n"
      "  assert property (@(posedge clk) first_match(a ##[1:3] b) |-> c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* item = r.cu->modules[0]->items.back();
  ASSERT_EQ(item->kind, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item->body, nullptr);
  const PropertyExprNode* tree = item->body->assert_property;
  ASSERT_NE(tree, nullptr);
  EXPECT_EQ(tree->kind, PropertyExprNode::Kind::kImplication);
  ASSERT_NE(tree->sequence, nullptr);
  EXPECT_TRUE(tree->sequence->seq_linear.first_match);
  EXPECT_EQ(tree->sequence->seq_linear.operands.size(), 2u);
}

}  // namespace
