#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

// §16.13.1: `@(posedge clk1)` after ##1 in a sequence changes the clock the
// operands from there on are evaluated on, which the linear body records
// beside its operands, the operand before the change carrying none, the
// leading clock's; a sequence naming a clock of its own is carried as the
// one operand of the assertion's tree.
TEST(MulticlockParsing, AClockAfterADelayIsRecordedOnTheOperandsAfterIt) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk0) sig0 ##1 @(posedge clk1) sig1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  const PropertyExprNode* root = item->body->assert_property;
  ASSERT_NE(root, nullptr);
  EXPECT_EQ(root->kind, PropertyExprNode::Kind::kSequence);
  ASSERT_NE(root->sequence, nullptr);
  const SeqLinearBody& body = root->sequence->seq_linear;
  ASSERT_EQ(body.operands.size(), 2u);
  ASSERT_EQ(body.clocks.size(), 2u);
  EXPECT_TRUE(body.clocks[0].empty());
  ASSERT_EQ(body.clocks[1].size(), 1u);
  EXPECT_EQ(body.clocks[1][0].edge, Edge::kPosedge);
  ASSERT_NE(body.clocks[1][0].signal, nullptr);
  EXPECT_EQ(body.clocks[1][0].signal->text, "clk1");
}

// §16.13.1: a sequence naming no clock of its own records none, and stays
// the sequential property the assertion carries as one.
TEST(MulticlockParsing, ASequenceOnOneClockRecordsNoClocks) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk0) sig0 ##1 sig1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->assert_property, nullptr);
  ASSERT_NE(item->body->assert_sequence, nullptr);
  EXPECT_TRUE(item->body->assert_sequence->seq_linear.clocks.empty());
}

// The antecedent's linear body of the one assertion of `src`.
const SeqLinearBody* AntecedentBody(ParseResult& r) {
  auto* item = FindItemByKind(r, ModuleItemKind::kAssertProperty);
  if (item == nullptr || item->body == nullptr) return nullptr;
  const PropertyExprNode* root = item->body->assert_property;
  if (root == nullptr || root->sequence == nullptr) return nullptr;
  return &root->sequence->seq_linear;
}

// §16.13.3: the clock in force at the end of a chain flows out of it, so
// a chain ending on the clock it names carries that clock out, and one
// whose clock is named inside parentheses carries none, the clock flowing
// into the parentheses and no further.
TEST(MulticlockParsing,
     TheClockAtAChainsEndFlowsOutOfItAndAParenthesisedOneDoesNot) {
  auto named = Parse(
      "module m;\n"
      "  assert property (@(posedge clk0) x ##1 @(posedge clk1) y |=> z);\n"
      "endmodule\n");
  ASSERT_NE(named.cu, nullptr);
  const SeqLinearBody* out = AntecedentBody(named);
  ASSERT_NE(out, nullptr);
  ASSERT_EQ(out->clock_out.size(), 1u);
  EXPECT_EQ(out->clock_out[0].signal->text, "clk1");
  auto grouped = Parse(
      "module m;\n"
      "  assert property (@(posedge clk0) w ##1 (x ##1 @(posedge clk1) y) "
      "|=> z);\n"
      "endmodule\n");
  ASSERT_NE(grouped.cu, nullptr);
  const SeqLinearBody* kept = AntecedentBody(grouped);
  ASSERT_NE(kept, nullptr);
  ASSERT_EQ(kept->operands.size(), 3u);
  ASSERT_EQ(kept->clocks.size(), 3u);
  EXPECT_EQ(kept->clocks[2][0].signal->text, "clk1");
  EXPECT_TRUE(kept->clock_out.empty());
}

}  // namespace
