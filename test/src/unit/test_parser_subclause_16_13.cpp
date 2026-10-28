#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_sequence_places.h"
#include "parser/ast_expr.h"
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

// §16.13.1 with §9.4 Syntax 9-4: the clock before a later operand may be
// written as a bare name, `@clk1`, and is recorded as `@(clk1)` would be,
// with no edge.
TEST(MulticlockParsing,
     ABareNamedClockAfterADelayIsRecordedAsTheOperandsClock) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk0) sig0 ##1 @clk1 sig1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  const PropertyExprNode* root = item->body->assert_property;
  ASSERT_NE(root, nullptr);
  ASSERT_NE(root->sequence, nullptr);
  const SeqLinearBody& body = root->sequence->seq_linear;
  ASSERT_EQ(body.operands.size(), 2u);
  ASSERT_EQ(body.clocks.size(), 2u);
  ASSERT_EQ(body.clocks[1].size(), 1u);
  EXPECT_EQ(body.clocks[1][0].edge, Edge::kNone);
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

// The name of the signal the one event of `clock` is an edge of, empty where
// it is not one event of a named signal.
std::string ClockSignal(const std::vector<EventExpr>& clock) {
  if (clock.size() != 1 || clock[0].signal == nullptr) return "";
  return std::string(clock[0].signal->text);
}

// §16.13.1 with Annex F.2 and F.3.2: a parenthesised group writing a clock of
// its own and repeated, `(@(posedge clk) a ##1 b)[*2]`, is read whatever its
// count, into a sequence of its own standing as one operand of the chain, the
// repetition on that operand and the clock on the operands of the sequence
// beneath it, for the elaborator to hold to the clock in force where the
// group stands; in a sequence a module or a package declares, a property and
// an assertion alike, and for a count, a range and a single operand.
TEST(MulticlockParsing, ARepeatedGroupWritingAClockIsOneNestedOperand) {
  for (const char* group :
       {"(@(posedge clk) a ##1 b)[*2]", "(@(posedge clk) a ##1 b)[*1:2]",
        "(@(posedge clk) a)[*2]"}) {
    auto r = Parse(InEverySequencePlace("@(posedge clk) " + std::string(group) +
                                        " ##1 c"));
    ASSERT_NE(r.cu, nullptr);
    EXPECT_FALSE(r.has_errors) << group;
    for (const SeqLinearBody* body : SequenceBodiesInEveryPlace(r)) {
      ASSERT_NE(body, nullptr) << group;
      ASSERT_EQ(body->operands.size(), 2u) << group;
      EXPECT_EQ(body->repetitions[0].kind, SeqRepetition::Kind::kConsecutive);
      const PropertyExprNode* tree = body->operands[0]->property_actual;
      ASSERT_NE(tree, nullptr) << group;
      ASSERT_NE(tree->sequence, nullptr) << group;
      const SeqLinearBody& inner = tree->sequence->seq_linear;
      ASSERT_FALSE(inner.clocks.empty()) << group;
      EXPECT_EQ(ClockSignal(inner.clocks[0]), "clk") << group;
    }
  }
}

// §16.13.1 with Annex F.3.2: a group writing no clock of its own, repeated
// after the chain wrote one, stands under that clock, as `@(b) R` does, and
// is unrolled as an unclocked group is, each copy of its operands on that
// clock.
TEST(MulticlockParsing, AGroupRepeatedUnderAWrittenClockIsUnrolledOnIt) {
  auto r = Parse(InEverySequencePlace(
      "@(posedge clk0) x ##1 @(posedge clk1) (a ##1 b)[*2]"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (const SeqLinearBody* body : SequenceBodiesInEveryPlace(r)) {
    ASSERT_NE(body, nullptr);
    ASSERT_EQ(body->operands.size(), 5u);
    ASSERT_EQ(body->clocks.size(), 5u);
    EXPECT_TRUE(body->clocks[0].empty());
    for (size_t i = 1; i < 5; ++i) {
      EXPECT_EQ(ClockSignal(body->clocks[i]), "clk1") << i;
    }
  }
}

// §16.9.10 with §16.13.1: the first operand of `within` may write a clock,
// which its operands keep, the two 1s the abbreviation wraps it in carrying
// none, the leading clock's, for the elaborator to hold to that clock.
TEST(MulticlockParsing, AWithinOperandWritingAClockKeepsIt) {
  auto r = Parse(InEverySequencePlace(
      "@(posedge clk) (@(posedge clk) a ##1 b) within (c ##1 d ##1 e)"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (const SeqLinearBody* body : SequenceBodiesInEveryPlace(r)) {
    ASSERT_NE(body, nullptr);
    EXPECT_TRUE(body->within);
    ASSERT_EQ(body->operands.size(), 4u);
    ASSERT_EQ(body->clocks.size(), 4u);
    EXPECT_TRUE(body->clocks[0].empty());
    EXPECT_EQ(ClockSignal(body->clocks[1]), "clk");
    EXPECT_EQ(ClockSignal(body->clocks[2]), "clk");
    EXPECT_TRUE(body->clocks[3].empty());
  }
}

}  // namespace
