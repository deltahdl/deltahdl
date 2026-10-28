#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_sequence_places.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

TEST(AssertionSemanticsParsing, Throughout) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) enable throughout (a ##1 b ##1 c));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// §16.9.9: the left operand of `throughout` is a condition and the right
// operand is a full sequence. The desugaring `(exp)[*0:$] intersect seq` leans
// on consecutive repetition (§16.9.2), so the guarded sequence must be allowed
// to carry a `[*N]` repetition. This mirrors the shape of the standard's own
// burst example: a negated condition held throughout a repeated match.
TEST(AssertionSemanticsParsing, ThroughoutGuardsRepeatedSequence) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge mclk)\n"
      "      (!burst_mode) throughout (##2 ((trdy==0)&&(irdy==0)) [*7]));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// §16.9.9: the guarded sequence may itself be an intersect composition — the
// very operator (§16.9.6) the throughout desugaring is defined in terms of. The
// parser must accept a throughout whose right operand is an intersect of two
// subsequences.
TEST(AssertionSemanticsParsing, ThroughoutGuardsIntersectSequence) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) enable throughout ((a ##1 b) intersect (c ##1 d)));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// §16.9.9 with §16.7: a throughout reached after a ranged delay is read, a 1
// standing at the start of each interval the range begins, at the tick it is
// read at, and the guarded sequence after it; in a sequence a module or a
// package declares, a property and an assertion alike.
TEST(AssertionSemanticsParsing, AThroughoutAfterARangedDelayIsRead) {
  for (const char* delay : {"##[1:2]", "##[1:$]"}) {
    auto r = Parse(InEverySequencePlace(
        "@(posedge clk) a " + std::string(delay) + " (e throughout b ##1 c)"));
    ASSERT_NE(r.cu, nullptr);
    EXPECT_FALSE(r.has_errors) << delay;
    for (const SeqLinearBody* body : SequenceBodiesInEveryPlace(r)) {
      ASSERT_NE(body, nullptr) << delay;
      ASSERT_EQ(body->operands.size(), 4u) << delay;
      EXPECT_EQ(body->operands[1]->text, "1") << delay;
      EXPECT_EQ(body->delays[1].min, 1u) << delay;
      EXPECT_NE(body->delays[1].max, 1u) << delay;
      EXPECT_EQ(body->delays[2].min, 0u) << delay;
      EXPECT_EQ(body->delays[2].max, 0u) << delay;
      ASSERT_EQ(body->throughouts.size(), 1u) << delay;
      EXPECT_EQ(body->throughouts[0].first, 1u) << delay;
      EXPECT_EQ(body->throughouts[0].last, 3u) << delay;
      EXPECT_TRUE(body->throughouts[0].begins_at_read) << delay;
    }
  }
}

// §16.9.9 with §16.7: the sequence a throughout guards may open with a ranged
// delay, the interval beginning where the throughout does, the least of the
// range before its first operand; the same throughout after a delay of one
// tick count keeps its interval's start where the delay ends.
TEST(AssertionSemanticsParsing, AThroughoutGuardingARangedDelayIsRead) {
  auto r = Parse(InEverySequencePlace("@(posedge clk) e throughout ##[1:2] b"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (const SeqLinearBody* body : SequenceBodiesInEveryPlace(r)) {
    ASSERT_NE(body, nullptr);
    ASSERT_EQ(body->operands.size(), 1u);
    EXPECT_EQ(body->delays[0].min, 1u);
    EXPECT_EQ(body->delays[0].max, 2u);
    ASSERT_EQ(body->throughouts.size(), 1u);
    EXPECT_EQ(body->throughouts[0].lead, 1u);
    EXPECT_FALSE(body->throughouts[0].begins_at_read);
  }
  auto fixed = Parse(
      InEverySequencePlace("@(posedge clk) a ##2 (e throughout ##[1:2] b)"));
  ASSERT_NE(fixed.cu, nullptr);
  EXPECT_FALSE(fixed.has_errors);
  for (const SeqLinearBody* body : SequenceBodiesInEveryPlace(fixed)) {
    ASSERT_NE(body, nullptr);
    ASSERT_EQ(body->operands.size(), 2u);
    EXPECT_EQ(body->delays[1].min, 3u);
    EXPECT_EQ(body->delays[1].max, 4u);
    ASSERT_EQ(body->throughouts.size(), 1u);
    EXPECT_EQ(body->throughouts[0].lead, 1u);
  }
}

}  // namespace
