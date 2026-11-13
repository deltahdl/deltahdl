#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
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

constexpr const char* kSequenceForBoolean =
    "a sequence stands where the grammar admits only an expression_or_dist";

TEST(ThroughoutLeftOperand, ASequenceOnTheLeftIsReportedInEveryPlace) {
  for (const char* left :
       {"(a ##1 b)", "(a ##0 b)", "a[*2]", "a[*1:2]", "a[->1]", "a[=1:2]",
        "first_match(a ##1 b)", "(a ##1 b) or (c ##1 d)"}) {
    SCOPED_TRACE(left);
    auto r = Parse(InEverySequencePlace("@(posedge clk) " + std::string(left) +
                                        " throughout (c ##1 c)"));
    for (uint32_t line : {2u, 3u, 4u, 7u}) {
      EXPECT_TRUE(ReportedError(r.diags, kSequenceForBoolean, line, "A.2.10"))
          << line;
    }
  }
}

TEST(ThroughoutLeftOperand, AnExpressionOnTheLeftIsAcceptedInEveryPlace) {
  for (const char* left :
       {"a", "(a)", "((a && b))", "!a", "a == b", "a dist {0 := 1, 1 := 1}",
        "f(a)", "w.triggered", "$rose(a)", "p::B", "u1.v"}) {
    SCOPED_TRACE(left);
    auto r = Parse(InEverySequencePlace("@(posedge clk) " + std::string(left) +
                                        " throughout (c ##1 c)"));
    ASSERT_NE(r.cu, nullptr);
    EXPECT_FALSE(r.has_errors);
  }
}

}  // namespace
