#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_expr.h"
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

TEST(AssertionSemanticsParsing, ConsecutiveRepetition) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a[*3] |-> b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// §16.9.2 and §16.12.2: a repetition on its own is a sequence, and a
// sequence is a sequential property, so a spec that is a repetition alone
// is read as one, its body a sequence with the repetition on its operand
// rather than a boolean the repetition's bracket would end.
TEST(AssertionSemanticsParsing, ARepetitionAloneIsASequentialProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a[*0:2]);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  const ModuleItem* item = nullptr;
  for (auto* candidate : r.cu->modules[0]->items) {
    if (candidate->kind == ModuleItemKind::kAssertProperty) item = candidate;
  }
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  ASSERT_NE(item->body->assert_sequence, nullptr);
  const SeqLinearBody& body = item->body->assert_sequence->seq_linear;
  ASSERT_EQ(body.operands.size(), 1u);
  EXPECT_EQ(body.repetitions[0].kind, SeqRepetition::Kind::kConsecutive);
  EXPECT_EQ(body.repetitions[0].min, 0u);
  EXPECT_EQ(body.repetitions[0].max, 2u);
}

TEST(AssertionSemanticsParsing, GotoRepetition) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ack[->1]);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(AssertionSemanticsParsing, NonconsecutiveRepetition) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ack[=2]);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// §16.9.2: a parenthesised sequence of more than one operand may be repeated
// by a range, `$`, a count of 0 or a count written as a constant expression,
// none of which copies of its operands spliced into the chain stand for. Each
// such group is read as a sequence of its own standing as one operand before
// c, as a group holding `or` is, the repetition on that operand and the
// group's two operands under it; an exact count, `[*2]`, is still unrolled
// into the chain, a and b twice before c.
TEST(SequenceRepetitionParsing, AGroupRepeatedByARangeIsOneNestedOperand) {
  auto r = Parse(
      "module m;\n"
      "  localparam int N = 2;\n"
      "  sequence s_range; (a ##1 b)[*1:2] ##1 c; endsequence\n"
      "  sequence s_plus; (a ##1 b)[+] ##1 c; endsequence\n"
      "  sequence s_zero; (a ##1 b)[*0] ##1 c; endsequence\n"
      "  sequence s_param; (a ##1 b)[*N] ##1 c; endsequence\n"
      "  sequence s_exact; (a ##1 b)[*2] ##1 c; endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  struct Expected {
    std::string_view name;
    uint32_t min;
    uint32_t max;
    bool count_expr;
  };
  for (const Expected& want :
       {Expected{"s_range", 1, 2, false},
        Expected{"s_plus", 1, SeqCycleDelay::kUnbounded, false},
        Expected{"s_zero", 0, 0, false}, Expected{"s_param", 0, 0, true}}) {
    SCOPED_TRACE(want.name);
    const ModuleItem* seq = FindItemByName(r.cu->modules[0]->items, want.name);
    ASSERT_NE(seq, nullptr);
    const SeqLinearBody& body = seq->seq_linear;
    ASSERT_EQ(body.operands.size(), 2u);
    const SeqRepetition& rep = body.repetitions[0];
    EXPECT_EQ(rep.kind, SeqRepetition::Kind::kConsecutive);
    EXPECT_EQ(rep.max_expr != nullptr, want.count_expr);
    if (!want.count_expr) {
      EXPECT_EQ(rep.min, want.min);
      EXPECT_EQ(rep.max, want.max);
    }
    const PropertyExprNode* group = body.operands[0]->property_actual;
    ASSERT_NE(group, nullptr);
    ASSERT_NE(group->sequence, nullptr);
    EXPECT_EQ(group->sequence->seq_linear.operands.size(), 2u);
    EXPECT_EQ(body.operands[1]->text, "c");
  }
  const ModuleItem* exact = FindItemByName(r.cu->modules[0]->items, "s_exact");
  ASSERT_NE(exact, nullptr);
  EXPECT_EQ(exact->seq_linear.operands.size(), 5u);
}

// §16.10: the match items of a group repeated by a range run at the end of
// each of its iterations, so they stay with the group's sequence, on its
// last operand, rather than on the operand after the group.
TEST(SequenceRepetitionParsing, ARepeatedGroupsMatchItemsEndEachIteration) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    int x;\n"
      "    (a ##1 b, x = 1)[*1:2] ##1 c;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* seq = FindItemByName(r.cu->modules[0]->items, "s");
  ASSERT_NE(seq, nullptr);
  const SeqLinearBody& body = seq->seq_linear;
  ASSERT_EQ(body.operands.size(), 2u);
  EXPECT_TRUE(body.match_items[1].empty());
  const PropertyExprNode* group = body.operands[0]->property_actual;
  ASSERT_NE(group, nullptr);
  ASSERT_NE(group->sequence, nullptr);
  const SeqLinearBody& inner = group->sequence->seq_linear;
  ASSERT_EQ(inner.operands.size(), 2u);
  EXPECT_TRUE(inner.match_items[0].empty());
  ASSERT_EQ(inner.match_items[1].size(), 1u);
  EXPECT_EQ(inner.match_items[1][0].lvar, "x");
}

}  // namespace
