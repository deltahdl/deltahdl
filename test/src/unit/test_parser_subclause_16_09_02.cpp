#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "parser/ast_module.h"

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

}  // namespace
