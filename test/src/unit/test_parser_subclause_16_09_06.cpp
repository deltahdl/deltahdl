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

TEST(AssertionSemanticsParsing, Intersect) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) (a ##[1:5] b) intersect (c ##[2:4] d));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(AssertionSemanticsParsing, AnIntersectOfBooleansIsASequentialProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a intersect b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* item = nullptr;
  for (auto* candidate : r.cu->modules[0]->items) {
    if (candidate->kind == ModuleItemKind::kAssertProperty) item = candidate;
  }
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  ASSERT_NE(item->body->assert_sequence, nullptr);
  const SeqLinearBody& body = item->body->assert_sequence->seq_linear;
  ASSERT_EQ(body.operands.size(), 1u);
  ASSERT_EQ(body.intersects.size(), 1u);
  EXPECT_EQ(body.intersects[0].operands.size(), 1u);
}

}  // namespace
