#include <gtest/gtest.h>

#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(SequenceMatchItem, SubroutineCallInSequenceParensParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic clk, a;\n"
              "  property p1;\n"
              "    @(posedge clk) (a, $display(\"matched\"));\n"
              "  endproperty\n"
              "  assert property (p1);\n"
              "endmodule\n"));
}

TEST(SequenceMatchItem, OperatorAssignmentMatchItemParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic clk, a;\n"
              "  int x;\n"
              "  property p1;\n"
              "    @(posedge clk) (a, x = x + 1);\n"
              "  endproperty\n"
              "  assert property (p1);\n"
              "endmodule\n"));
}

TEST(SequenceMatchItem, IncOrDecExpressionMatchItemParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic clk, a;\n"
              "  int x;\n"
              "  property p1;\n"
              "    @(posedge clk) (a, x++);\n"
              "  endproperty\n"
              "  assert property (p1);\n"
              "endmodule\n"));
}

TEST(SequenceMatchItem, ACallWrittenWithNoArgumentsIsCapturedAsOne) {
  auto r = Parse(
      "package P;\n"
      "  task tick; endtask\n"
      "endpackage\n"
      "module m;\n"
      "  logic clk, a;\n"
      "  sequence s; @(posedge clk) (a, note, P::tick, h.mark); endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* s = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(s, nullptr);
  ASSERT_EQ(s->seq_linear.match_items.size(), 1u);
  const std::vector<SeqMatchAssign>& items = s->seq_linear.match_items[0];
  ASSERT_EQ(items.size(), 3u);
  for (const SeqMatchAssign& item : items) {
    ASSERT_NE(item.call, nullptr);
    EXPECT_EQ(item.call->kind, ExprKind::kCall);
    EXPECT_TRUE(item.call->args.empty());
  }
  EXPECT_EQ(items[0].call->callee, "note");
}

}  // namespace
