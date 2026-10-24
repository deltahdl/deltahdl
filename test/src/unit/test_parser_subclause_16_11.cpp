#include <gtest/gtest.h>

#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(SequenceMatchItem, SubroutineCallInSequenceParensParses) {
  // §16.11 BNF (excerpt from Annex A.2.10): a sequence_expr may take the
  // form ( sequence_expr {, sequence_match_item} ) [ sequence_abbrev ], and
  // a sequence_match_item may itself be a subroutine_call. Confirm the
  // parser accepts the textual shape — an attached system task in a
  // comma-separated list following the sequence.
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
  // §16.11 BNF: sequence_match_item ::= operator_assignment | ...
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
  // §16.11 BNF: sequence_match_item ::= ... | inc_or_dec_expression | ...
  // The increment form must be accepted in the match-item slot.
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

// §16.11 with A.8.2: tf_call and method_call write their list of arguments
// as optional, so a match item naming a subroutine with none, plainly,
// through a package's scope or through a handle, is captured as the call it
// is with an empty one.
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
