#include "fixture_parser.h"

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

}  // namespace
