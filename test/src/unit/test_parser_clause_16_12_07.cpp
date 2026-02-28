// §16.12.7: Implication

#include "fixture_parser.h"

using namespace delta;

namespace {

// property_expr ::= sequence_expr |-> property_expr
TEST(ParserA210, PropertyExpr_OverlappedImplication) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) req |-> ack);\n"
              "endmodule\n"));
}

// property_expr ::= sequence_expr |=> property_expr
TEST(ParserA210, PropertyExpr_NonOverlappedImplication) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) req |=> ack);\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #30: sequence_instance
// sequence_instance ::=
//     ps_or_hierarchical_sequence_identifier
//     [ ( [sequence_list_of_arguments] ) ]
// =============================================================================
TEST(ParserA210, SequenceInstance_InProperty) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a ##1 b; endsequence\n"
              "  property p; s |-> c; endproperty\n"
              "  assert property (p);\n"
              "endmodule\n"));
}

}  // namespace
