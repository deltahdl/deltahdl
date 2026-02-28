// §16.10: Local variables

#include "fixture_parser.h"

using namespace delta;


namespace {

// =============================================================================
// §A.2.10 Production #29: sequence_match_item
// sequence_match_item ::=
//     operator_assignment | inc_or_dec_expression | subroutine_call
// =============================================================================
TEST(ParserA210, SequenceMatchItem_Assignment) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b, x = c) |-> d);\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #40: assertion_variable_declaration
// assertion_variable_declaration ::=
//     var_data_type list_of_variable_decl_assignments ;
// =============================================================================
TEST(ParserA210, AssertionVariableDecl_InProperty) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p;\n"
              "    int x;\n"
              "    (a, x = b) |-> (c == x);\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(ParserA210, AssertionVariableDecl_InSequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s;\n"
              "    int x;\n"
              "    (a, x = b) ##1 (c == x);\n"
              "  endsequence\n"
              "endmodule\n"));
}

// sequence_match_item ::= inc_or_dec_expression
TEST(ParserA210, SequenceMatchItem_IncDec) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b, x++) |-> c);\n"
              "endmodule\n"));
}

// assertion_variable_declaration — multiple vars and complex type
TEST(ParserA210, AssertionVariableDecl_MultipleVars) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p;\n"
              "    int x;\n"
              "    logic [7:0] y;\n"
              "    (a, x = b) |-> (c == x);\n"
              "  endproperty\n"
              "endmodule\n"));
}

}  // namespace
