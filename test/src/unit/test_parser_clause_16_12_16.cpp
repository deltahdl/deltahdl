// §16.12.16: Case

#include "fixture_parser.h"

using namespace delta;

return nullptr;
}

namespace {

// property_expr ::= case (...) property_case_item ... endcase
TEST(ParserA210, PropertyExpr_Case) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    case (sel)\n"
              "      2'b00: a |-> b;\n"
              "      2'b01: c |-> d;\n"
              "      default: 1;\n"
              "    endcase);\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #20: property_case_item
// property_case_item ::=
//     expression_or_dist { , expression_or_dist } : property_expr ;
//   | default [ : ] property_expr ;
// =============================================================================
TEST(ParserA210, PropertyCaseItem_MultiExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    case (sel)\n"
              "      2'b00, 2'b01: a |-> b;\n"
              "      default: 1;\n"
              "    endcase);\n"
              "endmodule\n"));
}

TEST(ParserA210, PropertyCaseItem_DefaultOnly) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    case (sel)\n"
              "      default: a;\n"
              "    endcase);\n"
              "endmodule\n"));
}

// property_case_item — default without colon
TEST(ParserA210, PropertyCaseItem_DefaultNoColon) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    case (sel)\n"
              "      2'b00: a |-> b;\n"
              "      default a;\n"
              "    endcase);\n"
              "endmodule\n"));
}

}  // namespace
