#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(AssertionStatementGrammar, FourKindsParsedAtModuleLevel) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p; 1'b1; endproperty\n"
              "  a1: assert property (p);\n"
              "  a2: assume property (p);\n"
              "  a3: cover  property (p);\n"
              "  a4: restrict property (p);\n"
              "endmodule\n"));
}

TEST(AssertionStatementGrammar, NoImmediateRestrictInProceduralCode) {
  EXPECT_FALSE(
      ParseOk("module m(input logic clk, input logic a);\n"
              "  always @(posedge clk) begin\n"
              "    restrict (a);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
