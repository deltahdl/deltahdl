#include "fixture_parser.h"

using namespace delta;

namespace {

// §16.2: "An assertion appears as an assertion statement that states the
// verification function to be performed.  The statement shall be of one
// of the following kinds: assert, assume, cover, restrict."  Observe that
// the parser accepts all four kinds at module-item level.
TEST(AssertionStatementGrammar, FourKindsParsedAtModuleLevel) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  property p; 1'b1; endproperty\n"
      "  a1: assert property (p);\n"
      "  a2: assume property (p);\n"
      "  a3: cover  property (p);\n"
      "  a4: restrict property (p);\n"
      "endmodule\n"));
}

// §16.2: "There is no immediate restrict assertion statement."  Observe
// that the parser rejects `restrict (...)` inside an always procedure.
TEST(AssertionStatementGrammar, NoImmediateRestrictInProceduralCode) {
  EXPECT_FALSE(ParseOk(
      "module m(input logic clk, input logic a);\n"
      "  always @(posedge clk) begin\n"
      "    restrict (a);\n"
      "  end\n"
      "endmodule\n"));
}

}  // namespace
