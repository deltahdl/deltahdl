// §6.20.7: $ as a constant

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// § primary — $
TEST(ParserA84, PrimaryDollar) {
  auto r = Parse("module m;\n"
                 "  logic [7:0] q [$];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
// =============================================================================
// LRM section 20.6.3 -- $isunbounded (range system function)
// =============================================================================
TEST(ParserSection20, IsUnboundedBasic) {
  auto r = Parse("module m #(parameter int P = $);\n"
                 "  initial begin\n"
                 "    if ($isunbounded(P)) $display(\"unbounded\");\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =========================================================================
// §6.20.7: $ as a constant
// =========================================================================
TEST(ParserSection6, DollarConstant_ParamAssign) {
  EXPECT_TRUE(ParseOk6("module t;\n"
                       "  parameter p = $;\n"
                       "endmodule\n"));
}

} // namespace
