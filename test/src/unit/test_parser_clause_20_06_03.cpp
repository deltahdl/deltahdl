// §20.6.3: Range system function

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection20, IsUnboundedInConditional) {
  auto r = Parse(
      "module m #(parameter int N = $);\n"
      "  generate\n"
      "    if (!$isunbounded(N)) begin\n"
      "      assign out = in;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection20, IsUnboundedWithBoundedParam) {
  auto r = Parse(
      "module m #(parameter int P = 42);\n"
      "  initial begin\n"
      "    if ($isunbounded(P)) $display(\"yes\");\n"
      "    else $display(\"no\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
