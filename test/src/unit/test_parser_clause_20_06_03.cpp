#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(UtilitySystemTaskParsing, IsUnboundedInConditional) {
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

// §20.6.3 BNF (Syntax 20-8): the argument may be a hierarchical_parameter_
// identifier, not just a simple ps_parameter_identifier. A dotted reference to
// a parameter inside an instantiated submodule shall parse cleanly here.
TEST(UtilitySystemTaskParsing, IsUnboundedWithHierarchicalParam) {
  auto r = Parse(
      "module sub #(parameter int P = $);\n"
      "endmodule\n"
      "module top;\n"
      "  sub s();\n"
      "  initial if ($isunbounded(s.P)) $display(\"unbounded\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
