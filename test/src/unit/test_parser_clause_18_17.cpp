// §18.17: Random sequence generation—randsequence

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.6.12 Randsequence — complex / combined constructs
// =============================================================================
// Multiple productions with mixed prods (if, repeat, code_block, items)
TEST(ParserA612, ComplexMixedProds) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : repeat(2) step { $display(\"done\"); };\n"
      "      step : if (1) a else b;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
