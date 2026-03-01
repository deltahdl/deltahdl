// §6.22.2: Equivalent types

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

using namespace delta;

namespace {

// =============================================================================
// LRM section 6.22.2 -- Compatible types
// =============================================================================
TEST(ParserSection6, CompatibleTypesParseLogicVectors) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  assign a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
