// §6.24.1: Cast operator

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

using namespace delta;

namespace {

// =============================================================================
// LRM section 6.20 -- Type operator
// =============================================================================
TEST(ParserSection6, TypeExprInCast) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = int'(3.14);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
