// §6.22.3: Assignment compatible

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

using namespace delta;

namespace {

TEST(ParserSection6, CompatibleTypesIntToLogic) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  int a;\n"
      "  logic [31:0] b;\n"
      "  initial a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// LRM section 6.22.3 -- Assignment compatible types
// =============================================================================
TEST(ParserSection6, AssignCompatibleIntToReal) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  real r;\n"
      "  initial r = 42;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
