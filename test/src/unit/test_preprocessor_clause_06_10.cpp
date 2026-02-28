// §6.10: Implicit declarations

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

using namespace delta;

namespace {

// =============================================================================
// LRM section 6.10 -- Implicit declarations
// =============================================================================
TEST(ParserSection6, ImplicitNetInPortList) {
  auto r = ParseWithPreprocessor(
      "module m(a, b);\n"
      "  input a;\n"
      "  output b;\n"
      "  assign b = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

TEST(ParserSection6, ImplicitNetInContAssign) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  assign out = in1 & in2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
