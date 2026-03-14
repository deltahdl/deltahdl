#include "elaborator/type_eval.h"
#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(DataTypeParsing, CompatibleTypesIntToLogic) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  int a;\n"
      "  logic [31:0] b;\n"
      "  initial a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DataTypeParsing, AssignCompatibleIntToReal) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  real r;\n"
      "  initial r = 42;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
