// §6.22.1: Matching types

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

using namespace delta;

namespace {

TEST(ParserSection6, CompatibleTypesNamedType) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  byte_t a;\n"
      "  byte_t b;\n"
      "  assign a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
