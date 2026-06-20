#include "elaborator/type_eval.h"
#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(MatchingTypesParsing, TypedefAssignThroughPreprocessor) {
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
