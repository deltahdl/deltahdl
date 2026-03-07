#include "elaborator/type_eval.h"
#include "fixture_parser.h"

using namespace delta;

namespace {

// §6.22.6: Wire nets of same data type match.
TEST(ParserSection6, MatchingNettypesSameWire) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire logic [7:0] a;\n"
      "  wire logic [7:0] b;\n"
      "  assign a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §6.22.6: Tri and wire are matching nettypes.
TEST(ParserSection6, MatchingNettypesWireAndTri) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire logic [3:0] a;\n"
      "  tri logic [3:0] b;\n"
      "  assign a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
