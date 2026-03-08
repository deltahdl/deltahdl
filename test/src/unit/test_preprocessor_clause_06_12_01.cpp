#include "elaborator/type_eval.h"
#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection6, AssignCompatibleRealToInt) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  int x;\n"
      "  initial x = 3.14;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}
