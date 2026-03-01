// §20.6.2: Expression size system function

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

using namespace delta;

namespace {

TEST(ParserSection6, TypeRefInBitsCast) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = $bits(int);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
