// §20.6.1: Type name function

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

using namespace delta;

namespace {

TEST(ParserSection6, TypeOperatorTypeOf) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  int a;\n"
      "  initial begin\n"
      "    $display(\"%0d\", $typename(a));\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
