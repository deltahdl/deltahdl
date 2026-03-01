// §6.16: String data type

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

using namespace delta;

namespace {

TEST(ParserSection6, AssignCompatibleStringLiteral) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  string s;\n"
      "  initial s = \"hello\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
