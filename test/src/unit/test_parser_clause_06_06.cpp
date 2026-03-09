#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserAnnexA, A2NetDeclTriWandWor) {
  auto r = Parse("module m; tri t; wand wa; wor wo; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items.size(), 3u);
}
TEST(ParserSection6, AllBuiltinNetTypes) {
  auto r = Parse(
      "module t;\n"
      "  wire w;\n"
      "  tri t;\n"
      "  wand wa;\n"
      "  wor wo;\n"
      "  triand ta;\n"
      "  trior to_;\n"
      "  tri0 t0;\n"
      "  tri1 t1;\n"
      "  supply0 s0;\n"
      "  supply1 s1;\n"
      "  uwire uw;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_GE(r.cu->modules[0]->items.size(), 11u);
}

}  // namespace
