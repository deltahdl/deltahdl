// §9.3.2: Parallel blocks

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA28, BlockItemInForkJoinAny) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial fork\n"
              "    int x;\n"
              "    x = 1;\n"
              "  join_any\n"
              "endmodule\n"));
}

TEST(ParserA28, BlockItemInForkJoinNone) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial fork\n"
              "    int x;\n"
              "    x = 1;\n"
              "  join_none\n"
              "endmodule\n"));
}

}  // namespace
