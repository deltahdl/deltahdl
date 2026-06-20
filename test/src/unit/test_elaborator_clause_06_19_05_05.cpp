#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(EnumMethods, NumElaboratesOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef enum {RED, GREEN, BLUE} color_e;\n"
             "  color_e c;\n"
             "  int n;\n"
             "  initial n = c.num();\n"
             "endmodule\n"));
}

TEST(EnumMethods, NumSingleMemberElaboratesOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef enum {ONLY} one_e;\n"
             "  one_e o;\n"
             "  int n;\n"
             "  initial n = o.num();\n"
             "endmodule\n"));
}

}  // namespace
