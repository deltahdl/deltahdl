#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(EnumMethods, NameElaboratesOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef enum {RED, GREEN, BLUE} color_e;\n"
             "  color_e c;\n"
             "  string s;\n"
             "  initial s = c.name();\n"
             "endmodule\n"));
}

}  // namespace
