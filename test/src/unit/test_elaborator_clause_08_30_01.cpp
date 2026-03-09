#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabA8301, WeakReferenceDeclOk) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
