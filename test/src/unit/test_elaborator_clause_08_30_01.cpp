#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §8.30.1: weak_reference declaration elaborates OK.
TEST(ElabA8301, WeakReferenceDeclOk) {
  EXPECT_TRUE(ElabOk(
      "class my_obj;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

}  // namespace
