#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §8.19: Global constant (const with initializer) is OK.
TEST(ElabA819, GlobalConstantOk) {
  EXPECT_TRUE(ElabOk(
      "class Jumbo_Packet;\n"
      "  const int max_size = 9 * 1024;\n"
      "endclass\n"
      "module m;\n"
      "  Jumbo_Packet p;\n"
      "endmodule\n"));
}

// §8.19: Static const with initializer (global constant) is OK.
TEST(ElabA819, StaticConstGlobalOk) {
  EXPECT_TRUE(ElabOk(
      "class Config;\n"
      "  static const int VERSION = 3;\n"
      "endclass\n"
      "module m;\n"
      "  Config c;\n"
      "endmodule\n"));
}

// §8.19: Instance constant (const without initializer) is OK.
TEST(ElabA819, InstanceConstantOk) {
  EXPECT_TRUE(ElabOk(
      "class Big_Packet;\n"
      "  const int size;\n"
      "  function new();\n"
      "    size = 4096;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  Big_Packet p;\n"
      "endmodule\n"));
}

// §8.19: Instance constant (no init) declared static is an error.
TEST(ElabA819, InstanceConstStaticError) {
  EXPECT_FALSE(ElabOk(
      "class Bad;\n"
      "  static const int size;\n"
      "endclass\n"
      "module m;\n"
      "  Bad b;\n"
      "endmodule\n"));
}

}  // namespace
