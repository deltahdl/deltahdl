#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §8.13: Basic class extends elaborates OK.
TEST(ElabA813, ClassExtendsOk) {
  EXPECT_TRUE(ElabOk(
      "class Base;\n"
      "  int x;\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  int y;\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n"));
}

// §8.13: Extending a final class is illegal.
TEST(ElabA813, ExtendFinalClassError) {
  EXPECT_FALSE(ElabOk(
      "class :final TopPacket;\n"
      "endclass\n"
      "class BrokenPacket extends TopPacket;\n"
      "endclass\n"
      "module m;\n"
      "  BrokenPacket b;\n"
      "endmodule\n"));
}

// §8.13: Final class without being extended is fine.
TEST(ElabA813, FinalClassAloneOk) {
  EXPECT_TRUE(ElabOk(
      "class :final Sealed;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  Sealed s;\n"
      "endmodule\n"));
}

// §8.13: Multi-level inheritance elaborates OK.
TEST(ElabA813, MultiLevelInheritanceOk) {
  EXPECT_TRUE(ElabOk(
      "class A;\n"
      "endclass\n"
      "class B extends A;\n"
      "endclass\n"
      "class C extends B;\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n"));
}

// §8.13: Extending a final class in a chain is illegal.
TEST(ElabA813, ExtendFinalInChainError) {
  EXPECT_FALSE(ElabOk(
      "class A;\n"
      "endclass\n"
      "class :final B extends A;\n"
      "endclass\n"
      "class C extends B;\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n"));
}

}  // namespace
