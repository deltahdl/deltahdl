#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §8.26.4: Interface class declared before use — OK.
TEST(ElabA8264, InterfaceDeclaredBeforeUseOk) {
  EXPECT_TRUE(ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

// §8.26.4: Interface class with parameterized type — OK.
TEST(ElabA8264, ParameterizedInterfaceOk) {
  EXPECT_TRUE(ElabOk(
      "interface class IC #(type T = int);\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

}  // namespace
