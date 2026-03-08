#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §8.26.5: Assign implementing class to interface variable — OK parse.
TEST(ElabA8265, InterfaceRefAssignOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.26.5: Interface class is abstract — cannot be directly constructed.
TEST(ElabA8265, InterfaceClassIsAbstract) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
