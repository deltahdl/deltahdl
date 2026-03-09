#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabA8268, InterfaceMethodDefaultArgsOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo(int a = 5);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function void foo(int a = 5);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
