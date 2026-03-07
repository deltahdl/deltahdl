#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §8.26.9: Interface class without constraint blocks — OK.
TEST(ElabA8269, InterfaceClassNoConstraintsOk) {
  EXPECT_TRUE(ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

// §8.26.9: Interface class with pure virtual methods — randomize is
// separate (OK, no data members to randomize).
TEST(ElabA8269, InterfaceClassPureVirtualOk) {
  EXPECT_TRUE(ElabOk(
      "interface class IC;\n"
      "  pure virtual function bit funcA();\n"
      "  pure virtual function bit funcB();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  virtual function bit funcA();\n"
      "    return 1;\n"
      "  endfunction\n"
      "  virtual function bit funcB();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

}  // namespace
