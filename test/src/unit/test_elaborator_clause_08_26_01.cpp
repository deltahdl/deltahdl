#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabA8261, InterfaceClassDeclOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void do_thing();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ElabA8261, InterfaceClassTypeAndParamOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  typedef int my_int;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ElabA8261, InterfaceClassNonPureVirtualError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ElabA8261, InterfaceClassDataMemberError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  int data;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ElabA8261, InterfaceClassMultiplePureVirtualsOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "  pure virtual function int bar();\n"
             "  pure virtual task do_stuff();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ElabA8263, InterfaceClassWithParamOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
