#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §8.26.1: Basic interface class declaration — elaborates OK.
TEST(ElabA8261, InterfaceClassDeclOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void do_thing();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.26.1: Interface class with typedef and localparam — OK.
TEST(ElabA8261, InterfaceClassTypeAndParamOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  typedef int my_int;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.26.1: Interface class with non-pure virtual method — error.
TEST(ElabA8261, InterfaceClassNonPureVirtualError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.26.1: Interface class with data member — error.
TEST(ElabA8261, InterfaceClassDataMemberError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  int data;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.26.1: Interface class with multiple pure virtuals — OK.
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

// §8.26.3: Interface class with parameter — OK.
TEST(ElabA8263, InterfaceClassWithParamOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
