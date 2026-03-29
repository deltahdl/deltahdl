#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(InterfaceClassMethodDefaults, MatchingDefaultValuesOk) {
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

TEST(InterfaceClassMethodDefaults, MultipleDefaultArgsOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function int calc(int a = 0, int b = 1);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function int calc(int a = 0, int b = 1);\n"
             "    return a + b;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, MixedDefaultAndNonDefaultArgsOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function int calc(int a, int b = 1);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function int calc(int a, int b = 1);\n"
             "    return a + b;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, ImplementorMissingDefaultError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo(int a = 5);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function void foo(int a);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, ImplementorAddsUnexpectedDefaultError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo(int a);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function void foo(int a = 5);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, MultipleImplementorsOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function int get(int a = 10);\n"
             "endclass\n"
             "class A implements IC;\n"
             "  virtual function int get(int a = 10);\n"
             "    return a;\n"
             "  endfunction\n"
             "endclass\n"
             "class B implements IC;\n"
             "  virtual function int get(int a = 10);\n"
             "    return a + 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, InheritedInterfaceDefaultArgsOk) {
  EXPECT_TRUE(
      ElabOk("interface class Base;\n"
             "  pure virtual function int foo(int a = 3);\n"
             "endclass\n"
             "interface class Derived extends Base;\n"
             "endclass\n"
             "class C implements Derived;\n"
             "  virtual function int foo(int a = 3);\n"
             "    return a;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, MismatchedDefaultValueError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo(int a = 5);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function void foo(int a = 10);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, MismatchedSecondDefaultValueError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function int calc(int a = 0, int b = 1);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function int calc(int a = 0, int b = 99);\n"
             "    return a + b;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, NonConstantDefaultValueError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo(int a = x);\n"
             "endclass\n"
             "module m;\n"
             "  int x = 5;\n"
             "endmodule\n"));
}

TEST(InterfaceClassMethodDefaults, ConstantExpressionDefaultValueOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function int foo(int a = 3 + 4);\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function int foo(int a = 3 + 4);\n"
             "    return a;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
