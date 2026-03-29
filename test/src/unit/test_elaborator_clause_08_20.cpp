#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(VirtualMethodElaboration, VirtualMethodOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  virtual function void display(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Base b;\n"
             "endmodule\n"));
}

TEST(VirtualMethodElaboration, VirtualOverrideOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  virtual function void display(); endfunction\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  virtual function void display(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

TEST(VirtualMethodElaboration, InitialAndExtendsError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  function :initial :extends void foo(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(VirtualMethodElaboration, InitialOverridesVirtualError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  virtual function void f2(); endfunction\n"
             "endclass\n"
             "class A extends Base;\n"
             "  function :initial void f2(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  A a;\n"
             "endmodule\n"));
}

TEST(VirtualMethodElaboration, ExtendsNoVirtualBaseError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  function void f1(); endfunction\n"
             "endclass\n"
             "class A extends Base;\n"
             "  virtual function :extends void f5(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  A a;\n"
             "endmodule\n"));
}

TEST(VirtualMethodElaboration, OverrideFinalError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  virtual function :final void f2(); endfunction\n"
             "endclass\n"
             "class A extends Base;\n"
             "  virtual function void f2(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  A a;\n"
             "endmodule\n"));
}

TEST(VirtualMethodElaboration, InitialNonVirtualBaseOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  function void f1(); endfunction\n"
             "endclass\n"
             "class A extends Base;\n"
             "  function :initial void f1(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  A a;\n"
             "endmodule\n"));
}

TEST(VirtualMethodElaboration, ExtendsFinalOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  virtual function void f2(); endfunction\n"
             "endclass\n"
             "class A extends Base;\n"
             "  virtual function :extends :final void f2(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  A a;\n"
             "endmodule\n"));
}

TEST(VirtualMethodElaboration, FinalOnPureVirtualFunctionError) {
  EXPECT_FALSE(
      ElabOk("virtual class Base;\n"
             "  pure virtual function :final void display();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(VirtualMethodElaboration, FinalOnPureVirtualTaskError) {
  EXPECT_FALSE(
      ElabOk("virtual class Base;\n"
             "  pure virtual task :final run();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(VirtualMethodElaboration, FinalOnNonPureVirtualMethodOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  virtual function :final void display();\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(VirtualMethodElaboration, InitialOverridesPureVirtualError) {
  EXPECT_FALSE(
      ElabOk("virtual class Base;\n"
             "  pure virtual function void f3();\n"
             "endclass\n"
             "class C extends Base;\n"
             "  function :initial void f3(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(VirtualMethodElaboration, InitialFinalCombinedOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  virtual function void f2(); endfunction\n"
             "endclass\n"
             "class A extends Base;\n"
             "  virtual function :initial :final void f4(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  A a;\n"
             "endmodule\n"));
}

TEST(VirtualMethodElaboration, VirtualOverridesNonVirtualOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  function void f1(); endfunction\n"
             "endclass\n"
             "class A extends Base;\n"
             "  virtual function void f1(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  A a;\n"
             "endmodule\n"));
}

TEST(VirtualMethodElaboration, OverrideFinalNonVirtualError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  function :final void f4(); endfunction\n"
             "endclass\n"
             "class B extends Base;\n"
             "  function void f4(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  B b;\n"
             "endmodule\n"));
}

TEST(VirtualMethodElaboration, OverrideFinalWithVirtualError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  function :final void f4(); endfunction\n"
             "endclass\n"
             "class B extends Base;\n"
             "  virtual function void f4(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  B b;\n"
             "endmodule\n"));
}

TEST(VirtualMethodElaboration, OverrideMismatchedArgTypeError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  virtual function void foo(int a); endfunction\n"
             "endclass\n"
             "class D extends Base;\n"
             "  virtual function void foo(bit a); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  D d;\n"
             "endmodule\n"));
}

TEST(VirtualMethodElaboration, OverrideMismatchedArgNameError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  virtual function void foo(int a); endfunction\n"
             "endclass\n"
             "class D extends Base;\n"
             "  virtual function void foo(int b); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  D d;\n"
             "endmodule\n"));
}

TEST(VirtualMethodElaboration, OverrideMismatchedArgDirectionError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  virtual function void foo(input int a); endfunction\n"
             "endclass\n"
             "class D extends Base;\n"
             "  virtual function void foo(output int a); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  D d;\n"
             "endmodule\n"));
}

TEST(VirtualMethodElaboration, OverrideMismatchedReturnTypeError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  virtual function int foo(); return 0; endfunction\n"
             "endclass\n"
             "class D extends Base;\n"
             "  virtual function bit foo(); return 0; endfunction\n"
             "endclass\n"
             "module m;\n"
             "  D d;\n"
             "endmodule\n"));
}

TEST(VirtualMethodElaboration, OverrideCovariantReturnTypeOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  virtual function C self(); return null; endfunction\n"
             "endclass\n"
             "class D extends C;\n"
             "  virtual function D self(); return null; endfunction\n"
             "endclass\n"
             "module m;\n"
             "  D d;\n"
             "endmodule\n"));
}

TEST(VirtualMethodElaboration, OverrideMatchingArgTypesOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  virtual function void foo(int a); endfunction\n"
             "endclass\n"
             "class D extends Base;\n"
             "  virtual function void foo(int a); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  D d;\n"
             "endmodule\n"));
}

TEST(VirtualMethodElaboration, OverrideDefaultPresenceMismatchError) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  virtual function void foo(int a = 0); endfunction\n"
             "endclass\n"
             "class D extends Base;\n"
             "  virtual function void foo(int a); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  D d;\n"
             "endmodule\n"));
}

TEST(VirtualMethodElaboration, OverrideDefaultValueDifferentOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  virtual function void foo(int a = 0); endfunction\n"
             "endclass\n"
             "class D extends Base;\n"
             "  virtual function void foo(int a = 5); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  D d;\n"
             "endmodule\n"));
}

}  // namespace
