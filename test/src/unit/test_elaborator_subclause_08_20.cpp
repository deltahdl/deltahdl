#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

TEST(VirtualMethodElaboration, InitialOverridesVirtualError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  virtual function void f2(); endfunction\n"
      "endclass\n"
      "class A extends Base;\n"
      "  function :initial void f2(); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  A a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "method with ':initial' shall not override a virtual base class method",
      5, "8.20"));
}

TEST(VirtualMethodElaboration, ExtendsNoVirtualBaseError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  function void f1(); endfunction\n"
      "endclass\n"
      "class A extends Base;\n"
      "  virtual function :extends void f5(); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  A a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "method with ':extends' does not override a virtual base class method", 5,
      "8.20"));
}

TEST(VirtualMethodElaboration, OverrideFinalError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  virtual function :final void f2(); endfunction\n"
      "endclass\n"
      "class A extends Base;\n"
      "  virtual function void f2(); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  A a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot override a method declared ':final'", 5,
                            "8.20"));
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

// 8.20: the ':extends' specifier implies the method is virtual, so the
// 'virtual' keyword is optional when overriding a virtual base method.
TEST(VirtualMethodElaboration, ExtendsWithoutVirtualKeywordOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  virtual function void f2(); endfunction\n"
             "endclass\n"
             "class A extends Base;\n"
             "  function :extends void f2(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  A a;\n"
             "endmodule\n"));
}

TEST(VirtualMethodElaboration, FinalOnPureVirtualFunctionError) {
  ElabFixture f;
  ElabOk(
      "virtual class Base;\n"
      "  pure virtual function :final void display();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "':final' shall not be specified on a pure virtual method", 2, "8.20"));
}

TEST(VirtualMethodElaboration, FinalOnPureVirtualTaskError) {
  ElabFixture f;
  ElabOk(
      "virtual class Base;\n"
      "  pure virtual task :final run();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "':final' shall not be specified on a pure virtual method", 2, "8.20"));
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
  ElabFixture f;
  ElabOk(
      "virtual class Base;\n"
      "  pure virtual function void f3();\n"
      "endclass\n"
      "class C extends Base;\n"
      "  function :initial void f3(); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "method with ':initial' shall not override a virtual base class method",
      5, "8.20"));
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
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  function :final void f4(); endfunction\n"
      "endclass\n"
      "class B extends Base;\n"
      "  function void f4(); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  B b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot override a method declared ':final'", 5,
                            "8.20"));
}

TEST(VirtualMethodElaboration, OverrideFinalWithVirtualError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  function :final void f4(); endfunction\n"
      "endclass\n"
      "class B extends Base;\n"
      "  virtual function void f4(); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  B b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot override a method declared ':final'", 5,
                            "8.20"));
}

TEST(VirtualMethodElaboration, OverrideMismatchedArgTypeError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  virtual function void foo(int a); endfunction\n"
      "endclass\n"
      "class D extends Base;\n"
      "  virtual function void foo(bit a); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  D d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "' has mismatched type", 5, "8.20"));
}

TEST(VirtualMethodElaboration, OverrideMismatchedArgNameError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  virtual function void foo(int a); endfunction\n"
      "endclass\n"
      "class D extends Base;\n"
      "  virtual function void foo(int b); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  D d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "virtual method override argument name '", 5,
                            "8.20"));
}

TEST(VirtualMethodElaboration, OverrideMismatchedArgDirectionError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  virtual function void foo(input int a); endfunction\n"
      "endclass\n"
      "class D extends Base;\n"
      "  virtual function void foo(output int a); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  D d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "' has mismatched direction",
                            5, "8.20"));
}

TEST(VirtualMethodElaboration, OverrideMismatchedReturnTypeError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  virtual function int foo(); return 0; endfunction\n"
      "endclass\n"
      "class D extends Base;\n"
      "  virtual function bit foo(); return 0; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  D d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "virtual method override has mismatched return type", 5, "8.20"));
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

// 8.20: an override shall match the prototype's argument list, so a differing
// argument count is rejected.
TEST(VirtualMethodElaboration, OverrideMismatchedArgCountError) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  virtual function void foo(int a); endfunction\n"
      "endclass\n"
      "class D extends Base;\n"
      "  virtual function void foo(int a, int b); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  D d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "virtual method override has different number of arguments", 5, "8.20"));
}

// 8.20: a virtual function return type that is a class type must be the same
// type or one derived from the prototype's; an unrelated class is rejected.
TEST(VirtualMethodElaboration, OverrideNonCovariantReturnTypeError) {
  ElabFixture f;
  ElabOk(
      "class C; endclass\n"
      "class U; endclass\n"
      "class Base;\n"
      "  virtual function C make(); return null; endfunction\n"
      "endclass\n"
      "class D extends Base;\n"
      "  virtual function U make(); return null; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  D d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "virtual method override has mismatched return type", 7, "8.20"));
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
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  virtual function void foo(int a = 0); endfunction\n"
      "endclass\n"
      "class D extends Base;\n"
      "  virtual function void foo(int a); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  D d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "': presence of default must match", 5, "8.20"));
}

// §8.20 states the whole of the override signature rule: "Virtual method
// overrides in subclasses shall have matching argument types, identical
// argument names, identical qualifiers, and identical directions to the
// prototype." The subclause on the report is what tells this rejection from
// §8.14's rule about which member a base-class handle reaches, which the same
// two class declarations can also breach.
TEST(VirtualMethodElaboration,
     SignatureDiffersFromTheOverriddenMemberNames8_20) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  virtual function void foo(int a); endfunction\n"
      "endclass\n"
      "class D extends Base;\n"
      "  virtual function void foo(bit a); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  D d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "virtual method override argument '", 5, "8.20"));
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
