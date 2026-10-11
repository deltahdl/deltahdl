#include <gtest/gtest.h>

#include <initializer_list>

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

// 8.20: an override takes the same argument list as its prototype, so a
// differing argument count is rejected.
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

// §8.20 states the whole of the override signature rule: a virtual method
// override in a subclass matches the prototype's argument types and repeats its
// argument names, qualifiers and directions exactly. The subclause on the
// report is what tells this rejection from §8.14's rule about which member a
// base-class handle reaches, which the same two class declarations can also
// breach.
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

// §8.20's override rules hold over a class a module declares as over one at
// compilation-unit scope.
TEST(VirtualMethodElaboration, ModuleClassOverrideArgumentNameIsChecked) {
  ElabFixture f;
  ElabOk(
      "class B; virtual function void f(int a); endfunction endclass\n"
      "module m;\n"
      "  class D extends B;\n"
      "    function void f(int b); endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "virtual method override argument name 'b' does "
                            "not match base 'a'",
                            4, "8.20"));
}

// §8.20: an override's qualifiers are those of the method it overrides, and
// `virtual` is the one it may leave off, so a local or protected qualifier
// written on one and not the other is a mismatch either way round, k's local
// as much as f's and g's protected. Matching qualifiers, the override of h,
// are legal.
TEST(VirtualMethodElaboration, OverrideQualifiersMatchTheOverriddenMethod) {
  ElabFixture f;
  ElabOk(
      "class B;\n"
      "  protected virtual function void f(); endfunction\n"
      "  virtual function void g(); endfunction\n"
      "  local virtual function void h(); endfunction\n"
      "  virtual function void k(); endfunction\n"
      "endclass\n"
      "class D extends B;\n"
      "  function void f(); endfunction\n"
      "  protected function void g(); endfunction\n"
      "  local function void h(); endfunction\n"
      "  local function void k(); endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  const char* const kMessage[] = {
      "virtual method override 'f' is not qualified local or protected as the "
      "method it overrides is",
      "virtual method override 'g' is not qualified local or protected as the "
      "method it overrides is",
      "virtual method override 'k' is not qualified local or protected as the "
      "method it overrides is"};
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage[0], 8, "8.20"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage[1], 9, "8.20"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "virtual method override 'h'", 10, "8.20"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage[2], 11, "8.20"));
}

// §8.20 asks an override's argument types to match the prototype's and its
// return type to match or derive from the base's, and §6.22.1 makes a typedef
// name match the type it stands for, whether the design or the class declares
// the typedef: the clause's Example 2 writes `T a` under `typedef int T` for
// `int a`. A type named behind a package scope, p::N, matches itself. A class
// return type is matched by a class derived from it, and by
// no other type.
TEST(VirtualMethodElaboration, TypedefsMatchTheTypesTheyNameInAnOverride) {
  ElabFixture f;
  ElabOk(
      "typedef int T;\n"
      "typedef byte B8;\n"
      "class X; endclass\n"
      "class C;\n"
      "  typedef shortint S;\n"
      "  virtual function C some_method(int a); return null; endfunction\n"
      "  virtual function byte r(); return 0; endfunction\n"
      "  virtual function void s(S v); endfunction\n"
      "  virtual function C q(); return null; endfunction\n"
      "  virtual function C w(); return null; endfunction\n"
      "endclass\n"
      "class D extends C;\n"
      "  typedef shortint S2;\n"
      "  virtual function D some_method(T a); return null; endfunction\n"
      "  virtual function B8 r(); return 0; endfunction\n"
      "  virtual function void s(S2 v); endfunction\n"
      "  virtual function int q(); return 0; endfunction\n"
      "  virtual function X w(); return null; endfunction\n"
      "endclass\n"
      "package p; typedef bit [3:0] N; endpackage\n"
      "class C2; virtual function void u(p::N v); endfunction endclass\n"
      "class D2 extends C2;\n"
      "  virtual function void u(p::N v); endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {14, 15, 16, 23}) {
    EXPECT_FALSE(ReportedError(diags, "virtual method override", kLine, "8.20"))
        << kLine;
  }
  for (const int kLine : {17, 18}) {
    EXPECT_TRUE(ReportedError(
        diags, "virtual method override has mismatched return type", kLine,
        "8.20"))
        << kLine;
  }
}

// §8.20 with §8.25: an override written in its class's own type parameter
// matches or not according to the specialization, so the generic declaration
// draws no report and each specialization a declaration uses is judged under
// the types it gives the parameters, by position, by name, or by default. The
// clause's Example 2: Y defaulting to logic is no match for int. A base
// method written in its own class's type parameter is likewise left to the
// specialization the subclass extends. An argument written in a type of its
// own, g's b, is no specialization's to judge.
TEST(VirtualMethodElaboration,
     AnOverrideInATypeParameterIsJudgedPerSpecialization) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  virtual function C some_method(int a); return null; endfunction\n"
      "  virtual function void g(int b, int c); endfunction endclass\n"
      "class D extends C; endclass\n"
      "class P #(type T = int);\n"
      "  virtual function void f(T a); endfunction\n"
      "endclass\n"
      "class Q extends P #(int);\n"
      "  virtual function void f(int a); endfunction\n"
      "endclass\n"
      "class E #(type Z = int, type Y = logic) extends C;\n"
      "  int x; virtual function void g(int b, Y c); endfunction\n"
      "  virtual function D some_method(Y a); return null; endfunction\n"
      "  function void extra(); endfunction\n"
      "endclass\n"
      "module a; class K; endclass K k; endmodule\n"
      "module b; class K; endclass endmodule\n"
      "module m; a ua();\n"
      "  E #() v1;\n"
      "  E #(int, int) v2;\n"
      "  E #(.Y(int)) v3;\n"
      "  E #(.Z(int)) v4;\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  const char* const kMessage =
      "virtual method override argument 'a' of 'E::some_method' has "
      "mismatched type in this specialization";
  EXPECT_TRUE(ReportedError(diags, kMessage, 19, "8.20"));
  EXPECT_FALSE(ReportedError(diags, kMessage, 20, "8.20"));
  EXPECT_FALSE(ReportedError(diags, kMessage, 21, "8.20"));
  EXPECT_TRUE(ReportedError(diags, kMessage, 22, "8.20"));
  EXPECT_TRUE(ReportedError(diags,
                            "virtual method override argument 'c' of 'E::g' "
                            "has mismatched type in this specialization",
                            19, "8.20"));
  EXPECT_FALSE(
      ReportedError(diags, "virtual method override argument 'b'", 19, "8.20"));
  for (const int kLine : {9, 13, 14, 15}) {
    EXPECT_FALSE(ReportedError(diags, "virtual method override", kLine, "8.20"))
        << kLine;
  }
}

// §8.20 holds an override to the method of the class its own class extends,
// that class being the one the extends name resolves to from the scope the
// class is written in (§8.13), though another module declares a class of the
// same name.
TEST(VirtualMethodElaboration, AnOverrideIsJudgedAgainstItsOwnScopesBase) {
  ElabFixture f;
  ElabOk(
      "module a;\n"
      "  class K; endclass\n"
      "endmodule\n"
      "module b;\n"
      "  class K; virtual function void f(int x); endfunction endclass\n"
      "  class D extends K; function void f(int y); endfunction endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "virtual method override argument name 'y' does "
                            "not match base 'x'",
                            6, "8.20"));
}

}  // namespace
