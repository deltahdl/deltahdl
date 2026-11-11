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

TEST(VirtualMethodElaboration, OverrideSpecifierRulesHoldInEveryPlace) {
  ElabFixture f;
  ElabOk(
      "package pk;\n"
      "  class B; virtual task t(); endtask function void n(); endfunction "
      "function :final void q(); endfunction endclass\n"
      "  class D extends B;\n"
      "    task :initial t(); endtask\n"
      "    function :extends void n(); endfunction\n"
      "    function void q(); endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "virtual class VB;\n"
      "  pure virtual task pt();\n"
      "  virtual function void v(); endfunction\n"
      "  function :final void fin(); endfunction\n"
      "  virtual function :initial void fresh(); endfunction\n"
      "  function void plain(); endfunction\n"
      "endclass\n"
      "class M1 extends VB;\n"
      "  task pt(); endtask\n"
      "  function void plain(); endfunction\n"
      "endclass\n"
      "class M2 extends M1;\n"
      "  function void fin(); endfunction\n"
      "  function :extends void v(); endfunction\n"
      "  function :extends void plain(); endfunction\n"
      "  function :extends void nothing(); endfunction\n"
      "  task :extends pt(); endtask\n"
      "endclass\n"
      "program pr;\n"
      "  class P extends VB;\n"
      "    task :initial pt(); endtask\n"
      "    function :initial void plain(); endfunction\n"
      "  endclass\n"
      "endprogram\n"
      "interface ifc;\n"
      "  class I extends VB;\n"
      "    task pt(); endtask\n"
      "    virtual function void fin(); endfunction\n"
      "    function :initial :final void plain(); endfunction\n"
      "  endclass\n"
      "endinterface\n"
      "module m;\n"
      "  class K extends VB;\n"
      "    task pt(); endtask\n"
      "    function :extends :final void v(); endfunction\n"
      "  endclass\n"
      "  class K2 extends K;\n"
      "    function void v(); endfunction\n"
      "  endclass\n"
      "  pr p(); ifc i();\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {6, 21, 36, 46}) {
    EXPECT_TRUE(ReportedError(
        diags, "cannot override a method declared ':final'", kLine, "8.20"))
        << kLine;
  }
  for (const int kLine : {5, 23, 24}) {
    EXPECT_TRUE(ReportedError(
        diags,
        "method with ':extends' does not override a virtual base class method",
        kLine, "8.20"))
        << kLine;
  }
  for (const int kLine : {4, 29}) {
    EXPECT_TRUE(ReportedError(
        diags,
        "method with ':initial' shall not override a virtual base class method",
        kLine, "8.20"))
        << kLine;
  }
  for (const int kLine : {13, 17, 18, 22, 25, 30, 37, 42}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(VirtualMethodElaboration, TaskAndPlaceOverridesMatchTheirBaseSignature) {
  ElabFixture f;
  ElabOk(
      "package pk;\n"
      "  class B;\n"
      "    virtual task t1(int a); endtask\n"
      "    virtual task t2(int a); endtask\n"
      "    virtual task t3(input int a); endtask\n"
      "    virtual task t4(int a = 1); endtask\n"
      "    virtual task t5(int a, int b); endtask\n"
      "    virtual task t6(int a = 1); endtask\n"
      "  endclass\n"
      "  class D extends B;\n"
      "    task t1(byte a); endtask\n"
      "    task t2(int b); endtask\n"
      "    task t3(output int a); endtask\n"
      "    task t4(int a); endtask\n"
      "    task t5(int a); endtask\n"
      "    task t6(int a = 2); endtask\n"
      "  endclass\n"
      "endpackage\n"
      "program pr;\n"
      "  class B; virtual function int f(ref int a); return 0; endfunction "
      "endclass\n"
      "  class D extends B; function int f(inout int a); return 0; endfunction "
      "endclass\n"
      "  class E extends B; function int f(ref int a); return 1; endfunction "
      "endclass\n"
      "endprogram\n"
      "interface ifc;\n"
      "  class B; virtual function int f(int a); return 0; endfunction "
      "endclass\n"
      "  class D extends B; function byte f(int a); return 0; endfunction "
      "endclass\n"
      "endinterface\n"
      "module m; pr p(); ifc i(); endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {11}) {
    EXPECT_TRUE(ReportedError(
        diags, "virtual method override argument 'a' has mismatched type",
        kLine, "8.20"))
        << kLine;
  }
  for (const int kLine : {12}) {
    EXPECT_TRUE(ReportedError(
        diags,
        "virtual method override argument name 'b' does not match base 'a'",
        kLine, "8.20"))
        << kLine;
  }
  for (const int kLine : {13, 21}) {
    EXPECT_TRUE(ReportedError(
        diags, "virtual method override argument 'a' has mismatched direction",
        kLine, "8.20"))
        << kLine;
  }
  for (const int kLine : {14}) {
    EXPECT_TRUE(ReportedError(
        diags,
        "virtual method override argument 'a': presence of default must match",
        kLine, "8.20"))
        << kLine;
  }
  for (const int kLine : {15}) {
    EXPECT_TRUE(ReportedError(
        diags, "virtual method override has different number of arguments",
        kLine, "8.20"))
        << kLine;
  }
  for (const int kLine : {26}) {
    EXPECT_TRUE(ReportedError(
        diags, "virtual method override has mismatched return type", kLine,
        "8.20"))
        << kLine;
  }
  for (const int kLine : {16, 22}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(VirtualMethodElaboration,
     DISABLED_OverrideWidthsNamingParametersAreCompared) {
  ElabFixture f;
  ElabOk(
      "module m #(int W = 4);\n"
      "  localparam int L = 3;\n"
      "  class B;\n"
      "    virtual function logic [W-1:0] r(); return 0; endfunction\n"
      "    virtual function void a(logic [L:0] x); endfunction\n"
      "    virtual function void u(int x [W]); endfunction\n"
      "  endclass\n"
      "  class D extends B;\n"
      "    virtual function logic [W:0] r(); return 0; endfunction\n"
      "    virtual function void a(logic [L+1:0] x); endfunction\n"
      "    virtual function void u(int x [W+1]); endfunction\n"
      "  endclass\n"
      "  class E extends B;\n"
      "    virtual function logic [W-1:0] r(); return 0; endfunction\n"
      "    virtual function void a(logic [3:0] x); endfunction\n"
      "    virtual function void u(int x [4]); endfunction\n"
      "  endclass\n"
      "  class PB #(int N = 8);\n"
      "    virtual function logic [N-1:0] g(); return 0; endfunction\n"
      "  endclass\n"
      "  class PD extends PB #(8);\n"
      "    virtual function logic [6:0] g(); return 0; endfunction\n"
      "  endclass\n"
      "  class PE extends PB #(8);\n"
      "    virtual function logic [7:0] g(); return 0; endfunction\n"
      "  endclass\n"
      "  for (genvar i = 2; i < 3; i++) begin : gl\n"
      "    class GB; virtual function logic [i:0] h(); return 0; endfunction "
      "endclass\n"
      "    class GD extends GB; virtual function logic [i+1:0] h(); return 0; "
      "endfunction endclass\n"
      "    class GE extends GB; virtual function logic [2:0] h(); return 0; "
      "endfunction endclass\n"
      "  end\n"
      "  virtual class VB; pure virtual function logic [W-1:0] p(); endclass\n"
      "  class VD extends VB; virtual function logic [W:0] p(); return 0; "
      "endfunction endclass\n"
      "  interface class IC; pure virtual function logic [W-1:0] q(); "
      "endclass\n"
      "  class ID implements IC; virtual function logic [W:0] q(); return 0; "
      "endfunction endclass\n"
      "  class IE implements IC; virtual function logic [3:0] q(); return 0; "
      "endfunction endclass\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {9, 22, 29, 33}) {
    EXPECT_TRUE(ReportedError(
        diags, "virtual method override has mismatched return type", kLine,
        "8.20"))
        << kLine;
  }
  for (const int kLine : {10, 11}) {
    EXPECT_TRUE(ReportedError(
        diags, "virtual method override argument 'x' has mismatched type",
        kLine, "8.20"))
        << kLine;
  }
  for (const int kLine : {35}) {
    EXPECT_TRUE(ReportedError(
        diags, "method 'q' does not match signature of pure virtual method 'q'",
        kLine, "8.26.6.1"))
        << kLine;
  }
  for (const int kLine : {14, 15, 16, 25, 30, 36}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(VirtualMethodElaboration, DISABLED_OverrideUnpackedDimensionsAreCompared) {
  ElabFixture f;
  ElabOk(
      "typedef int A4[4];\n"
      "typedef int A5[5];\n"
      "class B;\n"
      "  virtual function A4 r(); return '{default:0}; endfunction\n"
      "  virtual function void u(int x [4]); endfunction\n"
      "  virtual function void d(int x []); endfunction\n"
      "  virtual function void k(int x [int]); endfunction\n"
      "  virtual function void s(int x [4]); endfunction\n"
      "endclass\n"
      "class D extends B;\n"
      "  virtual function A5 r(); return '{default:0}; endfunction\n"
      "  virtual function void u(int x [0:4]); endfunction\n"
      "  virtual function void d(int x [$]); endfunction\n"
      "  virtual function void k(int x [string]); endfunction\n"
      "  virtual function void s(int x [0:3]); endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {11}) {
    EXPECT_TRUE(ReportedError(
        diags, "virtual method override has mismatched return type", kLine,
        "8.20"))
        << kLine;
  }
  for (const int kLine : {12, 13, 14}) {
    EXPECT_TRUE(ReportedError(
        diags, "virtual method override argument 'x' has mismatched type",
        kLine, "8.20"))
        << kLine;
  }
  for (const int kLine : {15}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

}  // namespace
