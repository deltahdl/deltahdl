#include <gtest/gtest.h>

#include <initializer_list>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(OutOfBlockDeclElaboration, OutOfBlockFuncOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  extern function int foo();\n"
             "endclass\n"
             "function int C::foo();\n"
             "  return 42;\n"
             "endfunction\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(OutOfBlockDeclElaboration, OutOfBlockTaskOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  extern task run();\n"
             "endclass\n"
             "task C::run();\n"
             "endtask\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(OutOfBlockDeclElaboration, UnknownClassError) {
  ElabFixture f;
  ElabOk(
      "function int UnknownClass::foo();\n"
      "  return 0;\n"
      "endfunction\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "out-of-block declaration for unknown class", 1,
                            "8.24"));
}

TEST(OutOfBlockDeclElaboration, NoMatchingPrototypeNames8_24) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  function int bar(); endfunction\n"
      "endclass\n"
      "function int C::foo();\n"
      "  return 0;\n"
      "endfunction\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "no matching extern prototype for", 4, "8.24"));
}

TEST(OutOfBlockDeclElaboration, DuplicateOutOfBlockError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  extern function int foo();\n"
      "endclass\n"
      "function int C::foo();\n"
      "  return 42;\n"
      "endfunction\n"
      "function int C::foo();\n"
      "  return 99;\n"
      "endfunction\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "duplicate out-of-block declaration for", 7,
                            "8.24"));
}

TEST(OutOfBlockDeclElaboration, OutOfBlockConstructorOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  extern function new();\n"
             "endclass\n"
             "function C::new();\n"
             "endfunction\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(OutOfBlockDeclElaboration, NoExternNoOutOfBlockOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  function int foo(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(OutOfBlockDeclElaboration, DuplicateOutOfBlockTaskError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  extern task run();\n"
      "endclass\n"
      "task C::run();\n"
      "endtask\n"
      "task C::run();\n"
      "endtask\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "duplicate out-of-block declaration for", 6,
                            "8.24"));
}

TEST(OutOfBlockDeclElaboration, MultipleExternMethodsOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  extern function int foo();\n"
             "  extern task bar();\n"
             "endclass\n"
             "function int C::foo();\n"
             "  return 0;\n"
             "endfunction\n"
             "task C::bar();\n"
             "endtask\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(OutOfBlockDeclElaboration, OutOfBlockForNonExternMethodError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  function int foo();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "function int C::foo();\n"
      "  return 1;\n"
      "endfunction\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "no matching extern prototype for", 6, "8.24"));
}

TEST(OutOfBlockDeclElaboration, OutOfBlockConstructorWithArgsOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  extern function new(int val);\n"
             "endclass\n"
             "function C::new(int val);\n"
             "  x = val;\n"
             "endfunction\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(OutOfBlockDeclElaboration, ReturnTypeClassScopeOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  typedef int T;\n"
             "  extern function T f();\n"
             "endclass\n"
             "function C::T C::f();\n"
             "  return 1;\n"
             "endfunction\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(OutOfBlockDeclElaboration, UnknownClassTaskError) {
  ElabFixture f;
  ElabOk(
      "task NoSuchClass::run();\n"
      "endtask\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "out-of-block declaration for unknown class", 1,
                            "8.24"));
}

TEST(OutOfBlockDeclElaboration, MismatchedArgCountError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  extern function int foo(int a);\n"
      "endclass\n"
      "function int C::foo(int a, int b);\n"
      "  return a + b;\n"
      "endfunction\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "out-of-block declaration for 'C::foo' has 2 "
                            "argument(s) but the prototype has 1",
                            4, "8.24"));
}

TEST(OutOfBlockDeclElaboration, MismatchedArgTypeError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  extern function int foo(int a);\n"
      "endclass\n"
      "function int C::foo(real a);\n"
      "  return 0;\n"
      "endfunction\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "out-of-block declaration for 'C::foo' argument "
                            "'a' has mismatched type",
                            4, "8.24"));
}

TEST(OutOfBlockDeclElaboration, MismatchedReturnTypeError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  extern function int foo();\n"
      "endclass\n"
      "function real C::foo();\n"
      "  return 1.0;\n"
      "endfunction\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "out-of-block declaration for 'C::foo' has "
                            "mismatched return type",
                            4, "8.24"));
}

TEST(OutOfBlockDeclElaboration, MatchingSignatureOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  extern function int add(int a, int b);\n"
             "endclass\n"
             "function int C::add(int a, int b);\n"
             "  return a + b;\n"
             "endfunction\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(OutOfBlockDeclElaboration, MismatchedArgDirectionError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  extern function void foo(input int a);\n"
      "endclass\n"
      "function void C::foo(output int a);\n"
      "endfunction\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "out-of-block declaration for 'C::foo' argument "
                            "'a' has mismatched direction",
                            4, "8.24"));
}

TEST(OutOfBlockDeclElaboration, MismatchedMethodKindError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  extern function int foo();\n"
      "endclass\n"
      "task C::foo();\n"
      "endtask\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "out-of-block declaration for 'C::foo' is a task "
                            "but the prototype is a function",
                            4, "8.24"));
}

TEST(OutOfBlockDeclElaboration, DefaultArgOmittedInBodyOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  extern function int foo(int a = 5);\n"
             "endclass\n"
             "function int C::foo(int a);\n"
             "  return a;\n"
             "endfunction\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(OutOfBlockDeclElaboration, DefaultArgRepeatedIdenticalOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  extern function int foo(int a = 5);\n"
             "endclass\n"
             "function int C::foo(int a = 5);\n"
             "  return a;\n"
             "endfunction\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(OutOfBlockDeclElaboration, DefaultArgRepeatedMismatchError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  extern function int foo(int a = 5);\n"
      "endclass\n"
      "function int C::foo(int a = 6);\n"
      "  return a;\n"
      "endfunction\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "syntactically identical to the prototype", 4,
                            "8.24"));
}

TEST(OutOfBlockDeclElaboration, DefaultArgOnlyInBodyError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  extern function int foo(int a);\n"
      "endclass\n"
      "function int C::foo(int a = 5);\n"
      "  return a;\n"
      "endfunction\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "syntactically identical to the prototype", 4,
                            "8.24"));
}

TEST(OutOfBlockDeclElaboration, DefaultArgCompoundExprIdenticalOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  extern function int foo(int a = 1 + 1);\n"
             "endclass\n"
             "function int C::foo(int a = 1 + 1);\n"
             "  return a;\n"
             "endfunction\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(OutOfBlockDeclElaboration, DefaultArgSameValueDifferentSyntaxError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  extern function int foo(int a = 2);\n"
      "endclass\n"
      "function int C::foo(int a = 1 + 1);\n"
      "  return a;\n"
      "endfunction\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "syntactically identical to the prototype", 4,
                            "8.24"));
}

TEST(OutOfBlockDeclElaboration, OutOfBlockBeforeClassError) {
  ElabFixture f;
  ElabOk(
      "function int C::foo();\n"
      "  return 0;\n"
      "endfunction\n"
      "class C;\n"
      "  extern function int foo();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "comes before the declaration of class", 1,
                            "8.24"));
}

TEST(OutOfBlockDeclElaboration, ThisInModuleOutOfBlockMethodIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  class C;\n"
             "    int x;\n"
             "    extern function void set(int v);\n"
             "  endclass\n"
             "  function void C::set(int v);\n"
             "    this.x = v;\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(OutOfBlockDeclElaboration, ThisInModuleStaticOutOfBlockMethodIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  class C;\n"
      "    int x;\n"
      "    extern static function void f();\n"
      "  endclass\n"
      "  function void C::f();\n"
      "    this.x = 1;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not be used in a static method", 6, "8.10"));
}

TEST(OutOfBlockDeclElaboration, ThisInUnitStaticOutOfBlockMethodIsError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  int x;\n"
      "  extern static function void f();\n"
      "endclass\n"
      "function void C::f();\n"
      "  this.x = 1;\n"
      "endfunction\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not be used in a static method", 5, "8.10"));
}

TEST(OutOfBlockDeclElaboration, AnOutOfBlockBodyIsHeldToTheMethodRules) {
  ElabFixture f;
  ElabOk(
      "class B; int k; function new(int a = 0); endfunction endclass\n"
      "class C;\n"
      "  int k;\n"
      "  const int g = 1;\n"
      "  extern static function int f();\n"
      "  extern function void h();\n"
      "endclass\n"
      "function int C::f(); return k; endfunction\n"
      "function void C::h(); super.k = 1; g = 2; endfunction\n"
      "class D extends B;\n"
      "  int x;\n"
      "  extern function new();\n"
      "endclass\n"
      "function D::new(); x = 1; super.new(2); endfunction\n"
      "package p;\n"
      "  class E; int k; extern static function int s(); endclass\n"
      "  function int E::s(); return this.k; endfunction\n"
      "endpackage\n"
      "module m; endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "static method shall not access non-static members", 8, "8.10"));
  EXPECT_TRUE(ReportedError(
      diags, "'super' shall only be used in a derived class", 9, "8.15"));
  EXPECT_TRUE(
      ReportedError(diags, "assignment to global constant 'g'", 9, "8.19"));
  EXPECT_TRUE(ReportedError(diags,
                            "super.new() does not open the constructor, and no "
                            "executable statement may come before it",
                            14, "8.17"));
  EXPECT_TRUE(ReportedError(
      diags, "'this' and 'super' shall not be used in a static method", 17,
      "8.10"));
}

TEST(OutOfBlockDeclElaboration, OutOfBlockDeclarationsInEveryScopeAreChecked) {
  ElabFixture f;
  ElabOk(
      "package p;\n"
      "  class C;\n"
      "    extern function int f(int a);\n"
      "    extern function void g();\n"
      "  endclass\n"
      "  function int C::f(byte a); return 0; endfunction\n"
      "  function void C::g(); endfunction\n"
      "  function void C::g(); endfunction\n"
      "endpackage\n"
      "module m; class E; endclass\n"
      "  function void D::h(); endfunction\n"
      "  class D; extern function void h(); endclass\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags,
      "out-of-block declaration for 'C::f' argument 'a' has mismatched "
      "type",
      6, "8.24"));
  EXPECT_TRUE(ReportedError(
      diags, "duplicate out-of-block declaration for 'C::g'", 8, "8.24"));
  EXPECT_TRUE(ReportedError(diags,
                            "out-of-block declaration for 'D::h' comes before "
                            "the declaration of class 'D'",
                            11, "8.24"));
}

TEST(OutOfBlockDeclElaboration, AModulesClassHasNoUnitOutOfBlockDeclaration) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  class C; extern function void f(); endclass\n"
      "endmodule\n"
      "function void C::f(); endfunction\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "out-of-block declaration for unknown class 'C'", 4,
                            "8.24"));
}

TEST(OutOfBlockDeclElaboration, ATypeNameResolvingDifferentlyIsReported) {
  ElabFixture f;
  ElabOk(
      "package p; typedef int T; endpackage\n"
      "typedef int T;\n"
      "class C;\n"
      "  typedef int U;\n"
      "  extern function void f(T x);\n"
      "  extern function U g(p::T y);\n"
      "  extern function T h();\n"
      "  typedef real T;\n"
      "endclass\n"
      "function void C::f(T x); endfunction\n"
      "function C::U C::g(p::T y); return 0; endfunction\n"
      "function C::T C::h(); return 0; endfunction\n"
      "class N; endclass\n"
      "class C2;\n"
      "  extern function void k(N z);\n"
      "  class N; endclass\n"
      "endclass\n"
      "function void C2::k(N z); endfunction\n"
      "module m; endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  const char* const kMessage[] = {
      "out-of-block declaration for 'C::f' resolves 'T' to the class's own "
      "type",
      "out-of-block declaration for 'C::h' resolves 'T' to the class's own "
      "type",
      "out-of-block declaration for 'C2::k' resolves 'N' to the class's own "
      "type"};
  EXPECT_TRUE(ReportedError(diags, kMessage[0], 10, "8.24"));
  EXPECT_TRUE(ReportedError(diags, kMessage[1], 12, "8.24"));
  EXPECT_FALSE(ReportedError(diags, "resolves", 11, "8.24"));
  EXPECT_TRUE(ReportedError(diags, kMessage[2], 18, "8.24"));
}

TEST(OutOfBlockDeclElaboration, ArgumentNamesMatchThePrototype) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  extern function void f(int a);\n"
      "  extern task t(input int x, output int y);\n"
      "endclass\n"
      "function void C::f(int b); endfunction\n"
      "task C::t(input int x, output int z); endtask\n"
      "module m; endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags,
                            "out-of-block declaration for 'C::f' names "
                            "argument 'b' where the prototype names it 'a'",
                            5, "8.24"));
  EXPECT_TRUE(ReportedError(diags,
                            "out-of-block declaration for 'C::t' names "
                            "argument 'z' where the prototype names it 'y'",
                            6, "8.24"));
}

const char* const kOutOfBlockSignatureSrc =
    "class C;\n"
    "  extern function void f1(logic signed [3:0] x);\n"
    "  extern function void f2(logic [3:0] x);\n"
    "  extern function void f3(int x[2]);\n"
    "  extern function void f4();\n"
    "  extern function int f5();\n"
    "  extern function void f6(logic [3:0] x);\n"
    "  extern function void f7(int x[2]);\n"
    "  extern function int f8();\n"
    "  local int lp;\n"
    "  static int sp;\n"
    "  typedef byte B;\n"
    "endclass\n"
    "function void C::f1(logic [3:0] x); endfunction\n"
    "function void C::f2(logic [7:0] x); endfunction\n"
    "function void C::f3(int x[3]); endfunction\n"
    "function int C::f4(); return 0; endfunction\n"
    "function void C::f5(); endfunction\n"
    "function void C::f6(logic [3:0] x); endfunction\n"
    "function void C::f7(int x[2]); endfunction\n"
    "function int C::f8(); B b; b = 1; return lp + sp + b; endfunction\n"
    "module m; endmodule\n";

TEST(OutOfBlockDeclElaboration, SignednessWidthAndVoidDifferencesAreReported) {
  ElabFixture f;
  ElaborateSrc(kOutOfBlockSignatureSrc, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {14, 15}) {
    EXPECT_TRUE(
        ReportedError(diags, "argument 'x' has mismatched type", kLine, "8.24"))
        << kLine;
  }
  for (const int kLine : {17, 18}) {
    EXPECT_TRUE(
        ReportedError(diags, "has mismatched return type", kLine, "8.24"))
        << kLine;
  }
  for (const int kLine : {19, 20, 21}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(OutOfBlockDeclElaboration,
     DISABLED_UnpackedDimensionDifferenceIsReported) {
  ElabFixture f;
  ElaborateSrc(kOutOfBlockSignatureSrc, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {16}) {
    EXPECT_TRUE(
        ReportedError(diags, "argument 'x' has mismatched type", kLine, "8.24"))
        << kLine;
  }
}

TEST(OutOfBlockDeclElaboration, DuplicateBodyIsReportedInEveryScope) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  class PC; extern function void f(); extern task t(); endclass\n"
      "  function void PC::f(); endfunction\n"
      "  function void PC::f(); endfunction\n"
      "  task PC::t(); endtask\n"
      "  task PC::t(); endtask\n"
      "endpackage\n"
      "interface ifc;\n"
      "  class IC; extern function void f(); endclass\n"
      "  function void IC::f(); endfunction\n"
      "  function void IC::f(); endfunction\n"
      "endinterface\n"
      "program pr;\n"
      "  class RC; extern function void f(); endclass\n"
      "  function void RC::f(); endfunction\n"
      "  function void RC::f(); endfunction\n"
      "endprogram\n"
      "module m;\n"
      "  class MC; extern function void f(); extern function void g(); "
      "endclass\n"
      "  function void MC::f(); endfunction\n"
      "  function void MC::f(); endfunction\n"
      "  function void MC::g(); endfunction\n"
      "  ifc i();\n"
      "  pr q();\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {4, 6, 11, 16, 21}) {
    EXPECT_TRUE(ReportedError(diags, "duplicate out-of-block declaration for",
                              kLine, "8.24"))
        << kLine;
  }
  for (const int kLine : {22}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

const char* const kBareOuterReturnTypeSrc =
    "typedef real T;\n"
    "typedef int S;\n"
    "typedef int G;\n"
    "class C;\n"
    "  typedef int T;\n"
    "  typedef struct { int a; } S;\n"
    "  typedef byte U;\n"
    "  extern function T f();\n"
    "  extern function S g();\n"
    "  extern function G k();\n"
    "  extern function U u();\n"
    "endclass\n"
    "function T C::f(); return 1; endfunction\n"
    "function S C::g(); return 1; endfunction\n"
    "function G C::k(); return 1; endfunction\n"
    "function C::U C::u(); return 1; endfunction\n"
    "package p;\n"
    "  typedef real T;\n"
    "  class PC;\n"
    "    typedef int T;\n"
    "    extern function T f();\n"
    "    extern function T f2();\n"
    "  endclass\n"
    "  function T PC::f(); return 1; endfunction\n"
    "  function PC::T PC::f2(); return 1; endfunction\n"
    "endpackage\n"
    "module m;\n"
    "  typedef real T;\n"
    "  class MC;\n"
    "    typedef int T;\n"
    "    extern function T f();\n"
    "    extern function T f2();\n"
    "  endclass\n"
    "  function T MC::f(); return 1; endfunction\n"
    "  function MC::T MC::f2(); return 1; endfunction\n"
    "endmodule\n";

TEST(OutOfBlockDeclElaboration, OuterOrScopedReturnTypeIsAccepted) {
  ElabFixture f;
  ElaborateSrc(kBareOuterReturnTypeSrc, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {15, 16, 25, 35}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(OutOfBlockDeclElaboration,
     DISABLED_BareReturnTypeNamingAnOuterTypeIsComparedWithThePrototype) {
  ElabFixture f;
  ElaborateSrc(kBareOuterReturnTypeSrc, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {13, 14, 24, 34}) {
    EXPECT_TRUE(
        ReportedError(diags, "has mismatched return type", kLine, "8.24"))
        << kLine;
  }
}

const char* const kSameNamedSubroutineSrc =
    "class UC; extern function int f(); extern task t(); endclass\n"
    "function int UC::f(); return 2; endfunction\n"
    "task UC::t(); endtask\n"
    "function int f(); return 1; endfunction\n"
    "task t(); endtask\n"
    "package p;\n"
    "  class PC; extern function int f(); endclass\n"
    "  function int PC::f(); return 4; endfunction\n"
    "  function int f(); return 3; endfunction\n"
    "endpackage\n"
    "interface ifc;\n"
    "  class IC; extern function int f(); endclass\n"
    "  function int IC::f(); return 6; endfunction\n"
    "  function int f(); return 5; endfunction\n"
    "endinterface\n"
    "module m;\n"
    "  class MC; extern function int f(); extern task t(); endclass\n"
    "  function int MC::f(); return 8; endfunction\n"
    "  task MC::t(); endtask\n"
    "  function int f(); return 7; endfunction\n"
    "  task t(); endtask\n"
    "  ifc i();\n"
    "  UC u = new;\n"
    "  MC c = new;\n"
    "  int r1, r2, r3, r4, r5, r6, r7;\n"
    "  initial begin\n"
    "    automatic p::PC pc = new;\n"
    "    r1 = $unit::f(); r2 = u.f(); r3 = p::f(); r4 = pc.f(); r5 = f(); r6 = "
    "c.f(); r7 = i.f();\n"
    "  end\n"
    "endmodule\n";

TEST(OutOfBlockDeclElaboration, UnitOrPackageSubroutineSharesAMethodsName) {
  ElabFixture f;
  ElaborateSrc(kSameNamedSubroutineSrc, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {4, 5, 9}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(OutOfBlockDeclElaboration,
     DISABLED_ModuleOrInterfaceSubroutineSharesAMethodsName) {
  ElabFixture f;
  ElaborateSrc(kSameNamedSubroutineSrc, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {14, 20, 21}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

const char* const kParameterBoundSignatureSrc =
    "module m #(int W = 4);\n"
    "  localparam int L = 4;\n"
    "  class C #(int V = 4);\n"
    "    extern function logic [W-1:0] f1();\n"
    "    extern function void f2(logic [W-1:0] a);\n"
    "    extern function void f3(logic [L-1:0] a);\n"
    "    extern function void f4(logic [V-1:0] a);\n"
    "    extern function void f5(int a[W]);\n"
    "    extern function logic [W-1:0] g1();\n"
    "    extern function void g2(logic [W-1:0] a);\n"
    "    extern function void g3(logic [L-1:0] a);\n"
    "    extern function void g4(logic [V-1:0] a);\n"
    "    extern function void g5(int a[W]);\n"
    "  endclass\n"
    "  function logic [W:0] C::f1(); return 0; endfunction\n"
    "  function void C::f2(logic [W:0] a); endfunction\n"
    "  function void C::f3(logic [L:0] a); endfunction\n"
    "  function void C::f4(logic [V:0] a); endfunction\n"
    "  function void C::f5(int a[W+1]); endfunction\n"
    "  function logic [3:0] C::g1(); return 0; endfunction\n"
    "  function void C::g2(logic [W-1:0] a); endfunction\n"
    "  function void C::g3(logic [3:0] a); endfunction\n"
    "  function void C::g4(logic [V-1:0] a); endfunction\n"
    "  function void C::g5(int a[4]); endfunction\n"
    "  for (genvar i = 2; i < 3; i++) begin : g\n"
    "    class D;\n"
    "      extern function void f(logic [i:0] a);\n"
    "      extern function void h(logic [i:0] a);\n"
    "    endclass\n"
    "    function void D::f(logic [i+1:0] a); endfunction\n"
    "    function void D::h(logic [2:0] a); endfunction\n"
    "  end\n"
    "endmodule\n";

TEST(OutOfBlockDeclElaboration, BoundsNamingParametersThatAgreeAreAccepted) {
  ElabFixture f;
  ElaborateSrc(kParameterBoundSignatureSrc, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {20, 21, 22, 23, 24, 31}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(OutOfBlockDeclElaboration,
     DISABLED_BoundsNamingParametersThatDifferAreReported) {
  ElabFixture f;
  ElaborateSrc(kParameterBoundSignatureSrc, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {15}) {
    EXPECT_TRUE(
        ReportedError(diags, "has mismatched return type", kLine, "8.24"))
        << kLine;
  }
  for (const int kLine : {16, 17, 18, 19, 30}) {
    EXPECT_TRUE(
        ReportedError(diags, "argument 'a' has mismatched type", kLine, "8.24"))
        << kLine;
  }
}

const char* const kForeignClassOutOfBlockSrc =
    "class Outer;\n"
    "  class Inner; extern function void m(); extern function void k(); "
    "endclass\n"
    "  function void Inner::k(); endfunction\n"
    "endclass\n"
    "class UC; extern function void m(); endclass\n"
    "function void Outer::Inner::m(); endfunction\n"
    "package p;\n"
    "  class PO; class PI; extern function void m(); endclass endclass\n"
    "  function void NoClass::m(); endfunction\n"
    "  function void PO::PI::m(); endfunction\n"
    "endpackage\n"
    "interface ifc;\n"
    "  class IO; class II; extern function void m(); endclass endclass\n"
    "  function void NoClass::m(); endfunction\n"
    "  function void IO::II::m(); endfunction\n"
    "endinterface\n"
    "program pr;\n"
    "  class RO; class RI; extern function void m(); endclass endclass\n"
    "  function void NoClass::m(); endfunction\n"
    "  function void RO::RI::m(); endfunction\n"
    "endprogram\n"
    "checker ck;\n"
    "  int kv;\n"
    "  function void NoClass::m(); endfunction\n"
    "  int kw;\n"
    "endchecker\n"
    "module m;\n"
    "  class MO; class MI; extern function void m(); endclass endclass\n"
    "  class MC; extern function void f(); endclass\n"
    "  function void NoClass::m(); endfunction\n"
    "  function void MO::MI::m(); endfunction\n"
    "  function void UC::m(); endfunction\n"
    "  function void MC::f(); endfunction\n"
    "  if (1) begin : g\n"
    "    function void MC::f(); endfunction\n"
    "    function void NoClass2::m(); endfunction\n"
    "  end\n"
    "  ifc i();\n"
    "  pr q();\n"
    "  ck c();\n"
    "endmodule\n";

TEST(OutOfBlockDeclElaboration, ForeignClassIsReportedInTheUnitAndAPackage) {
  ElabFixture f;
  ElaborateSrc(kForeignClassOutOfBlockSrc, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {6, 9, 10}) {
    EXPECT_TRUE(ReportedError(
        diags, "out-of-block declaration for unknown class", kLine, "8.24"))
        << kLine;
  }
  for (const int kLine : {3, 33}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(OutOfBlockDeclElaboration,
     DISABLED_ForeignClassIsReportedInEveryOtherScope) {
  ElabFixture f;
  ElaborateSrc(kForeignClassOutOfBlockSrc, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {14, 15, 19, 20, 24, 30, 31, 32, 35, 36}) {
    EXPECT_TRUE(
        ReportedError(diags, "out-of-block declaration for", kLine, "8.24"))
        << kLine;
  }
}

}  // namespace
