#include <gtest/gtest.h>

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

}  // namespace
