#include "fixture_elaborator.h"

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
  EXPECT_FALSE(
      ElabOk("function int UnknownClass::foo();\n"
             "  return 0;\n"
             "endfunction\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(OutOfBlockDeclElaboration, NoMatchingExternError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  function int bar(); endfunction\n"
             "endclass\n"
             "function int C::foo();\n"
             "  return 0;\n"
             "endfunction\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(OutOfBlockDeclElaboration, DuplicateOutOfBlockError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  extern function int foo();\n"
             "endclass\n"
             "function int C::foo();\n"
             "  return 42;\n"
             "endfunction\n"
             "function int C::foo();\n"
             "  return 99;\n"
             "endfunction\n"
             "module m;\n"
             "endmodule\n"));
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
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  extern task run();\n"
             "endclass\n"
             "task C::run();\n"
             "endtask\n"
             "task C::run();\n"
             "endtask\n"
             "module m;\n"
             "endmodule\n"));
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
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  function int foo();\n"
             "    return 0;\n"
             "  endfunction\n"
             "endclass\n"
             "function int C::foo();\n"
             "  return 1;\n"
             "endfunction\n"
             "module m;\n"
             "endmodule\n"));
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
  EXPECT_FALSE(
      ElabOk("task NoSuchClass::run();\n"
             "endtask\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(OutOfBlockDeclElaboration, MismatchedArgCountError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  extern function int foo(int a);\n"
             "endclass\n"
             "function int C::foo(int a, int b);\n"
             "  return a + b;\n"
             "endfunction\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(OutOfBlockDeclElaboration, MismatchedArgTypeError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  extern function int foo(int a);\n"
             "endclass\n"
             "function int C::foo(real a);\n"
             "  return 0;\n"
             "endfunction\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(OutOfBlockDeclElaboration, MismatchedReturnTypeError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  extern function int foo();\n"
             "endclass\n"
             "function real C::foo();\n"
             "  return 1.0;\n"
             "endfunction\n"
             "module m;\n"
             "endmodule\n"));
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
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  extern function void foo(input int a);\n"
             "endclass\n"
             "function void C::foo(output int a);\n"
             "endfunction\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.24: matching the prototype exactly includes the method kind; a task body
// for a function prototype (or vice versa) is an error.
TEST(OutOfBlockDeclElaboration, MismatchedMethodKindError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  extern function int foo();\n"
             "endclass\n"
             "task C::foo();\n"
             "endtask\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.24: a default argument value specified in the prototype may be omitted in
// the out-of-block declaration.
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

// §8.24: a default argument value repeated in the out-of-block declaration must
// be syntactically identical to the prototype's.
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

// §8.24: a differing default argument value in the out-of-block declaration is
// an error.
TEST(OutOfBlockDeclElaboration, DefaultArgRepeatedMismatchError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  extern function int foo(int a = 5);\n"
             "endclass\n"
             "function int C::foo(int a = 6);\n"
             "  return a;\n"
             "endfunction\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.24: a default argument value in the out-of-block declaration with none in
// the prototype is an error.
TEST(OutOfBlockDeclElaboration, DefaultArgOnlyInBodyError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  extern function int foo(int a);\n"
             "endclass\n"
             "function int C::foo(int a = 5);\n"
             "  return a;\n"
             "endfunction\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.24: the repeated default value comparison is structural, so an identical
// compound expression on both sides is accepted.
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

// §8.24: identity is syntactic rather than value-based, so two defaults that
// evaluate to the same number but are written differently do not match.
TEST(OutOfBlockDeclElaboration, DefaultArgSameValueDifferentSyntaxError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  extern function int foo(int a = 2);\n"
             "endclass\n"
             "function int C::foo(int a = 1 + 1);\n"
             "  return a;\n"
             "endfunction\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.24: an out-of-block declaration shall follow the class declaration.
TEST(OutOfBlockDeclElaboration, OutOfBlockBeforeClassError) {
  EXPECT_FALSE(
      ElabOk("function int C::foo();\n"
             "  return 0;\n"
             "endfunction\n"
             "class C;\n"
             "  extern function int foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
