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

}  // namespace
