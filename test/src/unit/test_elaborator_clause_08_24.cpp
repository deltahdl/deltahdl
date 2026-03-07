#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §8.24: Out-of-block function with matching extern prototype — OK.
TEST(ElabA824, OutOfBlockFuncOk) {
  EXPECT_TRUE(ElabOk(
      "class C;\n"
      "  extern function int foo();\n"
      "endclass\n"
      "function int C::foo();\n"
      "  return 42;\n"
      "endfunction\n"
      "module m;\n"
      "endmodule\n"));
}

// §8.24: Out-of-block task with matching extern prototype — OK.
TEST(ElabA824, OutOfBlockTaskOk) {
  EXPECT_TRUE(ElabOk(
      "class C;\n"
      "  extern task run();\n"
      "endclass\n"
      "task C::run();\n"
      "endtask\n"
      "module m;\n"
      "endmodule\n"));
}

// §8.24: Out-of-block declaration for unknown class — error.
TEST(ElabA824, UnknownClassError) {
  EXPECT_FALSE(ElabOk(
      "function int UnknownClass::foo();\n"
      "  return 0;\n"
      "endfunction\n"
      "module m;\n"
      "endmodule\n"));
}

// §8.24: Out-of-block declaration without matching extern — error.
TEST(ElabA824, NoMatchingExternError) {
  EXPECT_FALSE(ElabOk(
      "class C;\n"
      "  function int bar(); endfunction\n"
      "endclass\n"
      "function int C::foo();\n"
      "  return 0;\n"
      "endfunction\n"
      "module m;\n"
      "endmodule\n"));
}

// §8.24: Duplicate out-of-block declaration — error.
TEST(ElabA824, DuplicateOutOfBlockError) {
  EXPECT_FALSE(ElabOk(
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
      "endmodule\n"));
}

// §8.24: Out-of-block constructor — OK.
TEST(ElabA824, OutOfBlockConstructorOk) {
  EXPECT_TRUE(ElabOk(
      "class C;\n"
      "  extern function new();\n"
      "endclass\n"
      "function C::new();\n"
      "endfunction\n"
      "module m;\n"
      "endmodule\n"));
}

// §8.24: Class without extern methods, no out-of-block — OK.
TEST(ElabA824, NoExternNoOutOfBlockOk) {
  EXPECT_TRUE(ElabOk(
      "class C;\n"
      "  function int foo(); endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

}  // namespace
