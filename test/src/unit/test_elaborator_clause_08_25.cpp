#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §8.25: Parameterized class with value parameter — elaborates OK.
TEST(ElabA825, ValueParamClassOk) {
  EXPECT_TRUE(ElabOk(
      "class stack #(parameter int DEPTH = 8);\n"
      "  int data;\n"
      "endclass\n"
      "module m;\n"
      "  stack s;\n"
      "endmodule\n"));
}

// §8.25: Parameterized class with type parameter — elaborates OK.
TEST(ElabA825, TypeParamClassOk) {
  EXPECT_TRUE(ElabOk(
      "class container #(type T = int);\n"
      "  T data;\n"
      "endclass\n"
      "module m;\n"
      "  container c;\n"
      "endmodule\n"));
}

// §8.25: Parameterized class with multiple parameters — elaborates OK.
TEST(ElabA825, MultipleParamsOk) {
  EXPECT_TRUE(ElabOk(
      "class fifo #(parameter int WIDTH = 8, parameter int DEPTH = 16);\n"
      "  bit [WIDTH-1:0] data;\n"
      "endclass\n"
      "module m;\n"
      "  fifo f;\n"
      "endmodule\n"));
}

// §8.25: Parameterized class with explicit specialization — elaborates OK.
TEST(ElabA825, ExplicitSpecializationOk) {
  EXPECT_TRUE(ElabOk(
      "class vector #(int size = 1);\n"
      "  bit [size-1:0] a;\n"
      "endclass\n"
      "module m;\n"
      "  vector #(10) vten;\n"
      "endmodule\n"));
}

// §8.25: Parameterized class extending non-parameterized base — OK.
TEST(ElabA825, ParamClassExtendsBaseOk) {
  EXPECT_TRUE(ElabOk(
      "class Base;\n"
      "  int x;\n"
      "endclass\n"
      "class Derived #(parameter int N = 4) extends Base;\n"
      "  int y;\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n"));
}

// §8.25: Parameterized class extending parameterized base — OK.
TEST(ElabA825, ParamClassExtendsParamBaseOk) {
  EXPECT_TRUE(ElabOk(
      "class C #(type T = int);\n"
      "  T data;\n"
      "endclass\n"
      "class D #(type P = int) extends C;\n"
      "  P extra;\n"
      "endclass\n"
      "module m;\n"
      "  D d;\n"
      "endmodule\n"));
}

// §8.25: Default specialization uses default parameters.
TEST(ElabA825, DefaultSpecializationOk) {
  EXPECT_TRUE(ElabOk(
      "class stack #(type T = int);\n"
      "  T items;\n"
      "endclass\n"
      "module m;\n"
      "  stack is_default;\n"
      "endmodule\n"));
}

}  // namespace
