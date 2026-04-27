#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParameterizedClassElaboration, ValueParamClassOk) {
  EXPECT_TRUE(
      ElabOk("class stack #(parameter int DEPTH = 8);\n"
             "  int data;\n"
             "endclass\n"
             "module m;\n"
             "  stack s;\n"
             "endmodule\n"));
}

TEST(ParameterizedClassElaboration, TypeParamClassOk) {
  EXPECT_TRUE(
      ElabOk("class container #(type T = int);\n"
             "  T data;\n"
             "endclass\n"
             "module m;\n"
             "  container c;\n"
             "endmodule\n"));
}

TEST(ParameterizedClassElaboration, MultipleParamsOk) {
  EXPECT_TRUE(ElabOk(
      "class fifo #(parameter int WIDTH = 8, parameter int DEPTH = 16);\n"
      "  bit [WIDTH-1:0] data;\n"
      "endclass\n"
      "module m;\n"
      "  fifo f;\n"
      "endmodule\n"));
}

TEST(ParameterizedClassElaboration, ExplicitSpecializationOk) {
  EXPECT_TRUE(
      ElabOk("class vector #(int size = 1);\n"
             "  bit [size-1:0] a;\n"
             "endclass\n"
             "module m;\n"
             "  vector #(10) vten;\n"
             "endmodule\n"));
}

TEST(ParameterizedClassElaboration, ParamClassExtendsBaseOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  int x;\n"
             "endclass\n"
             "class Derived #(parameter int N = 4) extends Base;\n"
             "  int y;\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

TEST(ParameterizedClassElaboration, ParamClassExtendsParamBaseOk) {
  EXPECT_TRUE(
      ElabOk("class C #(type T = int);\n"
             "  T data;\n"
             "endclass\n"
             "class D #(type P = int) extends C;\n"
             "  P extra;\n"
             "endclass\n"
             "module m;\n"
             "  D d;\n"
             "endmodule\n"));
}

TEST(ParameterizedClassElaboration, DefaultSpecializationOk) {
  EXPECT_TRUE(
      ElabOk("class stack #(type T = int);\n"
             "  T items;\n"
             "endclass\n"
             "module m;\n"
             "  stack is_default;\n"
             "endmodule\n"));
}

// §8.25: typedef for specialization elaborates.
TEST(ParameterizedClassElaboration, TypedefSpecializationOk) {
  EXPECT_TRUE(
      ElabOk("class vector #(int size = 1);\n"
             "  bit [size-1:0] a;\n"
             "endclass\n"
             "typedef vector#(4) Vfour;\n"
             "module m;\n"
             "  Vfour v;\n"
             "endmodule\n"));
}

// §8.25: Extending parameterized base with explicit #(...) params.
TEST(ParameterizedClassElaboration, ExtendsParameterizedBaseOk) {
  EXPECT_TRUE(
      ElabOk("class C #(type T = bit);\n"
             "  T data;\n"
             "endclass\n"
             "class D #(type P = real) extends C #(integer);\n"
             "  P extra;\n"
             "endclass\n"
             "module m;\n"
             "  D d;\n"
             "endmodule\n"));
}

// §8.25: Forwarding type param to parameterized base.
TEST(ParameterizedClassElaboration, ExtendsBaseForwardingTypeParamOk) {
  EXPECT_TRUE(
      ElabOk("class C #(type T = bit);\n"
             "  T data;\n"
             "endclass\n"
             "class D #(type P = real) extends C #(P);\n"
             "  P extra;\n"
             "endclass\n"
             "module m;\n"
             "  D d;\n"
             "endmodule\n"));
}

// §8.25: Type parameter used as base class name.
TEST(ParameterizedClassElaboration, TypeParamAsBaseClassOk) {
  EXPECT_TRUE(
      ElabOk("class C #(type T = bit);\n"
             "endclass\n"
             "class D #(type P = C#(real)) extends P;\n"
             "endclass\n"
             "module m;\n"
             "  D d;\n"
             "endmodule\n"));
}

// §8.25: Mixed type and value parameters.
TEST(ParameterizedClassElaboration, MixedTypeAndValueParamsOk) {
  EXPECT_TRUE(
      ElabOk("class C #(type T = int, parameter int N = 8);\n"
             "  T data;\n"
             "  bit [N-1:0] flags;\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

// §8.25: Explicit default specialization #() syntax.
TEST(ParameterizedClassElaboration, ExplicitDefaultSpecializationOk) {
  EXPECT_TRUE(
      ElabOk("class C #(int p = 1);\n"
             "  int data;\n"
             "endclass\n"
             "module m;\n"
             "  C #() obj;\n"
             "endmodule\n"));
}

// §8.25: User-defined type (struct) as type parameter.
TEST(ParameterizedClassElaboration, StructTypeParamOk) {
  EXPECT_TRUE(
      ElabOk("typedef struct { int x; int y; } point_t;\n"
             "class container #(type T = point_t);\n"
             "  T value;\n"
             "endclass\n"
             "module m;\n"
             "  container c;\n"
             "endmodule\n"));
}

// §8.25: Class type as type parameter argument.
TEST(ParameterizedClassElaboration, ClassAsTypeParamArgOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int data;\n"
             "endclass\n"
             "class stack #(type T = int);\n"
             "  T items;\n"
             "endclass\n"
             "module m;\n"
             "  stack #(Packet) ps;\n"
             "endmodule\n"));
}

// §8.25: Static member in parameterized class elaborates.
TEST(ParameterizedClassElaboration, StaticMemberInParamClassOk) {
  EXPECT_TRUE(
      ElabOk("class vector #(int size = 1);\n"
             "  bit [size-1:0] a;\n"
             "  static int count = 0;\n"
             "endclass\n"
             "module m;\n"
             "  vector #(10) v;\n"
             "endmodule\n"));
}

// §8.25: Multiple different specializations in the same module.
TEST(ParameterizedClassElaboration, MultipleSpecializationsOk) {
  EXPECT_TRUE(
      ElabOk("class vector #(int size = 1);\n"
             "  bit [size-1:0] a;\n"
             "endclass\n"
             "module m;\n"
             "  vector #(8) v8;\n"
             "  vector #(16) v16;\n"
             "  vector #(32) v32;\n"
             "endmodule\n"));
}

// §8.25: Typedef chain through parameterized specialization.
TEST(ParameterizedClassElaboration, TypedefChainedSpecializationOk) {
  EXPECT_TRUE(
      ElabOk("class vector #(int size = 1);\n"
             "  bit [size-1:0] a;\n"
             "endclass\n"
             "typedef vector#(4) Vfour;\n"
             "class stack #(type T = int);\n"
             "  T items;\n"
             "endclass\n"
             "typedef stack#(Vfour) Stack4;\n"
             "module m;\n"
             "  Stack4 s;\n"
             "endmodule\n"));
}

}  // namespace
