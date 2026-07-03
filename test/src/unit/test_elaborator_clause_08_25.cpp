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

TEST(ParameterizedClassElaboration, ExplicitDefaultSpecializationOk) {
  EXPECT_TRUE(
      ElabOk("class C #(int p = 1);\n"
             "  int data;\n"
             "endclass\n"
             "module m;\n"
             "  C #() obj;\n"
             "endmodule\n"));
}

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

// A parameterized class whose value parameter has no default has no default
// specialization, so using its unadorned name as a type is illegal (the LRM's
// "D obj;" example).
TEST(ParameterizedClassElaboration, NoDefaultSpecializationUnadornedIsError) {
  EXPECT_FALSE(
      ElabOk("class D #(int p);\n"
             "  int data;\n"
             "endclass\n"
             "module m;\n"
             "  D obj;\n"
             "endmodule\n"));
}

// The same class supplied with an explicit parameter has a concrete
// specialization and elaborates, confirming the rejection above is specific to
// the missing default specialization rather than to the class itself.
TEST(ParameterizedClassElaboration, ExplicitOverrideForNoDefaultClassOk) {
  EXPECT_TRUE(
      ElabOk("class D #(int p);\n"
             "  int data;\n"
             "endclass\n"
             "module m;\n"
             "  D #(4) obj;\n"
             "endmodule\n"));
}

// §8.25: when only some parameters have defaults, a specialization must supply
// values for the ones without defaults. Overriding the defaultless parameter
// while letting the rest default is legal (contrast
// NoDefaultSpecializationUnadornedIsError, which omits the required override).
TEST(ParameterizedClassElaboration, MixedDefaultPartialOverrideOk) {
  EXPECT_TRUE(
      ElabOk("class C #(int a, int b = 2);\n"
             "  int data;\n"
             "endclass\n"
             "module m;\n"
             "  C #(5) c;\n"
             "endmodule\n"));
}

}  // namespace
