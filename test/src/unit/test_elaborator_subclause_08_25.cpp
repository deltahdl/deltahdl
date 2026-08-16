#include "fixture_elaborator.h"
#include "helpers_child_instance.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

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
  ElabFixture f;
  ElabOk(
      "class D #(int p);\n"
      "  int data;\n"
      "endclass\n"
      "module m;\n"
      "  D obj;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "has no default specialization; parameter", 5,
                            "8.25"));
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

// §23.10.2.2 binds a named parameter argument to the formal it names, so `byte`
// reaches T2 although T2 is declared second and the argument is written first.
// The width says which formal it reached: T1's default is int at 32 bits and
// T2's is bit at 1 bit, so only `byte` landing on T2 gives elem_t 8 bits.
//
// This case alone passes wrongly for an elaborator that ignores the name and
// gives elem_t whatever type the specialization mentions, which is what
// OmittedNamedTypeArgumentKeepsItsDeclaredDefault below rules out.
TEST(ParameterizedClassElaboration, NamedTypeArgumentReachesTheFormalItNames) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Buf #(type T1 = int, type T2 = bit);\n"
      "  typedef T2 elem_t;\n"
      "endclass\n"
      "module m;\n"
      "  Buf#(.T2(byte))::elem_t v;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectVariableWidth(FindModule(design, "m"), "v", 8u);
}

// §23.10.2.2 requires only the parameters being given new values to be
// specified, so naming T1 alone leaves T2 at its declared default of bit and
// elem_t 1 bit wide. The 8 bits of `byte` and the 32 of T1's own default are
// both distinct from 1, so neither reaching elem_t can be mistaken for this.
//
// This case alone passes wrongly for an elaborator that discards every named
// argument and defaults the whole specialization, which is what
// NamedTypeArgumentReachesTheFormalItNames above rules out.
TEST(ParameterizedClassElaboration,
     OmittedNamedTypeArgumentKeepsItsDeclaredDefault) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Buf #(type T1 = int, type T2 = bit);\n"
      "  typedef T2 elem_t;\n"
      "endclass\n"
      "module m;\n"
      "  Buf#(.T1(byte))::elem_t v;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectVariableWidth(FindModule(design, "m"), "v", 1u);
}

// Both formals are named, in the reverse of the order the class declares them,
// so §23.10.2.2's binding by name is the only rule that puts `byte` on T2 and
// `shortint` on T1. An elaborator binding these two arguments by the position
// they are written in gives T2 shortint and elem_t 16 bits, and one taking the
// last argument mentioned gives the same 16, so 8 is reachable only by name.
TEST(ParameterizedClassElaboration,
     NamedTypeArgumentsResolveOutOfDeclarationOrder) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Buf #(type T1 = int, type T2 = bit);\n"
      "  typedef T2 elem_t;\n"
      "endclass\n"
      "module m;\n"
      "  Buf#(.T2(byte), .T1(shortint))::elem_t v;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectVariableWidth(FindModule(design, "m"), "v", 8u);
}

}  // namespace
