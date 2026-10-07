#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_child_instance.h"
#include "helpers_param_value.h"
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

// §23.10.2.2 states that the parameter named must be one the instantiated
// module declares, and §8.25 applies the same parameter override rules to a
// class specialization, so `.Nope` names no parameter of Buf and the
// specialization is illegal. An elaborator that drops an argument whose name it
// cannot find accepts the source and leaves T2 at its declared default of bit,
// giving v 1 bit rather than saying the name is wrong.
TEST(ParameterizedClassElaboration,
     NamedArgumentNamingNoClassParameterIsError) {
  ElabFixture f;
  ElabOk(
      "class Buf #(type T1 = int, type T2 = bit);\n"
      "  typedef T2 elem_t;\n"
      "endclass\n"
      "module m;\n"
      "  Buf#(.Nope(byte))::elem_t v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'Buf' has no parameter 'Nope'", 5,
                            "23.10.2.2"));
}

// §23.10.2.2 states that a parameter given a value may not be assigned again
// under that name, so naming T2 twice in one specialization is illegal. An
// elaborator that lets each named argument overwrite the last accepts the
// source and gives T2 shortint, making v 16 bits from whichever argument was
// written last rather than reporting the repeat.
TEST(ParameterizedClassElaboration, NamedClassParameterAssignedTwiceIsError) {
  ElabFixture f;
  ElabOk(
      "class Buf #(type T1 = int, type T2 = bit);\n"
      "  typedef T2 elem_t;\n"
      "endclass\n"
      "module m;\n"
      "  Buf#(.T2(byte), .T2(shortint))::elem_t v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter 'T2' of class 'Buf' is assigned more "
                            "than once",
                            5, "23.10.2.2"));
}

// §8.25 instantiates a parameterized class object "using the same parameter
// override rules (see 23.10)", and §23.10.2 gives a parameter override a
// constant expression as its value, so the module variable `v` is not a legal
// argument of the specialization `C#(v)`. An elaborator that folds the argument
// only where a later constant expression happens to read it accepts this
// declaration and carries C's own default of 1 in place of the value the source
// wrote, so the report is the only thing that says the source is wrong.
TEST(ParameterizedClassElaboration,
     NonConstantValueArgumentInDeclarationIsError) {
  ElabFixture f;
  ElabOk(
      "class C #(int P = 1);\n"
      "  int data;\n"
      "endclass\n"
      "module m;\n"
      "  int v;\n"
      "  C#(v) c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'C' parameter override is not a constant", 6,
                            "23.10.2"));
}

// A localparam is a constant expression per §6.20.2, so `C#(K)` is a legal
// specialization and the rejection above is specific to an argument that is not
// one. Without this case the cheapest way to pass
// NonConstantValueArgumentInDeclarationIsError is to reject every value
// argument. K is 4 rather than C's own default of 1, so the argument the source
// wrote is the value that has to fold here.
TEST(ParameterizedClassElaboration,
     ConstantLocalparamValueArgumentInDeclarationOk) {
  EXPECT_TRUE(
      ElabOk("class C #(int P = 1);\n"
             "  int data;\n"
             "endclass\n"
             "module m;\n"
             "  localparam int K = 4;\n"
             "  C#(K) c;\n"
             "endmodule\n"));
}

// The same rule over an extends clause rather than a declaration. §8.25 rules
// that instances of a parameterized class are instantiated "using the same
// parameter override rules (see 23.10)" (printed page 203), and §23.10.2 gives
// an override a constant expression, so the module variable `v` is not a legal
// argument of `C#(v)` wherever the specialization is written.
// Elaborator::ValidateSpecializationArgsConstant reports the declaration form
// at elaborator_decls_var.cpp and reaches no inheritance clause, so nothing
// said this source was wrong: the class silently took C's own default of 1 in
// place of the value the source wrote.
TEST(ParameterizedClassElaboration, NonConstantValueArgumentInExtendsIsError) {
  ElabFixture f;
  ElabOk(
      "class C #(int P = 1);\n"
      "  int data;\n"
      "endclass\n"
      "module m;\n"
      "  int v;\n"
      "  class D extends C#(v);\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'C' parameter override is not a constant", 6,
                            "23.10.2"));
}

// §6.20.1 gives a class's own formal value parameter no value until the class
// is specialized, so `N` here is not an argument that failed to be constant and
// the report above must not fire on it. Without this case the obvious
// implementation of that report -- reject every argument that does not fold --
// passes every other test in this file and rejects a legal source.
TEST(ParameterizedClassElaboration, ForwardedFormalValueArgumentInExtendsOk) {
  EXPECT_TRUE(
      ElabOk("class C #(int P = 1);\n"
             "  int data;\n"
             "endclass\n"
             "class D #(int N = 4) extends C#(N);\n"
             "endclass\n"));
}

// The false positive the report must not produce, and the reason the fold and
// the report are one change. `K` is declared in the module the class is
// declared in, which is a scope Elaborator::cu_param_scope_ does not hold, so a
// report added without ScopeParamValues rejects this legal source. K is 4
// rather than C's own default of 1, so the argument has a value distinct from
// what accepting it silently would leave behind.
TEST(ParameterizedClassElaboration, ModuleLocalparamValueArgumentInExtendsOk) {
  EXPECT_TRUE(
      ElabOk("class C #(int P = 1);\n"
             "  int data;\n"
             "endclass\n"
             "module m;\n"
             "  localparam int K = 4;\n"
             "  class D extends C#(K);\n"
             "  endclass\n"
             "endmodule\n"));
}

// §8.25 gives each specialization its own parameter values, and §6.20.1 lets a
// parameter depend on earlier ones, so the class body localparam `N` and the
// header's `M` are both `W * 2` with the specialization's `W`: 8 in `C#(4)`,
// 16 in the default and 6 under the named override `.W(3)`, and `M` written
// out as 5 in `C#(4, 5)` is 5. Each is folded at elaboration as the
// right-hand side of a module localparam. This fails on a fold that reads a
// parameter the list does not override with the class's default `W = 8` in
// scope, which answered 16 wherever it read `W * 2`.
TEST(ParameterizedClassElaboration,
     ParameterThroughASpecializationFoldsWithItsParameters) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C #(int W = 8, int M = W * 2);\n"
      "  localparam int N = W * 2;\n"
      "endclass\n"
      "module m;\n"
      "  localparam int X = C#(4)::N;\n"
      "  localparam int Y = C#()::N;\n"
      "  localparam int Z = C#(.W(3))::N;\n"
      "  localparam int A = C#(4)::M;\n"
      "  localparam int B = C#(4, 5)::M;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "X"), 8);
  EXPECT_EQ(ParamValue(design, "Y"), 16);
  EXPECT_EQ(ParamValue(design, "Z"), 6);
  EXPECT_EQ(ParamValue(design, "A"), 8);
  EXPECT_EQ(ParamValue(design, "B"), 5);
}

// §6.20.1 with §8.25: a class parameter declared with unpacked dimensions is
// an array of constants, assigned by a pattern whose items, nested for a second
// dimension or real for a real element, are each constant, or by another
// parameter array; the pattern is no one integer, and is not judged as one.
TEST(ParameterizedClassElaboration, ParameterArrayOfConstantsOk) {
  ElabFixture f;
  ElabOk(
      "class C #(parameter int P[2] = '{3, 4});\n"
      "  parameter int A[2] = '{1, 2};\n"
      "  localparam int M[2][2] = '{'{1, 2}, '{3, 4}};\n"
      "  localparam real R[2] = '{1.5, 0.25};\n"
      "  localparam int K[3] = '{default: 7};\n"
      "  localparam int B[2] = A;\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// An item of the pattern that is no constant expression is reported, as a
// scalar parameter's value would be.
TEST(ParameterizedClassElaboration, ParameterArrayItemNotConstantIsError) {
  ElabFixture f;
  ElabOk(
      "int g;\n"
      "class C;\n"
      "  parameter int A[2] = '{1, g};\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class parameter 'A' value is not a constant "
                            "expression",
                            3, "6.20.2"));
}

}  // namespace
