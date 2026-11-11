#include <gtest/gtest.h>

#include <initializer_list>

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

TEST(ParameterizedClassElaboration, ExplicitOverrideForNoDefaultClassOk) {
  EXPECT_TRUE(
      ElabOk("class D #(int p);\n"
             "  int data;\n"
             "endclass\n"
             "module m;\n"
             "  D #(4) obj;\n"
             "endmodule\n"));
}

TEST(ParameterizedClassElaboration, MixedDefaultPartialOverrideOk) {
  EXPECT_TRUE(
      ElabOk("class C #(int a, int b = 2);\n"
             "  int data;\n"
             "endclass\n"
             "module m;\n"
             "  C #(5) c;\n"
             "endmodule\n"));
}

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

TEST(ParameterizedClassElaboration, ForwardedFormalValueArgumentInExtendsOk) {
  EXPECT_TRUE(
      ElabOk("class C #(int P = 1);\n"
             "  int data;\n"
             "endclass\n"
             "class D #(int N = 4) extends C#(N);\n"
             "endclass\n"));
}

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

TEST(ParameterizedClassElaboration, TypeParameterWithoutDefaultHasNoDefault) {
  ElabFixture f;
  ElabOk(
      "class D #(type T);\n"
      "  T x;\n"
      "endclass\n"
      "module m;\n"
      "  D obj;\n"
      "  D #(int) ok;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameterized class 'D' has no default "
                            "specialization; parameter 'T' has no default "
                            "value",
                            5, "8.25"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "has no default", 6, "8.25"));
}

TEST(ParameterizedClassElaboration, NoDefaultSpecializationInEveryDeclaration) {
  ElabFixture f;
  ElabOk(
      "class D #(int p);\n"
      "endclass\n"
      "class H;\n"
      "  D prop;\n"
      "  function D get(D arg); return arg; endfunction\n"
      "  D #(3) ok;\n"
      "endclass\n"
      "class E extends D; endclass\n"
      "typedef D d_t;\n"
      "D cu_var;\n"
      "package q;\n"
      "  D pkg_var;\n"
      "endpackage\n"
      "module m;\n"
      "  initial begin D blk; end\n"
      "endmodule\n",
      f);
  for (const int kLine : {4, 5, 8, 9, 10, 12, 15}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "parameterized class 'D' has no default "
                              "specialization; parameter 'p' has no default "
                              "value",
                              kLine, "8.25"))
        << kLine;
  }
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "has no default", 6, "8.25"));
}

TEST(ParameterizedClassElaboration, ABaseResolvingToNoClassIsAnError) {
  ElabFixture f;
  ElabOk(
      "typedef int T;\n"
      "class B; endclass\n"
      "typedef B b_t;\n"
      "class A extends Nonexistent; endclass\n"
      "class X extends T; endclass\n"
      "class Y extends b_t; endclass\n"
      "class M extends mailbox #(int); endclass\n"
      "class C #(int N = 1, type P = int) extends P; endclass\n"
      "module m;\n"
      "  C c;\n"
      "  C #(1, B) cb;\n"
      "  G g;\n"
      "endmodule\n"
      "class G #(type Q) extends Q; endclass\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "class 'A' extends 'Nonexistent', which nothing declares", 4,
      "8.13"));
  EXPECT_TRUE(ReportedError(
      diags, "class 'X' extends 'T', a typedef of a type that is no class", 5,
      "8.25"));
  const char* const kSpecialization =
      "this specialization of 'C' gives its type parameter 'P', the class it "
      "extends, a type that is no class";
  EXPECT_TRUE(ReportedError(diags, kSpecialization, 10, "8.25"));
  EXPECT_FALSE(ReportedError(diags, kSpecialization, 11, "8.25"));
  EXPECT_TRUE(ReportedError(diags,
                            "parameterized class 'G' has no default "
                            "specialization; parameter 'Q' has no default "
                            "value",
                            12, "8.25"));
  EXPECT_FALSE(ReportedError(diags, "this specialization of 'G'", 12, "8.25"));
  for (const int kLine : {6, 7, 8}) {
    EXPECT_FALSE(ReportedError(diags, "extends", kLine, "8.13")) << kLine;
    EXPECT_FALSE(ReportedError(diags, "extends", kLine, "8.25")) << kLine;
  }
}

const char* const kNonMatchingSpecializationSrc =
    "class vector #(int size = 1); bit [size-1:0] a; endclass\n"
    "class stack #(type T = int); T items[$]; endclass\n"
    "class vb #(type VT = int, VT p = 1); endclass\n"
    "class dv extends vector #(4); endclass\n"
    "typedef int myint;\n"
    "function vector #(5) ret5(vector #(4) h); return h; endfunction\n"
    "function vector #(4) ret4(vector #(4) h); return h; endfunction\n"
    "function void take5(vector #(5) h); endfunction\n"
    "function void take4(vector #(4) h); endfunction\n"
    "module top;\n"
    "  vector #(4) a;\n"
    "  vector #(5) b;\n"
    "  vector #(2+2) c;\n"
    "  vector d0;\n"
    "  vector #(1) d;\n"
    "  stack #(int) s;\n"
    "  stack #(integer) t;\n"
    "  stack #(int) u;\n"
    "  stack #(myint) w;\n"
    "  stack #(bit [7:0]) x;\n"
    "  stack #(bit [8:1]) y;\n"
    "  stack #(byte) bb;\n"
    "  stack #(bit signed [7:0]) bs;\n"
    "  vb #(shortint, 1) v1;\n"
    "  vb #(int, 1) v2;\n"
    "  vb #(int, 1) v3;\n"
    "  dv e;\n"
    "  initial begin\n"
    "    b = a;\n"
    "    c = a;\n"
    "    d = d0;\n"
    "    t = s;\n"
    "    u = s;\n"
    "    w = s;\n"
    "    y = x;\n"
    "    bs = bb;\n"
    "    v2 = v1;\n"
    "    v3 = v2;\n"
    "    take5(a);\n"
    "    take4(a);\n"
    "    a = e;\n"
    "    b = e;\n"
    "  end\n"
    "endmodule\n";

TEST(ParameterizedClassElaboration,
     MatchingSpecializationsAssignWithoutReport) {
  ElabFixture f;
  ElaborateSrc(kNonMatchingSpecializationSrc, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {7, 30, 31, 33, 34, 36, 38, 40, 41}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(ParameterizedClassElaboration,
     DISABLED_NonMatchingSpecializationsAreDistinctTypes) {
  ElabFixture f;
  ElaborateSrc(kNonMatchingSpecializationSrc, f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {29, 32, 35, 37, 42}) {
    EXPECT_TRUE(ReportedError(diags, "requires assignment compatible types",
                              kLine, "8.4"))
        << kLine;
  }
  for (const int kLine : {39}) {
    EXPECT_TRUE(ReportedError(diags, "assignment compatible", kLine, "13.5"))
        << kLine;
  }
  for (const int kLine : {6}) {
    EXPECT_TRUE(ReportedError(
        diags, "is not assignment-compatible with the function's return type",
        kLine, "12.8"))
        << kLine;
  }
}

TEST(ParameterizedClassElaboration,
     SpecializationOfAModulesClassDiffersPerInstanceButNotFromAPackage) {
  ElabFixture f;
  ElaborateSrc(
      "package pk;\n"
      "  class PCl #(int n = 1); endclass\n"
      "endpackage\n"
      "module sub;\n"
      "  class C #(int n = 1); endclass\n"
      "  C #(4) h;\n"
      "  pk::PCl #(4) ph;\n"
      "endmodule\n"
      "module top;\n"
      "  sub u1();\n"
      "  sub u2();\n"
      "  initial begin\n"
      "    u2.h = u1.h;\n"
      "    u2.ph = u1.ph;\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags,
                            "'u2.h' and 'u1.h' have types the instances 'u2' "
                            "and 'u1' each declare for themselves",
                            13, "6.22"));
  EXPECT_FALSE(ErrorOnLine(diags, 14));
}

}  // namespace
