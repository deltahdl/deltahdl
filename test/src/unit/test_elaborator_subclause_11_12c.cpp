#include <gtest/gtest.h>

#include <cstdint>
#include <format>
#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kNotCastCompatible =
    "is not cast compatible with the type of formal";

TEST(LetActualScopeElaboration, AUnitArrayTypedefsVariableIsAnArray) {
  ElabFixture f;
  ElaborateSrc(
      "typedef int arr_t [2];\n"
      "arr_t v; int i;\n"
      "let p(arr_t x) = x[0];\n"
      "function automatic int c(); arr_t w; return p(w) + p(v); endfunction\n"
      "module m;\n"
      "  let q(arr_t x) = x[1];\n"
      "  initial $display(\"%0d\", p(v) + q(v) + c());\n"
      "  initial $display(\"%0d\", p(i));\n"
      "endmodule\n",
      f);
  for (uint32_t line : {4u, 7u}) {
    EXPECT_FALSE(
        ReportedError(f.diag.Diagnostics(), kNotCastCompatible, line, "11.12"));
  }
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 8, "11.12"));
}

TEST(LetActualScopeElaboration, ImportsAreSearchedScopeByScope) {
  ElabFixture f;
  ElaborateSrc(
      "package p; let f(int x) = x; endpackage\n"
      "package q; let f(x) = x; endpackage\n"
      "package r; let g(int x) = x; endpackage\n"
      "import p::f;\n"
      "import r::*;\n"
      "let g(x) = x;\n"
      "module m;\n"
      "  import q::f;\n"
      "  int arr [2];\n"
      "  initial $display(\"%0d\", f(arr) + g(arr));\n"
      "endmodule\n"
      "module n;\n"
      "  int arr [2];\n"
      "  initial $display(\"%0d\", f(arr));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 10, "11.12"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 14, "11.12"));
}

TEST(LetActualScopeElaboration, AWildcardImportedNonLetEndsTheSearch) {
  ElabFixture f;
  ElaborateSrc(
      "let f(int x) = x;\n"
      "package p;\n"
      "  function automatic int f(int a [2]); return a[0]; endfunction\n"
      "endpackage\n"
      "module m;\n"
      "  import p::*;\n"
      "  int arr [2];\n"
      "  initial $display(\"%0d\", f(arr));\n"
      "endmodule\n"
      "module n;\n"
      "  int arr [2];\n"
      "  initial $display(\"%0d\", f(arr));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 8, "11.12"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 12, "11.12"));
}

TEST(LetActualScopeElaboration, AUnitScopedCallReachesTheUnitsLet) {
  ElabFixture f;
  ElaborateSrc(
      "let f(x) = x;\n"
      "let h(int x) = x;\n"
      "package p; let f(int x) = x; let h(x) = x; endpackage\n"
      "module m;\n"
      "  import p::*;\n"
      "  int arr [2];\n"
      "  initial $display(\"%0d\", $unit::f(arr));\n"
      "  initial $display(\"%0d\", $unit::h(arr));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 7, "11.12"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 8, "11.12"));
}

TEST(LetActualScopeElaboration, AUnitLetsFormalTakesTheUnitsTypedef) {
  ElabFixture f;
  ElaborateSrc(
      "typedef int t;\n"
      "t v;\n"
      "let f(t x) = x;\n"
      "let g(int x) = x;\n"
      "module m;\n"
      "  typedef struct { int a; byte b; } t;\n"
      "  int i; int a [2];\n"
      "  initial $display(\"%0d\", f(i) + g(v));\n"
      "  initial $display(\"%0d\", f(a));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 8, "11.12"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 9, "11.12"));
}

TEST(LetActualScopeElaboration, APackageLetsFormalTakesAnImportedTypedef) {
  ElabFixture f;
  ElaborateSrc(
      "package q; typedef int q_t; endpackage\n"
      "package p;\n"
      "  import q::*;\n"
      "  let f(q_t x) = x;\n"
      "  typedef q_t c_t;\n"
      "  let g(c_t x) = x;\n"
      "endpackage\n"
      "module m;\n"
      "  int i; int arr [2];\n"
      "  initial $display(\"%0d\", p::f(i) + p::g(i));\n"
      "  initial $display(\"%0d\", p::f(arr));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 10, "11.12"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 11, "11.12"));
}

TEST(LetActualScopeElaboration, LocalNamesHideAUnitVariable) {
  ElabFixture f;
  ElaborateSrc(
      "string w;\n"
      "string pv, lp;\n"
      "package p; real pv; endpackage\n"
      "module m(input real w);\n"
      "  import p::*;\n"
      "  localparam real lp = 1.5;\n"
      "  let f(real a) = a;\n"
      "  let h(real w) = f(w);\n"
      "  function automatic real g(real w); return f(w); endfunction\n"
      "  initial $display(\"%f\", f(w) + f(pv) + f(lp) + g(1.0) + h(2.0));\n"
      "endmodule\n"
      "module n;\n"
      "  let f(real a) = a;\n"
      "  initial $display(\"%f\", f(w));\n"
      "endmodule\n",
      f);
  for (uint32_t line : {8u, 9u, 10u}) {
    EXPECT_FALSE(
        ReportedError(f.diag.Diagnostics(), kNotCastCompatible, line, "11.12"));
  }
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 14, "11.12"));
}

TEST(LetActualScopeElaboration, ABlocksImportReachesAPackagesLet) {
  ElabFixture f;
  ElaborateSrc(
      "package p; typedef int arr_t [2]; let f(arr_t x) = x[0]; endpackage\n"
      "let f(int x) = x;\n"
      "module m;\n"
      "  int arr [2];\n"
      "  initial begin\n"
      "    import p::*;\n"
      "    $display(\"%0d\", f(arr));\n"
      "  end\n"
      "  initial $display(\"%0d\", f(arr));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 7, "11.12"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 9, "11.12"));
}

TEST(LetActualScopeElaboration, APackageLetsFormalTakesThePackagesClass) {
  ElabFixture f;
  ElaborateSrc(
      "package q; class C; endclass endpackage\n"
      "package p;\n"
      "  class C; endclass\n"
      "  let f(C c) = c != null;\n"
      "endpackage\n"
      "module m;\n"
      "  p::C h; q::C k;\n"
      "  initial $display(\"%0d\", p::f(h));\n"
      "  initial $display(\"%0d\", p::f(k));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 8, "11.12"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 9, "11.12"));
}

TEST(LetActualScopeElaboration, APackageArrayTypedefsVariableIsAnArray) {
  ElabFixture f;
  ElaborateSrc(
      "package p; typedef int a_t [2]; let h(a_t x) = x[0]; endpackage\n"
      "module m;\n"
      "  import p::*;\n"
      "  p::a_t v; a_t w; int i;\n"
      "  initial $display(\"%0d\", p::h(v) + h(w));\n"
      "  initial $display(\"%0d\", h(i));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 5, "11.12"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 6, "11.12"));
}

TEST(LetActualScopeElaboration, AUnitImportedTypedefIsResolved) {
  ElabFixture f;
  ElaborateSrc(
      "package p; typedef int t; endpackage\n"
      "import p::*;\n"
      "t v;\n"
      "let f(int x) = x;\n"
      "let g(t x) = x;\n"
      "int arr [2];\n"
      "function automatic int c(); return f(v) + g(v); endfunction\n"
      "function automatic int d(); return g(arr); endfunction\n"
      "module m; endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 7, "11.12"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 8, "11.12"));
}

TEST(LetActualScopeElaboration, AGenerateBlocksLetIsReachedWithinTheBlock) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [2];\n"
      "  let f(x) = x;\n"
      "  if (1) begin : g\n"
      "    let f(int x) = x;\n"
      "    initial $display(\"%0d\", f(arr));\n"
      "  end\n"
      "  initial $display(\"%0d\", f(arr));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 6, "11.12"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 8, "11.12"));
}

TEST(LetActualScopeElaboration, ArrayActualsAreJudgedByCountAndSize) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  let p(int x [3]) = x[0];\n"
      "  let q(byte x [2]) = x[0];\n"
      "  let r(byte x [8]) = x[0];\n"
      "  let s(int x [2]) = x[0];\n"
      "  int arr [2]; int a3 [3]; int dyn [];\n"
      "  initial $display(\"%0d\", p(arr));\n"
      "  initial $display(\"%0d\", q(arr));\n"
      "  initial $display(\"%0d\", r(arr) + s(arr) + p(a3) + p(dyn));\n"
      "endmodule\n",
      f);
  for (uint32_t line : {7u, 8u}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNotCastCompatible, line, "11.12"));
  }
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 9, "11.12"));
}

TEST(LetActualScopeElaboration, AggregateActualsFitByBitStreamCast) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a; } s_t;\n"
      "  typedef struct { int a; int b; } d_t;\n"
      "  typedef struct { bit [7:0] a; shortint b; } n_t;\n"
      "  s_t s; byte b4 [4]; int arr [2]; n_t n;\n"
      "  let g(int x) = x;\n"
      "  let h(d_t x) = x.a;\n"
      "  let r(real x) = x;\n"
      "  initial $display(\"%0d\", g(s) + g(b4) + h(arr));\n"
      "  initial $display(\"%0d\", g(n));\n"
      "  initial $display(\"%0d\", r(arr));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 9, "11.12"));
  for (uint32_t line : {10u, 11u}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNotCastCompatible, line, "11.12"));
  }
}

TEST(LetActualScopeElaboration, ArrayDimensionsFoldFromTheirOwnScopesNames) {
  ElabFixture f;
  ElaborateSrc(
      "module m #(parameter int K = 4);\n"
      "  let f(int x [2][3]) = x[0][0];\n"
      "  let s(int x [2]) = x[0];\n"
      "  int a23 [2][3]; int a2k1 [2][K-1];\n"
      "  int a2k [2][K]; int a33 [3][3];\n"
      "  initial $display(\"%0d\", f(a23) + f(a2k1));\n"
      "  initial $display(\"%0d\", f(a2k));\n"
      "  initial $display(\"%0d\", f(a33));\n"
      "  if (1) begin : g\n"
      "    localparam int K = 3;\n"
      "    localparam int J = 2;\n"
      "    localparam int L = 8;\n"
      "    let fj(int x [J][K]) = x[0][0];\n"
      "    int b2k [2][K]; int cj [J][3]; byte bl [L];\n"
      "    initial $display(\"%0d\", f(b2k) + f(cj) + fj(a23) + s(bl));\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {6u, 15u}) {
    EXPECT_FALSE(
        ReportedError(f.diag.Diagnostics(), kNotCastCompatible, line, "11.12"));
  }
  for (uint32_t line : {7u, 8u}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNotCastCompatible, line, "11.12"));
  }
}

TEST(LetActualScopeElaboration, ArrayActualsOfOtherShapesFitByBitStreamCast) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  let f(int x [2][3]) = x[0][0];\n"
      "  let fq(int x [2][$]) = x[0][0];\n"
      "  let d(real x []) = x[0];\n"
      "  let dd(int x []) = x[0];\n"
      "  int a23 [2][3]; int a6 [6]; int a5 [5];\n"
      "  int q2 [2][$]; int q [$]; real ra [2]; byte b2 [2];\n"
      "  initial $display(\"%0d\", f(a6) + f(q2) + f(q) + fq(a23));\n"
      "  initial $display(\"%0d\", d(ra) + dd(b2));\n"
      "  initial $display(\"%0d\", f(a5));\n"
      "endmodule\n",
      f);
  for (uint32_t line : {8u, 9u}) {
    EXPECT_FALSE(
        ReportedError(f.diag.Diagnostics(), kNotCastCompatible, line, "11.12"));
  }
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 10, "11.12"));
}

TEST(LetActualScopeElaboration,
     AnAssociativeFormalTakesOnlyAnAssociativeArray) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef int aa_t [string];\n"
      "  let f(int x [2]) = x[0];\n"
      "  let g(aa_t x) = x.num();\n"
      "  int aa [string]; int arr [2];\n"
      "  initial $display(\"%0d\", f(aa) + g(aa));\n"
      "  initial $display(\"%0d\", g(arr));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 6, "11.12"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 7, "11.12"));
}

TEST(LetActualScopeElaboration, ATypeParametersTypeIsNotTakenFromItsDefault) {
  ElabFixture f;
  ElaborateSrc(
      "module m #(parameter type T = int);\n"
      "  let f(T x) = x[0];\n"
      "  let g(int x [2]) = x[0];\n"
      "  int arr [2]; T v;\n"
      "  initial $display(\"%0d\", f(arr) + g(v));\n"
      "endmodule\n"
      "module top;\n"
      "  typedef int a_t [2];\n"
      "  m #(.T(a_t)) u ();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 5, "11.12"));
}

TEST(LetActualScopeElaboration, UnitScopedNamesPassTheModulesOwn) {
  ElabFixture f;
  ElaborateSrc(
      "typedef struct { int a; int b; } t;\n"
      "parameter int N = 3;\n"
      "module m #(parameter int N = 2);\n"
      "  typedef struct { int a; int b; int c; } t;\n"
      "  let f($unit::t x) = x.a;\n"
      "  let h(int x [3]) = x[0];\n"
      "  int arr [2]; int a3 [3]; int an [$unit::N];\n"
      "  initial $display(\"%0d\", f(arr) + h(an));\n"
      "  initial $display(\"%0d\", f(a3));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 8, "11.12"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 9, "11.12"));
}

TEST(LetActualScopeElaboration, TypesOfAnInterfacePortAreNotFollowed) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc;\n"
      "  typedef int t [2];\n"
      "endinterface\n"
      "module m (ifc p);\n"
      "  typedef p.t lt;\n"
      "  let f(lt x) = x[0];\n"
      "  int a3 [3];\n"
      "  initial $display(\"%0d\", f(a3));\n"
      "endmodule\n"
      "module top;\n"
      "  ifc i ();\n"
      "  m u (i);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 8, "11.12"));
}

TEST(LetActualScopeElaboration, ATypeAClassDeclaresIsFollowed) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "  typedef struct { int a; int b; } s_t;\n"
      "  typedef s_t s2_t;\n"
      "  class N;\n"
      "    typedef byte n_t [3];\n"
      "  endclass\n"
      "endclass\n"
      "package q;\n"
      "  typedef int qt [2];\n"
      "endpackage\n"
      "module m;\n"
      "  let f(C::s_t x) = x.a;\n"
      "  let h(int x [3]) = x[0];\n"
      "  let g(C::s2_t x) = x.a;\n"
      "  let n(int x) = x;\n"
      "  int q;\n"
      "  int a3 [3]; int arr [2];\n"
      "  C::s_t v; C::N::n_t nv; q::qt qv;\n"
      "  initial $display(\"%0d\", f(a3));\n"
      "  initial $display(\"%0d\", h(v));\n"
      "  initial $display(\"%0d\", f(arr) + g(arr));\n"
      "  initial $display(\"%0d\", n(nv));\n"
      "  initial $display(\"%0d\", h(qv));\n"
      "endmodule\n",
      f);
  for (uint32_t line : {20u, 21u, 23u, 24u}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNotCastCompatible, line, "11.12"))
        << line;
  }
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 22, "11.12"));
}

TEST(LetActualScopeElaboration, AChainThroughNoClassLeavesItsTypeUnjudged) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "  typedef int t [2];\n"
      "endclass\n"
      "module m;\n"
      "  let h(int x [3]) = x[0];\n"
      "  C::x::t xv; C::y::t yv;\n"
      "  initial $display(\"%0d\", h(xv) + h(yv));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 8, "11.12"));
}

TEST(LetActualScopeElaboration, AnActualDeclaredNowhereIsNotJudged) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  let f(int x [2]) = x[0];\n"
      "  initial $display(\"%0d\", f(nope));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 3, "11.12"));
}

TEST(LetActualScopeElaboration, AStdImportOffersStdsNamesAlone) {
  ElabFixture f;
  ElaborateSrc(
      "int u3 [3];\n"
      "int mailbox [3];\n"
      "module m;\n"
      "  import std::*;\n"
      "  let f(int x [2]) = x[0];\n"
      "  initial $display(\"%0d\", f(u3));\n"
      "  initial $display(\"%0d\", f(mailbox));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 6, "11.12"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 7, "11.12"));
}

TEST(LetActualScopeElaboration, AnUndeclaredPackagesImportBringsInNoName) {
  ElabFixture f;
  ElaborateSrc(
      "int u3 [3];\n"
      "module m;\n"
      "  import nopkg::*;\n"
      "  let f(int x [2]) = x[0];\n"
      "  initial $display(\"%0d\", f(u3));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "import from unknown package 'nopkg'", 3, "26.3"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 5, "11.12"));
}

TEST(LetActualScopeElaboration, ARepeatedImportAndALoopVariableAreJudged) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  let f(int x) = x;\n"
      "endpackage\n"
      "module m;\n"
      "  import p::*;\n"
      "  import p::*;\n"
      "  typedef struct { int a; int b; } d_t;\n"
      "  let h(d_t x) = x.a;\n"
      "  int arr [2]; d_t dv;\n"
      "  initial $display(\"%0d\", f(arr));\n"
      "  initial $display(\"%0d\", h(dv));\n"
      "  initial for (int i = 0; i < 2; i++) $display(\"%0d\", h(i));\n"
      "endmodule\n",
      f);
  for (uint32_t line : {10u, 12u}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNotCastCompatible, line, "11.12"));
  }
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 11, "11.12"));
}

TEST(LetActualScopeElaboration, StructureMembersAreSizedThroughTheirTypedefs) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef byte b_t;\n"
      "  typedef b_t c_t;\n"
      "  typedef real r_t;\n"
      "  typedef struct { c_t a; c_t b; } p_t;\n"
      "  typedef struct { c_t a; c_t b; c_t c; } q_t;\n"
      "  typedef struct { r_t a; } rs_t;\n"
      "  let g(shortint x) = x;\n"
      "  let s(int x [2]) = x[0];\n"
      "  let w(p_t x) = x.a;\n"
      "  p_t pv; q_t qv; rs_t rv; int ar [0:1]; int ar3 [1:3];\n"
      "  initial $display(\"%0d\", g(pv) + s(ar) + w(pv));\n"
      "  initial $display(\"%0d\", g(qv));\n"
      "  initial $display(\"%0d\", g(rv));\n"
      "  initial $display(\"%0d\", s(ar3));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 12, "11.12"));
  for (uint32_t line : {13u, 14u, 15u}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNotCastCompatible, line, "11.12"));
  }
}

TEST(LetActualScopeElaboration, ARealIsNoActualForAChandleFormal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  let h(chandle x) = x;\n"
      "  real r;\n"
      "  initial $display(\"%0d\", h(r) == null);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 4, "11.12"));
}

TEST(LetActualScopeElaboration, AnArrayOfHandlesFitsAnArrayOfItsClass) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  int v;\n"
      "endclass\n"
      "module m;\n"
      "  let k(C x [2]) = x[0];\n"
      "  C ca [2];\n"
      "  initial $display(\"%0d\", k(ca) == null);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 7, "11.12"));
}

TEST(LetActualScopeElaboration, TypeReferencesFitWhatTheyName) {
  ElabFixture f;
  ElaborateSrc(
      "int i;\n"
      "var type(i) w;\n"
      "module m;\n"
      "  int j;\n"
      "  typedef type(j) jt;\n"
      "  let f(jt x) = x;\n"
      "  let g(int x) = x;\n"
      "  initial $display(\"%0d\", f(j) + g(w));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 8, "11.12"));
}

TEST(LetActualScopeElaboration, ABlocksTypeReferenceTypedefIsNoForwardOne) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a; int b; } kt;\n"
      "  int j;\n"
      "  initial begin\n"
      "    typedef type(j) kt;\n"
      "    let f(kt x) = x;\n"
      "    $display(\"%0d\", f(j));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 7, "11.12"));
}

TEST(LetActualScopeElaboration, ALongTypedefChainIsFollowedToABound) {
  std::string src = "module m;\n  typedef int t0 [2];\n";
  for (int i = 1; i < 32; ++i)
    src += std::format("  typedef t{} t{};\n", i - 1, i);
  src +=
      "  let f(t30 x) = x[0];\n"
      "  let g(t31 x) = x[0];\n"
      "  int a3 [3]; int arr [2];\n"
      "  initial $display(\"%0d\", f(a3));\n"
      "  initial $display(\"%0d\", g(arr));\n"
      "endmodule\n";
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 37, "11.12"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 38, "11.12"));
}

TEST(LetActualScopeElaboration, AnUnpackedUnionIsNoBitStreamType) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef union { int a; byte b; } u_t;\n"
      "  typedef struct { u_t u; } su_t;\n"
      "  typedef union packed { int a; bit [31:0] b; } pu_t;\n"
      "  u_t u; su_t s; pu_t pu;\n"
      "  let g(int x) = x;\n"
      "  initial $display(\"%0d\", g(u));\n"
      "  initial $display(\"%0d\", g(s));\n"
      "  initial $display(\"%0d\", g(pu));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 7, "11.12"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 8, "11.12"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 9, "11.12"));
}

TEST(LetActualScopeElaboration, ArraysOfHandlesAreJudgedByAssignment) {
  ElabFixture f;
  ElaborateSrc(
      "class C; int v; endclass\n"
      "class D; int w; endclass\n"
      "module m;\n"
      "  let h(C x) = x;\n"
      "  let k(C x [2]) = x[0];\n"
      "  let f(int x [2]) = x[0];\n"
      "  int arr [2]; C c; C ca [2]; C c3 [3]; D da [2];\n"
      "  initial $display(\"%0d\", h(ca) == null);\n"
      "  initial $display(\"%0d\", k(c) == null);\n"
      "  initial $display(\"%0d\", k(arr) == null);\n"
      "  initial $display(\"%0d\", k(c3) == null);\n"
      "  initial $display(\"%0d\", k(da) == null);\n"
      "  initial $display(\"%0d\", f(ca));\n"
      "endmodule\n",
      f);
  for (uint32_t line : {8u, 9u, 10u, 11u, 12u}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNotCastCompatible, line, "11.12"))
        << line;
  }
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 13, "11.12"));
}

TEST(LetActualScopeElaboration, AHandleIsABitStreamCastsSource) {
  ElabFixture f;
  ElaborateSrc(
      "class C; int v; endclass\n"
      "class L; local int v; endclass\n"
      "class P; protected int v; endclass\n"
      "class Q extends P; endclass\n"
      "module m;\n"
      "  typedef int aa_t [string];\n"
      "  C c; L l; Q q; C ca [2];\n"
      "  let g(int x) = x;\n"
      "  let s(string x) = x.len();\n"
      "  let r(real x) = x;\n"
      "  let a(aa_t x) = x.num();\n"
      "  initial $display(\"%0d\", g(c) + s(c));\n"
      "  initial $display(\"%0d\", g(l));\n"
      "  initial $display(\"%0d\", s(q));\n"
      "  initial $display(\"%0d\", r(c));\n"
      "  initial $display(\"%0d\", a(ca));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 12, "11.12"));
  for (uint32_t line : {13u, 14u, 15u, 16u}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNotCastCompatible, line, "11.12"))
        << line;
  }
}

}  // namespace
