#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kNotCastCompatible =
    "is not cast compatible with the type of formal";

// §11.12, rule 2, with §7.4: a compilation unit's typedef of an unpacked array
// makes a variable the unit or a unit function declares with it an array, as
// a module's does, so it fits a formal of that typedef, a unit let's or a
// module let's, while an int does not.
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

// §26.3 searches one scope at a time, each scope's declarations and explicit
// imports ahead of its wildcard imports, and the module's scope ahead of the
// compilation unit's: m's `import q::f` gives `f` q's untyped let over the
// unit's `import p::f`, and the unit's own `g` comes ahead of the unit's
// wildcard import of r. n imports nothing, so its `f` is p's.
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

// §26.3: a wildcard import's candidate is whatever the package declares of the
// name, so p's function `f` is what m's `f(arr)` calls, ahead of the
// compilation unit's let `f`, which n, importing nothing, reaches.
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

// §3.12.1: `$unit::f` names the compilation unit's own `f`, whatever the
// module imports, so `$unit::f(arr)` reaches the unit's untyped let rather
// than p's, and `$unit::h(arr)` the unit's typed one rather than p's untyped.
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

// §3.12.1: a compilation unit's let and variable take the unit's typedef `t`,
// an int, in a module declaring a `t` of its own, so `f(i)` and `g(v)` fit,
// while an unpacked array of two ints is no actual for the unit's `t`.
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

// §26.3 within a package: a package's let formal written with a typedef the
// package imports, or with its own typedef of one, takes that typedef's type,
// an int here, though the calling module imports neither package.
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

// §3.12.1 and §26.3: a port, a parameter, a let's formal, a function's formal
// and a variable a wildcard import brings in each hide a compilation unit's
// string of the same name, so a real formal takes them; n declares none of the
// names, so its `w` is the unit's string.
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

// §26.3: a block's wildcard import is searched ahead of the scopes around the
// block, so `f(arr)` within the block reaches p's let of an unpacked array,
// which arr fits, and outside it the compilation unit's let of an int.
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

// §26.2 with §6.22.5: a package's let formal written with the package's own
// class takes that class, whatever another package's class of the same name,
// so p's own handle fits it and q's is reported.
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

// §7.4 with §26.3: a variable written with a package's typedef of an unpacked
// array, behind the package's prefix or through a wildcard import, is an
// array, so it fits the package let's formal of that typedef, and an int does
// not.
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

// §26.3 at the compilation unit: a unit variable and a unit let's formal
// written with a typedef the unit imports take its type, an int, so a unit
// function's calls passing the variable fit, while an unpacked array does not.
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

// §27.3 makes a generate block a scope of its own, so its let `f` is what a
// call within the block reaches, and a call outside it reaches the module's
// untyped `f`.
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

// §11.12, rule 2, with §7.6 and §6.24.3: an unpacked array fits an array
// formal it is assignment compatible with -- equivalent elements and, for a
// fixed-size formal, as many of them -- or one a bit-stream cast converts it
// to, of the same number of bits. Two ints are neither for three ints nor for
// two bytes; they are both for eight bytes and for two ints, and a dynamic
// array's size is not known until it runs.
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

// §11.12, rule 2, with §6.24.3: a bit-stream cast converts between two
// bit-stream types of the same number of bits, a structure and an array among
// them, so a 32-bit structure or four bytes fit an int formal and two ints a
// 64-bit structure's; a 24-bit structure does not fit an int, and a real is no
// bit-stream type at all.
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

}  // namespace
