#include <gtest/gtest.h>

#include <string_view>
#include <unordered_set>

#include "elaborator/package_references.h"
#include "fixture_elaborator.h"
#include "fixture_parser.h"
#include "helpers_reported_error.h"

namespace {

TEST(PackageExport, WildcardExportOfImportedPackage) {
  EXPECT_TRUE(
      ElabOk("package base_pkg;\n"
             "  typedef int myint;\n"
             "endpackage\n"
             "package pkg;\n"
             "  import base_pkg::*;\n"
             "  export base_pkg::*;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n"));
}

TEST(PackageExport, SpecificExportMatchingExplicitImport) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef int t;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::t;\n"
             "  export p1::t;\n"
             "endpackage\n"
             "module m;\n"
             "  import p2::t;\n"
             "endmodule\n"));
}

TEST(PackageExport, SpecificExportMatchingWildcardImport) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef int x;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::*;\n"
             "  export p1::x;\n"
             "endpackage\n"
             "module m;\n"
             "  import p2::x;\n"
             "endmodule\n"));
}

TEST(PackageExport, StarStarExportElaborates) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef int t;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::*;\n"
             "  export *::*;\n"
             "endpackage\n"
             "module m;\n"
             "  import p2::*;\n"
             "endmodule\n"));
}

TEST(PackageExport, ExportPrecedingMatchingImportIsLegal) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef int t;\n"
             "endpackage\n"
             "package p2;\n"
             "  export p1::t;\n"
             "  import p1::t;\n"
             "endpackage\n"
             "module m;\n"
             "  import p2::t;\n"
             "endmodule\n"));
}

TEST(PackageExport, DuplicateExportsOfSameDeclarationAllowed) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef int t;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::t;\n"
             "  export p1::t;\n"
             "  export p1::t;\n"
             "endpackage\n"
             "module m;\n"
             "  import p2::t;\n"
             "endmodule\n"));
}

TEST(PackageExport, ExportOfNameNotInSourcePackageIsError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p1;\n"
             "  typedef int t;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::*;\n"
             "  export p1::missing;\n"
             "endpackage\n"
             "module m;\n"
             "  import p2::*;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'missing' is not a candidate for import from package 'p1'", 6, "26.6"));
}

TEST(PackageExport, ExportWithoutAnyMatchingImportIsError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p1;\n"
             "  typedef int t;\n"
             "endpackage\n"
             "package p2;\n"
             "  export p1::t;\n"
             "endpackage\n"
             "module m;\n"
             "  import p2::t;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "export 'p1::t': 't' is not imported in package "
                            "'p2'",
                            5, "26.6"));
}

TEST(PackageExport, ExportFromUnknownPackageIsError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p2;\n"
             "  export missing_pkg::x;\n"
             "endpackage\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "export from unknown package 'missing_pkg'", 2,
                            "26.6"));
}

TEST(PackageExport, ExportRequiresImportFromTheNamedPackage) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p1;\n"
             "  typedef int t;\n"
             "endpackage\n"
             "package p2;\n"
             "  typedef int t;\n"
             "endpackage\n"
             "package p3;\n"
             "  import p1::t;\n"
             "  export p2::t;\n"
             "endpackage\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "export 'p2::t': 't' is not imported in package "
                            "'p3'",
                            9, "26.6"));
}

TEST(PackageExport, ExportOfWildcardImportedNameBlocksLaterLocalDecl) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p1;\n"
             "  typedef int x;\n"
             "endpackage\n"
             "package p6;\n"
             "  import p1::*;\n"
             "  export p1::x;\n"
             "  int x;\n"
             "endpackage\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of 'x' in package 'p6' follows an "
                            "export that referenced it through a wildcard "
                            "package import",
                            7, "26.6"));
}

TEST(PackageExport, ExportOfWildcardImportedNameBlocksLaterEnumLiteral) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p1; int x = 3; endpackage\n"
             "package p6;\n"
             "  import p1::*;\n"
             "  export p1::x;\n"
             "  typedef enum {x, w} e_t;\n"
             "endpackage\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of 'x' in package 'p6' follows an "
                            "export that referenced it through a wildcard "
                            "package import",
                            5, "26.6"));
}

TEST(PackageExport, ExportOfWildcardImportedNameBlocksLaterEnumVariable) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p1; int x = 3; endpackage\n"
             "package p6;\n"
             "  import p1::*;\n"
             "  export p1::x;\n"
             "  int other;\n"
             "  enum {w, x} v;\n"
             "endpackage\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of 'x' in package 'p6' follows an "
                            "export that referenced it through a wildcard "
                            "package import",
                            6, "26.6"));
}

TEST(PackageExport, ExportOfExplicitlyImportedNameAllowsUnrelatedLocalDecl) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef int t;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::t;\n"
             "  export p1::t;\n"
             "  int other;\n"
             "endpackage\n"
             "module m; endmodule\n"));
}

TEST(PackageExport, WildcardExportedNameDeclaredBeforeExportStaysLegal) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef int y;\n"
             "endpackage\n"
             "package p3;\n"
             "  int keep;\n"
             "  import p1::*;\n"
             "  export p1::y;\n"
             "endpackage\n"
             "module m; endmodule\n"));
}

TEST(PackageExport, ReExportChainAcrossThreePackages) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef int t;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::t;\n"
             "  export p1::t;\n"
             "endpackage\n"
             "package p3;\n"
             "  import p2::t;\n"
             "  export p2::t;\n"
             "endpackage\n"
             "module m;\n"
             "  import p3::t;\n"
             "endmodule\n"));
}

TEST(PackageExport, WildcardExportProvidesOnlyImportedNames) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p1;\n"
             "  typedef int a;\n"
             "  typedef int b;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::a;\n"
             "  export p1::*;\n"
             "endpackage\n"
             "package p3;\n"
             "  import p2::*;\n"
             "  export p2::b;\n"
             "endpackage\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'b' is not a candidate for import from package 'p2'", 11, "26.6"));
}

TEST(PackageExport, WildcardExportProvidesTheImportedNameDownstream) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef int a;\n"
             "  typedef int b;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::a;\n"
             "  export p1::*;\n"
             "endpackage\n"
             "package p3;\n"
             "  import p2::a;\n"
             "  export p2::a;\n"
             "endpackage\n"
             "module m; endmodule\n"));
}

TEST(PackageExport, ClassDeclarationSpecificallyReExported) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  class C;\n"
             "  endclass\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::C;\n"
             "  export p1::C;\n"
             "endpackage\n"
             "module m;\n"
             "  import p2::C;\n"
             "endmodule\n"));
}

TEST(PackageExport, ExportOfClassNotDeclaredInSourceIsError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p1;\n"
             "  class C;\n"
             "  endclass\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::*;\n"
             "  export p1::Missing;\n"
             "endpackage\n"
             "module m;\n"
             "  import p2::*;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'Missing' is not a candidate for import from package 'p1'", 7, "26.6"));
}

TEST(PackageExport, ImportedNameNotExportedIsUnresolvedThroughTheImporter) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p1;\n"
             "  int x = 6;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::x;\n"
             "  int y = x;\n"
             "endpackage\n"
             "module top;\n"
             "  import p2::*;\n"
             "  int r;\n"
             "  initial $display(\"%0d\", x);\n"
             "  initial r = y;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'x'", 11,
                            "23.9"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "reference to unresolved identifier 'y'", 12,
                             "23.9"));
}

TEST(PackageExport, ExplicitExportMakesTheImportedVariableVisible) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  int x = 6;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::x;\n"
             "  export p1::x;\n"
             "  int y = x;\n"
             "endpackage\n"
             "module top;\n"
             "  import p2::*;\n"
             "  int r;\n"
             "  initial $display(\"%0d\", x);\n"
             "  initial r = x + y;\n"
             "endmodule\n",
             f));
}

TEST(PackageExport, StarStarExportMakesTheImportedVariableVisible) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  int x = 6;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::x;\n"
             "  export *::*;\n"
             "endpackage\n"
             "package p3;\n"
             "  import p2::*;\n"
             "  export p2::*;\n"
             "  int seen = x;\n"
             "endpackage\n"
             "module top;\n"
             "  import p3::*;\n"
             "  int r;\n"
             "  initial r = x;\n"
             "endmodule\n",
             f));
}

TEST(PackageExport, ExplicitImportsOfOneDeclarationThroughTwoExportsAgree) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  int x = 6;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::x;\n"
             "  export p1::x;\n"
             "endpackage\n"
             "package p4;\n"
             "  import p1::*;\n"
             "  export p1::*;\n"
             "  int y = x;\n"
             "endpackage\n"
             "module top;\n"
             "  import p2::x;\n"
             "  import p4::x;\n"
             "  import p1::x;\n"
             "  int r;\n"
             "  initial r = x;\n"
             "  initial $display(\"%0d\", x);\n"
             "endmodule\n",
             f));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "reference to unresolved identifier 'x'", 18,
                             "23.9"));
}

TEST(PackageExport, ExplicitImportsOfTwoDistinctDeclarationsStillConflict) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p1;\n"
             "  int x = 6;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::x;\n"
             "  export p1::x;\n"
             "endpackage\n"
             "package p3;\n"
             "  int x = 9;\n"
             "endpackage\n"
             "module top;\n"
             "  import p2::x;\n"
             "  import p3::x;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "explicit import of 'p3::x' conflicts with earlier "
                            "explicit import from 'p2'",
                            13, "26.3"));
}

TEST(PackageExport, ExplicitImportOfTheDeclarationAWildcardReferenceBound) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  int x = 6;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::x;\n"
             "  export p1::x;\n"
             "endpackage\n"
             "package p4;\n"
             "  import p1::*;\n"
             "  export p1::*;\n"
             "  int y = x;\n"
             "endpackage\n"
             "module top;\n"
             "  import p4::*;\n"
             "  int r;\n"
             "  initial r = x;\n"
             "  import p2::x;\n"
             "endmodule\n"));
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p1;\n"
             "  int x = 6;\n"
             "endpackage\n"
             "package p3;\n"
             "  int x = 9;\n"
             "endpackage\n"
             "package p4;\n"
             "  import p1::*;\n"
             "  export p1::*;\n"
             "  int y = x;\n"
             "endpackage\n"
             "module top;\n"
             "  import p4::*;\n"
             "  int r;\n"
             "  initial r = x;\n"
             "  import p3::x;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "explicit import of 'p3::x' is illegal because 'x' "
                            "was already referenced through a wildcard "
                            "package import",
                            16, "26.5"));
}

TEST(PackageExport, ScopedReferenceThroughTheExportingPackage) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  int x = 6;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::x;\n"
             "  export p1::x;\n"
             "endpackage\n"
             "package p4;\n"
             "  import p1::*;\n"
             "  export p1::*;\n"
             "  int y = x;\n"
             "endpackage\n"
             "module top;\n"
             "  int r;\n"
             "  initial r = p2::x + p4::x;\n"
             "endmodule\n"));
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p1;\n"
             "  int x = 6;\n"
             "endpackage\n"
             "package p5;\n"
             "  import p1::x;\n"
             "endpackage\n"
             "module top;\n"
             "  int r;\n"
             "  initial r = p5::x;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to 'p5::x', which package 'p5' neither "
                            "declares nor exports",
                            9, "26.3"));
}

TEST(PackageExport, ExplicitExportOfAnEnumerationLiteral) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef enum {LOW, MID = 6, HIGH} level_t;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::MID;\n"
             "  export p1::MID;\n"
             "endpackage\n"
             "module top;\n"
             "  int r;\n"
             "  initial r = p2::MID;\n"
             "endmodule\n"
             "module m;\n"
             "  import p2::MID;\n"
             "  int r;\n"
             "  initial r = MID;\n"
             "endmodule\n"));
}

TEST(PackageExport, ExportOfANameThePackageNeverDeclaresStaysReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p1;\n"
             "  typedef enum {LOW, MID, HIGH} level_t;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::*;\n"
             "  export p1::NOPE;\n"
             "endpackage\n"
             "module top;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'NOPE' is not a candidate for import from package 'p1'", 6, "26.6"));
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef enum {LOW, MID, HIGH} level_t;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::MID;\n"
             "endpackage\n"
             "module top;\n"
             "endmodule\n"));
}

TEST(PackageExport, ExplicitExportOfAStructMemberAndAVariableEnumLiteral) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef struct { enum {IDLE, BUSY} st; int n; } rec_t;\n"
             "  enum {RED, GREEN} light;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::*;\n"
             "  export p1::BUSY;\n"
             "  export p1::GREEN;\n"
             "endpackage\n"
             "module top;\n"
             "endmodule\n"));
}

TEST(PackageExport, ExplicitExportOfARangedEnumerationLiteral) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef enum {add = 10, sub[5]} e1_t;\n"
             "  enum {v[2:4] = 7} vr;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::*;\n"
             "  export p1::sub3;\n"
             "  export p1::v4;\n"
             "endpackage\n"
             "module top;\n"
             "  int r, s;\n"
             "  initial begin\n"
             "    r = p2::sub3;\n"
             "    s = p2::v4;\n"
             "  end\n"
             "endmodule\n"
             "module m;\n"
             "  import p2::sub3;\n"
             "  int r;\n"
             "  initial r = sub3;\n"
             "endmodule\n"));
}

TEST(PackageExport, ExportOfANameARangedLiteralNeverGeneratesIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p1;\n"
             "  typedef enum {sub[5], w[3:1]} e1_t;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::*;\n"
             "  export p1::sub5;\n"
             "  export p1::sub;\n"
             "  export p1::w0;\n"
             "  export p1::w1;\n"
             "endpackage\n"
             "module top;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'sub5' is not a candidate for import from package 'p1'", 6, "26.6"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'sub' is not a candidate for import from package 'p1'", 7, "26.6"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'w0' is not a candidate for import from package 'p1'", 8, "26.6"));
  EXPECT_FALSE(ReportedError(
      f.diag.Diagnostics(),
      "'w1' is not a candidate for import from package 'p1'", 9, "26.6"));
}

TEST(PackageExport, ExplicitImportOfAnUnexportedImportIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p1; int x = 5; endpackage\n"
             "package p2; import p1::x; endpackage\n"
             "module top;\n"
             "  import p2::x;\n"
             "  initial $display(\"%0d\", x);\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "explicit import of 'p2::x', which package 'p2' "
                            "neither declares nor exports",
                            4, "26.3"));
}

TEST(PackageExport, ExplicitImportOfAnUndeclaredNameIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p; int x = 5; endpackage\n"
             "module top;\n"
             "  import p::nosuch;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "explicit import of 'p::nosuch', which package "
                            "'p' neither declares nor exports",
                            3, "26.3"));
}

TEST(PackageExport, ExplicitImportsOfACheckerAndAStdClassElaborate) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  checker chk(logic a); endchecker\n"
             "endpackage\n"
             "module top;\n"
             "  import p::chk;\n"
             "  import std::semaphore;\n"
             "  logic a = 1;\n"
             "  chk c(a);\n"
             "  semaphore s = new(1);\n"
             "endmodule\n"));
}

TEST(PackageExport, WildcardExportHandsOnOnlyReferencedCandidates) {
  EXPECT_TRUE(
      ElabOk("package p1; int x = 1; int y = 10; endpackage\n"
             "package p4;\n"
             "  import p1::*;\n"
             "  export p1::*;\n"
             "  int q = x;\n"
             "endpackage\n"
             "package p7; int y = 70; endpackage\n"
             "module top;\n"
             "  import p4::*;\n"
             "  import p7::*;\n"
             "  int z = y;\n"
             "  initial $display(\"%0d %0d\", y, q);\n"
             "endmodule\n"));
}

TEST(PackageExport, PackageReferencedNamesReadEveryDeclaration) {
  auto r = Parse(
      "package p;\n"
      "  typedef int my_t;\n"
      "  typedef enum {A = KA, R[2]} e_t;\n"
      "  typedef struct { my_t m; int arr[KD]; struct { int k; } in; } s_t;\n"
      "  my_t v = initv;\n"
      "  logic [KL:0] w;\n"
      "  logic [1:0][KX:0] z;\n"
      "  int u[KU];\n"
      "  function my_t f(my_t a = defv);\n"
      "    typedef int blk_t;\n"
      "    my_t loc = body_ref;\n"
      "    return call_ref(a);\n"
      "  endfunction\n"
      "  property pr(b); @(posedge clk_ref) b |-> tree_ref; endproperty\n"
      "  property pq; @(posedge clk2) disable iff (dis_ref) bool_ref;\n"
      "  endproperty\n"
      "  class C #(int W = cparam_ref) extends base_ref;\n"
      "    my_t m = minit_ref;\n"
      "    int marr[mdim_ref];\n"
      "    typedef int ctd_t;\n"
      "    function void meth(); m = meth_ref; endfunction\n"
      "  endclass\n"
      "  typedef int pt_t;\n"
      "  C #(pt_t) cv;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  const std::unordered_set<std::string_view> kNames =
      PackageReferencedNames(r.cu->packages[0]);
  for (std::string_view name :
       {"KA",         "my_t",     "KD",        "initv",    "KL",
        "KX",         "KU",       "defv",      "body_ref", "call_ref",
        "clk_ref",    "tree_ref", "clk2",      "dis_ref",  "bool_ref",
        "cparam_ref", "base_ref", "minit_ref", "mdim_ref", "meth_ref",
        "pt_t"}) {
    EXPECT_TRUE(kNames.contains(name)) << name;
  }
}

}  // namespace
