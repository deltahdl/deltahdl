#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

namespace {

TEST(PackageImport, ExplicitImportCollidesWithLocalDecl) {
  ElabFixture f;
  ElabOk(
      "package pkg;\n"
      "  int x;\n"
      "endpackage\n"
      "module m;\n"
      "  int x;\n"
      "  import pkg::x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "explicit import of 'pkg::x' collides with existing", 6, "26.3"));
}

TEST(PackageImport, ExplicitImportCollidesWithOtherExplicitImport) {
  ElabFixture f;
  ElabOk(
      "package p1;\n"
      "  int x;\n"
      "endpackage\n"
      "package p2;\n"
      "  int x;\n"
      "endpackage\n"
      "module m;\n"
      "  import p1::x;\n"
      "  import p2::x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "explicit import of 'p2::x' conflicts with earlier",
                            9, "26.3"));
}

TEST(PackageImport, RepeatedExplicitImportFromSamePackageAllowed) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  int x;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::x;\n"
             "  import pkg::x;\n"
             "endmodule\n"));
}

TEST(PackageImport, LocalDeclShadowsWildcardImport) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  int x;\n"
             "endpackage\n"
             "module m;\n"
             "  int x;\n"
             "  import pkg::*;\n"
             "endmodule\n"));
}

TEST(PackageImport, LocalDeclAfterWildcardReferenceIsIllegal) {
  ElabFixture f;
  ElabOk(
      "package pkg;\n"
      "  int x;\n"
      "endpackage\n"
      "module m;\n"
      "  import pkg::*;\n"
      "  initial x = 1;\n"
      "  int x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "declaration of 'x' follows a reference resolved through", 7, "26.3"));
}

TEST(PackageImport, AmbiguousWildcardImportIsIllegal) {
  ElabFixture f;
  ElabOk(
      "package p1;\n"
      "  int x;\n"
      "endpackage\n"
      "package p2;\n"
      "  int x;\n"
      "endpackage\n"
      "module m;\n"
      "  import p1::*;\n"
      "  import p2::*;\n"
      "  int y;\n"
      "  initial y = x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "reference to 'x' is ambiguous between wildcard imports", 11, "26.3"));
}

TEST(PackageImport, ExplicitImportMakesIdentifierVisible) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic [7:0] byte_t;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::byte_t;\n"
             "  byte_t x;\n"
             "endmodule\n"));
}

TEST(PackageImport, WildcardImportResolvesUndefinedReference) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  int c;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "  int d;\n"
             "  initial d = c;\n"
             "endmodule\n"));
}

TEST(PackageImport, ExplicitImportWithWildcardFromOtherPackageAllowed) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  int c;\n"
             "endpackage\n"
             "package q;\n"
             "  int c;\n"
             "endpackage\n"
             "module m;\n"
             "  import q::*;\n"
             "  import p::c;\n"
             "endmodule\n"));
}

TEST(PackageImport, ExplicitImportAfterWildcardReferenceIsIllegal) {
  ElabFixture f;
  ElabOk(
      "package q;\n"
      "  int c;\n"
      "endpackage\n"
      "package p;\n"
      "  int c;\n"
      "endpackage\n"
      "module m;\n"
      "  import q::*;\n"
      "  int d;\n"
      "  initial d = c;\n"
      "  import p::c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "explicit import of 'p::c' is illegal because", 11,
                            "26.5"));
}

TEST(PackageImport, OverlappingWildcardImportsLegalWithoutAmbiguousReference) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  int x;\n"
             "  int a;\n"
             "endpackage\n"
             "package p2;\n"
             "  int x;\n"
             "  int b;\n"
             "endpackage\n"
             "module m;\n"
             "  import p1::*;\n"
             "  import p2::*;\n"
             "  int ya, yb;\n"
             "  initial begin\n"
             "    ya = a;\n"
             "    yb = b;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(PackageImport, ExplicitImportResolvesWildcardAmbiguity) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  int x;\n"
             "endpackage\n"
             "package p2;\n"
             "  int x;\n"
             "endpackage\n"
             "module m;\n"
             "  import p1::*;\n"
             "  import p2::*;\n"
             "  import p1::x;\n"
             "  int y;\n"
             "  initial y = x;\n"
             "endmodule\n"));
}

TEST(PackageImport, AmbiguousWildcardImportOfEnumMemberIsIllegal) {
  ElabFixture f;
  ElabOk(
      "package p1;\n"
      "  typedef enum bit {FALSE, TRUE} b1_t;\n"
      "endpackage\n"
      "package p2;\n"
      "  typedef enum bit {FALSE, TRUE} b2_t;\n"
      "endpackage\n"
      "module m;\n"
      "  import p1::*;\n"
      "  import p2::*;\n"
      "  int y;\n"
      "  initial y = FALSE;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "reference to 'FALSE' is ambiguous between wildcard imports", 11,
      "26.3"));
}

TEST(PackageImport, WildcardImportMakesEnumMemberVisible) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  typedef enum bit {FALSE, TRUE} b_t;\n"
             "endpackage\n"
             "module m;\n"
             "  import p::*;\n"
             "  int y;\n"
             "  initial y = TRUE;\n"
             "endmodule\n"));
}

TEST(PackageImport, NetInitReferenceForcesWildcardThenExplicitImportConflicts) {
  ElabFixture f;
  ElabOk(
      "package q;\n"
      "  int c;\n"
      "endpackage\n"
      "package p;\n"
      "  int c;\n"
      "endpackage\n"
      "module m;\n"
      "  import q::*;\n"
      "  wire a = c;\n"
      "  import p::c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "explicit import of 'p::c' is illegal because", 10,
                            "26.5"));
}

TEST(PackageImport, AmbiguousWildcardReferenceViaNetInitIsIllegal) {
  ElabFixture f;
  ElabOk(
      "package p1;\n"
      "  int x;\n"
      "endpackage\n"
      "package p2;\n"
      "  int x;\n"
      "endpackage\n"
      "module m;\n"
      "  import p1::*;\n"
      "  import p2::*;\n"
      "  wire w = x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "reference to 'x' is ambiguous between wildcard imports", 10, "26.3"));
}

TEST(PackageImport, NetInitReferenceResolvesThroughSingleWildcard) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  int c;\n"
             "endpackage\n"
             "module m;\n"
             "  import p::*;\n"
             "  wire w = c;\n"
             "endmodule\n"));
}

TEST(PackageImport, ExplicitImportOfTypedefCollidesWithLocalTypedef) {
  ElabFixture f;
  ElabOk(
      "package pkg;\n"
      "  typedef logic [3:0] T;\n"
      "endpackage\n"
      "module m;\n"
      "  typedef int T;\n"
      "  import pkg::T;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "explicit import of 'pkg::T' collides with existing", 6, "26.3"));
}

TEST(PackageImport, ExplicitImportOfParameterCollidesWithLocalParameter) {
  ElabFixture f;
  ElabOk(
      "package pkg;\n"
      "  parameter int P = 1;\n"
      "endpackage\n"
      "module m;\n"
      "  localparam int P = 2;\n"
      "  import pkg::P;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "explicit import of 'pkg::P' collides with existing", 6, "26.3"));
}

TEST(PackageImport, ExplicitImportCollidesWithLocalEnumMember) {
  ElabFixture f;
  ElabOk(
      "package pkg;\n"
      "  int X;\n"
      "endpackage\n"
      "module m;\n"
      "  typedef enum bit {X, Y} local_e;\n"
      "  import pkg::X;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "explicit import of 'pkg::X' collides with existing", 6, "26.3"));
}

TEST(PackageImport, LocalEnumMemberDeclAfterWildcardReferenceIsIllegal) {
  ElabFixture f;
  ElabOk(
      "package pkg;\n"
      "  int X;\n"
      "endpackage\n"
      "module m;\n"
      "  import pkg::*;\n"
      "  int d;\n"
      "  initial d = X;\n"
      "  typedef enum bit {X, Y} local_e;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "declaration of 'X' follows a reference resolved through", 8, "26.3"));
}

TEST(PackageImport, LocalEnumShadowsUnreferencedWildcardImport) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  int X;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "  typedef enum bit {X, Y} local_e;\n"
             "  int y;\n"
             "  initial y = Y;\n"
             "endmodule\n"));
}

TEST(PackageImport, ExplicitImportOfConstFromTwoPackagesIsIllegal) {
  ElabFixture f;
  ElabOk(
      "package p;\n"
      "  const int c = 0;\n"
      "endpackage\n"
      "package q;\n"
      "  const int c = 1;\n"
      "endpackage\n"
      "module m;\n"
      "  import p::c;\n"
      "  import q::c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "explicit import of 'q::c' conflicts with earlier",
                            9, "26.3"));
}

TEST(PackageImport, ExplicitImportMakesEnumMemberVisible) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef enum bit {FALSE, TRUE} e;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::TRUE;\n"
             "  int y;\n"
             "  initial y = TRUE;\n"
             "endmodule\n"));
}

TEST(PackageImport, PackageLocalparamOfPackageEnumTypeFoldsToLiteral) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef enum { FALSE, TRUE } BOOL;\n"
      "  localparam BOOL d = TRUE;\n"
      "endpackage\n"
      "module top;\n"
      "  import p::*;\n"
      "  localparam int SCOPED = p::d;\n"
      "  localparam int IMPORTED = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* scoped = FindParam(design, "top", "SCOPED");
  ASSERT_NE(scoped, nullptr);
  EXPECT_TRUE(scoped->is_resolved);
  EXPECT_EQ(scoped->resolved_value, 1);
  const auto* imported = FindParam(design, "top", "IMPORTED");
  ASSERT_NE(imported, nullptr);
  EXPECT_TRUE(imported->is_resolved);
  EXPECT_EQ(imported->resolved_value, 1);
}

}  // namespace
