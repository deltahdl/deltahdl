#include "fixture_elaborator.h"
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
  // The name being exported must have been imported from the very package named
  // in the export. Here 't' is imported, but from p1 — so exporting it as p2::t
  // is an error even though p2 also declares a 't'.
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
  // §26.6 package p6 example: exporting a wildcard-imported name makes the
  // export count as a reference that imports the name into the package, so a
  // later local declaration of that same name in the package is illegal.
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

TEST(PackageExport, ExportOfExplicitlyImportedNameAllowsUnrelatedLocalDecl) {
  // Positive control: the conflict is specific to a name pulled in *only*
  // through a wildcard import. An explicit import of one name leaves an
  // unrelated local declaration legal.
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
  // Positive control on ordering: the p6 rule flags only a declaration that
  // *follows* the export. A local declaration that precedes the export is not
  // reached by the export-as-reference rule.
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
  // §26.6: `export p1::*` re-exports only the names the package actually
  // imported from p1, not every candidate p1 declares. p2 imports only p1::a,
  // so its `export p1::*` makes a available but not b. A downstream package
  // that tries to export p2::b therefore references a name p2 does not provide,
  // which is an error.
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
  // Positive control for the rule above: the name p2 did import from p1 (a) is
  // provided by its `export p1::*`, so a downstream export of p2::a is legal.
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
  // §26.6 applies to any exported declaration kind, not only typedefs. A class
  // name is resolved through the class-name branch of the export-candidate
  // check, distinct from the plain item-name branch the typedef cases exercise.
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
  // Negative form of the class input: a class name that the source package does
  // not declare is not a candidate for import, so exporting it is an error.
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

}  // namespace
