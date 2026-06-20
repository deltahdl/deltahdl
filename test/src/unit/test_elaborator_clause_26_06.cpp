#include "fixture_elaborator.h"

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
             "endmodule\n"));
}

TEST(PackageExport, ExportWithoutAnyMatchingImportIsError) {
  EXPECT_FALSE(
      ElabOk("package p1;\n"
             "  typedef int t;\n"
             "endpackage\n"
             "package p2;\n"
             "  export p1::t;\n"
             "endpackage\n"
             "module m;\n"
             "  import p2::t;\n"
             "endmodule\n"));
}

TEST(PackageExport, ExportFromUnknownPackageIsError) {
  EXPECT_FALSE(
      ElabOk("package p2;\n"
             "  export missing_pkg::x;\n"
             "endpackage\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(PackageExport, ExportRequiresImportFromTheNamedPackage) {
  // The name being exported must have been imported from the very package named
  // in the export. Here 't' is imported, but from p1 — so exporting it as p2::t
  // is an error even though p2 also declares a 't'.
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

}  // namespace
