#include "fixture_elaborator.h"

namespace {

TEST(PackageImport, ExplicitImportCollidesWithLocalDecl) {
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  int x;\n"
             "endpackage\n"
             "module m;\n"
             "  int x;\n"
             "  import pkg::x;\n"
             "endmodule\n"));
}

TEST(PackageImport, ExplicitImportCollidesWithOtherExplicitImport) {
  EXPECT_FALSE(
      ElabOk("package p1;\n"
             "  int x;\n"
             "endpackage\n"
             "package p2;\n"
             "  int x;\n"
             "endpackage\n"
             "module m;\n"
             "  import p1::x;\n"
             "  import p2::x;\n"
             "endmodule\n"));
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
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  int x;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "  initial x = 1;\n"
             "  int x;\n"
             "endmodule\n"));
}

TEST(PackageImport, AmbiguousWildcardImportIsIllegal) {
  EXPECT_FALSE(
      ElabOk("package p1;\n"
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
             "endmodule\n"));
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
  EXPECT_FALSE(
      ElabOk("package q;\n"
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
             "endmodule\n"));
}

// Table 26-1 Row B, column 4 (the "otherwise allowed" facet): two wildcard
// imports that both supply the same name make only an unqualified *reference*
// to that name illegal; the import declarations themselves stay legal. Here the
// overlapping name is never referenced, while the names unique to each package
// are referenced and resolve cleanly, so elaboration succeeds.
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

// Table 26-1 Row B (columns 3 and 4 together): an explicit import outranks
// wildcard imports, so explicitly importing a name that two wildcard imports
// both provide resolves the would-be ambiguity. The unqualified reference binds
// to the explicitly imported declaration and elaboration succeeds, in contrast
// to the same two wildcards without the explicit import.
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

}  // namespace
