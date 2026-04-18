// §26.3

#include "fixture_elaborator.h"

namespace {

TEST(PackageImport, MultiplePackages) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef int t1;\n"
             "endpackage\n"
             "package p2;\n"
             "  typedef int t2;\n"
             "endpackage\n"
             "module m;\n"
             "  import p1::*;\n"
             "  import p2::*;\n"
             "endmodule\n"));
}

TEST(PackageImport, WildcardImportedIntoModule) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic [7:0] byte_t;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "  byte_t data;\n"
             "endmodule\n"));
}

TEST(PackageImport, WildcardImportFunctionIntoModule) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  function int add(int a, int b); return a + b; endfunction\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n"));
}

TEST(PackageImport, ImportInClassScopeError) {
  ElabFixture f;
  ElaborateSrc(
      "package pkg;\n"
      "  parameter int X = 1;\n"
      "endpackage\n"
      "class c;\n"
      "  import pkg::*;\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

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

TEST(PackageImport, ImportedIdentifierNotVisibleViaHierarchicalRef) {
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  int x;\n"
             "endpackage\n"
             "module child;\n"
             "  import pkg::x;\n"
             "endmodule\n"
             "module top;\n"
             "  child c();\n"
             "  int y;\n"
             "  initial y = c.x;\n"
             "endmodule\n"));
}

}  // namespace
