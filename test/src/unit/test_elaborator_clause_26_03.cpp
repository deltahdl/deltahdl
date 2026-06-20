

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

TEST(PackageImport, WildcardImportFromUnknownPackageIsError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  import nonexistent_pkg::*;\n"
             "endmodule\n"));
}

TEST(PackageImport, ExplicitImportFromUnknownPackageIsError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  import nonexistent_pkg::x;\n"
             "endmodule\n"));
}

TEST(PackageImport, RepeatedExplicitImportFromSamePackageIsAllowed) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  parameter int X = 1;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::X;\n"
             "  import pkg::X;\n"
             "endmodule\n"));
}

TEST(PackageImport, ExplicitImportCollidesWithExistingLocalDeclaration) {
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  parameter int X = 1;\n"
             "endpackage\n"
             "module m;\n"
             "  int X;\n"
             "  import pkg::X;\n"
             "endmodule\n"));
}

TEST(PackageImport,
     ExplicitImportCollidesWithExplicitImportFromAnotherPackage) {
  EXPECT_FALSE(
      ElabOk("package p1;\n"
             "  parameter int X = 1;\n"
             "endpackage\n"
             "package p2;\n"
             "  parameter int X = 2;\n"
             "endpackage\n"
             "module m;\n"
             "  import p1::X;\n"
             "  import p2::X;\n"
             "endmodule\n"));
}

TEST(PackageImport, WildcardAmbiguityBetweenTwoPackagesIsError) {
  EXPECT_FALSE(
      ElabOk("package p1;\n"
             "  parameter int X = 1;\n"
             "endpackage\n"
             "package p2;\n"
             "  parameter int X = 2;\n"
             "endpackage\n"
             "module m;\n"
             "  int y;\n"
             "  initial y = X;\n"
             "  import p1::*;\n"
             "  import p2::*;\n"
             "endmodule\n"));
}

TEST(PackageImport, DeclarationAfterWildcardClaimIsError) {
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  parameter int X = 1;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "  int y;\n"
             "  initial y = X;\n"
             "  int X;\n"
             "endmodule\n"));
}

TEST(PackageImport, LocalDeclShadowsWildcardImportedName) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  parameter int X = 1;\n"
             "endpackage\n"
             "module m;\n"
             "  int X;\n"
             "  import pkg::*;\n"
             "  int y;\n"
             "  initial y = X;\n"
             "endmodule\n"));
}

TEST(PackageScopeReference, PackageScopeParamResolution) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  parameter int WIDTH = 8;\n"
             "endpackage\n"
             "module m;\n"
             "  logic [pkg::WIDTH-1:0] data;\n"
             "endmodule\n"));
}

TEST(PackageScopeReference, PackageScopeTypeResolution) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic [7:0] byte_t;\n"
             "endpackage\n"
             "module m;\n"
             "  pkg::byte_t data;\n"
             "endmodule\n"));
}

TEST(PackageImport, ExplicitImportIdentVisibleUnqualified) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  parameter int WIDTH = 16;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::WIDTH;\n"
             "  logic [WIDTH-1:0] data;\n"
             "endmodule\n"));
}

TEST(PackageScopeReference, PackageScopedFunctionCall) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  function int add(int a, int b); return a + b; endfunction\n"
             "endpackage\n"
             "module m;\n"
             "  int x;\n"
             "  initial x = pkg::add(1, 2);\n"
             "endmodule\n"));
}

TEST(PackageImport, FunctionCallBindsToLaterFunctionInSameScope) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int x;\n"
             "  initial x = helper(2);\n"
             "  function int helper(int a); return a + 1; endfunction\n"
             "endmodule\n"));
}

TEST(PackageImport, OuterScopeSearchFindsCompilationUnitName) {
  EXPECT_TRUE(
      ElabOk("localparam int WIDTH = 8;\n"
             "module m;\n"
             "  logic [WIDTH-1:0] data;\n"
             "endmodule\n"));
}

TEST(PackageImport, UnresolvedReferenceIsError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int y;\n"
             "  initial y = nonexistent_identifier;\n"
             "endmodule\n"));
}

}  // namespace
