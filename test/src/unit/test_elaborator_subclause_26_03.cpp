

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "package import declaration is not allowed in "
                            "class scope",
                            5, "26.3"));
}

TEST(PackageImport, ImportedIdentifierNotVisibleViaHierarchicalRef) {
  ElabFixture f;
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
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference 'c.x' targets a name "
                            "imported into 'child' from a package",
                            10, "26.3"));
}

TEST(PackageImport, WildcardImportFromUnknownPackageIsError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  import nonexistent_pkg::*;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "import from unknown package 'nonexistent_pkg'", 2,
                            "26.3"));
}

TEST(PackageImport, ExplicitImportFromUnknownPackageIsError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  import nonexistent_pkg::x;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "import from unknown package 'nonexistent_pkg'", 2,
                            "26.3"));
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
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  parameter int X = 1;\n"
             "endpackage\n"
             "module m;\n"
             "  int X;\n"
             "  import pkg::X;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "explicit import of 'pkg::X' collides with existing declaration of 'X'",
      6, "26.3"));
}

TEST(PackageImport,
     ExplicitImportCollidesWithExplicitImportFromAnotherPackage) {
  ElabFixture f;
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
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "explicit import of 'p2::X' conflicts with earlier "
                            "explicit import from 'p1'",
                            9, "26.3"));
}

TEST(PackageImport, WildcardAmbiguityBetweenTwoPackagesIsError) {
  ElabFixture f;
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
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to 'X' is ambiguous between wildcard "
                            "imports of packages 'p1' and 'p2'",
                            9, "26.3"));
}

TEST(PackageImport, DeclarationAfterWildcardClaimIsError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  parameter int X = 1;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "  int y;\n"
             "  initial y = X;\n"
             "  int X;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of 'X' follows a reference resolved "
                            "through a wildcard package import",
                            8, "26.3"));
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

// §26.3: an explicit import brings in only the symbol it names. Importing
// pkg::A must not make the sibling declaration pkg::B visible unqualified.
TEST(PackageImport, ExplicitImportDoesNotBringSiblingPackageSymbols) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  parameter int A = 1;\n"
             "  parameter int B = 2;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::A;\n"
             "  logic [31:0] y;\n"
             "  initial y = B;\n"
             "endmodule\n",
             f));
  // The §26.3 rule leaves 'B' invisible; the report that fires is the §23.9
  // unresolved bare-identifier read.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'B'", 8,
                            "23.9"));
}

// §26.3: importing an enumeration type by explicit import imports the type name
// only, not the enumeration literals declared inside it. A bare reference to a
// literal of that enum must therefore fail to resolve.
TEST(PackageImport, ExplicitImportOfEnumTypeDoesNotImportLiterals) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package q;\n"
             "  typedef enum { ORIGINAL, FALSE } teeth_t;\n"
             "endpackage\n"
             "module m;\n"
             "  import q::teeth_t;\n"
             "  teeth_t myteeth;\n"
             "  initial myteeth = FALSE;\n"
             "endmodule\n",
             f));
  // The §26.3 rule leaves the literal 'FALSE' invisible; the report that fires
  // is the §23.9 unresolved bare-identifier read.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'FALSE'", 7,
                            "23.9"));
}

// §26.3 (companion to the rule above): a wildcard import of the same package
// does bring the enumeration literals into scope, so the bare reference now
// resolves.
TEST(PackageImport, WildcardImportOfEnumBringsLiteralsIntoScope) {
  EXPECT_TRUE(
      ElabOk("package q;\n"
             "  typedef enum { ORIGINAL, FALSE } teeth_t;\n"
             "endpackage\n"
             "module m;\n"
             "  import q::*;\n"
             "  teeth_t myteeth;\n"
             "  initial myteeth = FALSE;\n"
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

// §26.3: the package scope resolution operator names any constant member of a
// package. A localparam is a distinct §11.2.1 constant form from a parameter
// and folds through the compound-key path in const evaluation, so exercise it
// in a constant-expression position (a packed range) separately.
TEST(PackageScopeReference, PackageScopeLocalparamResolution) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  localparam int W = 6;\n"
             "endpackage\n"
             "module m;\n"
             "  logic [pkg::W-1:0] data;\n"
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

// A §26.3 package-scoped subroutine call resolves to the function declared in
// the named package, arguments included; the parser file for this subclause
// carries the case that the same call is accepted by the grammar.
TEST(PackageScopeReference, PackageScopedFunctionCallElaborates) {
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
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int y;\n"
             "  initial y = nonexistent_identifier;\n"
             "endmodule\n",
             f));
  // A bare read that no import makes visible is reported under §23.9.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier "
                            "'nonexistent_identifier'",
                            3, "23.9"));
}

}  // namespace
