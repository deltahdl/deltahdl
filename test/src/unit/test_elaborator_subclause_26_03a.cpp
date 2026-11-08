#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

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
  ElaborateSrcAllowingParseErrors(
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

TEST(PackageImport, WildcardImportedIdentifierNotVisibleViaHierarchicalRef) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  int w;\n"
             "  class K; endclass\n"
             "  int x;\n"
             "endpackage\n"
             "module child;\n"
             "  import pkg::*;\n"
             "  int seen = x;\n"
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
                            13, "26.3"));
}

TEST(PackageImport, HierarchicalRefToAChildsOwnDeclarationElaborates) {
  EXPECT_TRUE(
      ElabOk("package p; int x = 1; endpackage\n"
             "module child;\n"
             "  import p::*;\n"
             "  int x = 9;\n"
             "endmodule\n"
             "module top;\n"
             "  child u();\n"
             "  int y;\n"
             "  initial #1 y = u.x;\n"
             "endmodule\n"));
}

TEST(PackageImport, ImportOfAPackageDeclaredLaterIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module top;\n"
             "  import p::*;\n"
             "  int r = K;\n"
             "endmodule\n"
             "package p; parameter int K = 3; endpackage\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "import from package 'p', which is declared after "
                            "the scope importing it",
                            2, "26.3"));
}

TEST(PackageImport, ReferenceBeforeTheWildcardImportIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p; int x = 5; endpackage\n"
             "module m;\n"
             "  int y;\n"
             "  initial begin y = x; end\n"
             "  import p::*;\n"
             "  initial begin y = x; end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to 'x' precedes the wildcard import of "
                            "package 'p' that declares it",
                            4, "26.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "reference to 'x' precedes the wildcard import of "
                             "package 'p' that declares it",
                             6, "26.3"));
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
             "  import p1::*;\n"
             "  import p2::*;\n"
             "  int y;\n"
             "  initial y = X;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to 'X' is ambiguous between wildcard "
                            "imports of packages 'p1' and 'p2'",
                            11, "26.3"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'B'", 8,
                            "23.9"));
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'FALSE'", 7,
                            "23.9"));
}

TEST(PackageImport, WildcardImportOfEnumBringsLiteralsIntoScope) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package q;\n"
      "  typedef enum { ORIGINAL, FALSE } teeth_t;\n"
      "endpackage\n"
      "module m;\n"
      "  import q::*;\n"
      "  teeth_t myteeth;\n"
      "  initial myteeth = FALSE;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("teeth_t");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 2u);
  EXPECT_EQ(it->second[1].name, "FALSE");
  EXPECT_EQ(it->second[1].value, 1);
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier "
                            "'nonexistent_identifier'",
                            3, "23.9"));
}

TEST(PackageImport, BodyImportedTypedefSizesTheVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package q;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n"
      "module m;\n"
      "  import q::*;\n"
      "  byte_t data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* data = FindVar(design, "m", "data");
  ASSERT_NE(data, nullptr);
  EXPECT_EQ(data->width, 8u);
}

TEST(PackageImport, ExplicitBodyImportOfTypedefSizesTheVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package q;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n"
      "module m;\n"
      "  import q::byte_t;\n"
      "  byte_t data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* data = FindVar(design, "m", "data");
  ASSERT_NE(data, nullptr);
  EXPECT_EQ(data->width, 8u);
}

TEST(PackageImport, BodyImportedParameterSizesTheVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package q;\n"
      "  parameter int W = 8;\n"
      "endpackage\n"
      "module m;\n"
      "  import q::*;\n"
      "  logic [W-1:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* data = FindVar(design, "m", "data");
  ASSERT_NE(data, nullptr);
  EXPECT_EQ(data->width, 8u);
}

TEST(PackageImport, BodyImportedEnumTypedefNamesTheEnumType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package q;\n"
      "  typedef enum { ORIGINAL, FALSE } teeth_t;\n"
      "endpackage\n"
      "module m;\n"
      "  import q::*;\n"
      "  teeth_t myteeth;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* myteeth = FindVar(design, "m", "myteeth");
  ASSERT_NE(myteeth, nullptr);
  EXPECT_EQ(myteeth->enum_type_name, "teeth_t");
}

TEST(PackageImport, ImportedTypedefDoesNotReachAnotherModule) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "package q;\n"
      "  typedef logic [15:0] word_t;\n"
      "endpackage\n"
      "module a;\n"
      "  import q::*;\n"
      "  word_t x;\n"
      "endmodule\n"
      "module b;\n"
      "  localparam word_t = 1;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* x = FindVar(design, "a", "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->width, 16u);
  EXPECT_NE(FindParam(design, "b", "word_t"), nullptr);
}

TEST(PackageImport, ImportedParameterDoesNotReachAnotherModule) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "package q;\n"
      "  parameter int W = 16;\n"
      "endpackage\n"
      "module a;\n"
      "  import q::*;\n"
      "  logic [W-1:0] x;\n"
      "endmodule\n"
      "module b;\n"
      "  logic [W-1:0] y;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  const auto* x = FindVar(design, "a", "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->width, 16u);
  const auto* y = FindVar(design, "b", "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->width, 1u);
}

TEST(PackageReference, ScopedTypedefSizesTheVariableWithoutImport) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  typedef shortint word_t;\n"
      "endpackage\n"
      "module m;\n"
      "  pkg::word_t v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* v = FindVar(design, "m", "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 16u);
}

TEST(PackageImport,
     ImportedIdentifierNotVisibleViaHierRefInARandsequenceCodeBlock) {
  ElabFixture f;
  ElaborateSrc(
      "package pkg;\n"
      "  int x;\n"
      "endpackage\n"
      "module child;\n"
      "  import pkg::x;\n"
      "endmodule\n"
      "module top;\n"
      "  child c();\n"
      "  int y;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { y = c.x; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference 'c.x' targets a name "
                            "imported into 'child' from a package",
                            12, "26.3"));
}

TEST(PackageImport,
     ImportedIdentifierNotVisibleViaHierRefInARandsequenceWeightCodeBlock) {
  ElabFixture f;
  ElaborateSrc(
      "package pkg;\n"
      "  int x;\n"
      "endpackage\n"
      "module child;\n"
      "  import pkg::x;\n"
      "endmodule\n"
      "module top;\n"
      "  child c();\n"
      "  int y;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { y = c.x; };\n"
      "      alt : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference 'c.x' targets a name "
                            "imported into 'child' from a package",
                            12, "26.3"));
}

void ExpectUnknownScopeBaseIn(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "module m;\n  int x;\n  initial\n    " + stmt + "\nendmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved package or scope 'nope'",
                            LineHolding(src, "x = nope::y;"), "26.3"));
}

TEST(PackageImport, UnknownScopeBaseInAnAssertionPassStmt) {
  ExpectUnknownScopeBaseIn("assert (x) x = nope::y;");
}

TEST(PackageImport, UnknownScopeBaseInAnAssertionFailStmt) {
  ExpectUnknownScopeBaseIn("assert (x) else x = nope::y;");
}

TEST(PackageImport, UnknownScopeBaseInARandcaseItem) {
  ExpectUnknownScopeBaseIn("randcase 1: x = nope::y; endcase");
}

TEST(PackageImport, UnknownScopeBaseInARandsequenceCodeBlock) {
  ExpectUnknownScopeBaseIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { x = nope::y; };\n"
      "      endsequence\n"
      "    end");
}

TEST(PackageImport, UnknownScopeBaseInARandsequenceWeightCodeBlock) {
  ExpectUnknownScopeBaseIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : alt := 1 { x = nope::y; };\n"
      "        alt : { x = 1; };\n"
      "      endsequence\n"
      "    end");
}

void ExpectWildcardAmbiguityIn(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "package p1;\n  parameter int X = 1;\nendpackage\n"
      "package p2;\n  parameter int X = 2;\nendpackage\n"
      "module m;\n  import p1::*;\n  import p2::*;\n  int y;\n"
      "  initial\n    " +
      stmt + "\nendmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to 'X' is ambiguous between wildcard "
                            "imports of packages 'p1' and 'p2'",
                            LineHolding(src, "y = X;"), "26.3"));
}

TEST(PackageImport, WildcardAmbiguityInARandsequenceCodeBlock) {
  ExpectWildcardAmbiguityIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { y = X; };\n"
      "      endsequence\n"
      "    end");
}

TEST(PackageImport, WildcardAmbiguityInARandsequenceWeightCodeBlock) {
  ExpectWildcardAmbiguityIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : alt := 1 { y = X; };\n"
      "        alt : { y = 1; };\n"
      "      endsequence\n"
      "    end");
}

}  // namespace
