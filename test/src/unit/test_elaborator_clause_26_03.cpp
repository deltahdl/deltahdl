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

// §26.3 opens by stating that the compilation of a package shall precede
// the compilation of scopes in which the package is imported.  In a
// single-compilation-unit model that translates to: an import from a
// package name that has not been declared in this compilation unit is
// illegal at elaboration time, because no compiled package supplies the
// requested symbols.
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

// §26.3: "Importing an identifier from the same package multiple times is
// allowed."  Two `import pkg::x;` statements in the same scope must not
// collide with each other.
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

// §26.3: "An explicit import shall be illegal if the imported identifier is
// declared in the same scope or explicitly imported from another package."
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

TEST(PackageImport, ExplicitImportCollidesWithExplicitImportFromAnotherPackage) {
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

// §26.3: "It shall be illegal if the wildcard import of more than one package
// within the same scope defines the same potentially locally visible
// identifier and a search for a reference matches that identifier."
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

// §26.3: "If a wildcard imported symbol is made locally visible in a scope,
// any later locally visible declaration of the same name in that scope shall
// be illegal."
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

// §26.3: "A wildcard import allows all identifiers declared within a package
// to be imported provided the identifier is not otherwise defined in the
// importing scope."  A local declaration that precedes the wildcard import
// keeps the wildcard candidate from binding to that name — the reference
// resolves to the local decl, and the module is well-formed.
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

// §26.3: "One way to use declarations made in a package is to reference them
// using the package scope resolution operator ::."  A package parameter
// referenced via `pkg::WIDTH` in a dimension must resolve at elaboration.
TEST(PackageScopeReference, PackageScopeParamResolution) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  parameter int WIDTH = 8;\n"
             "endpackage\n"
             "module m;\n"
             "  logic [pkg::WIDTH-1:0] data;\n"
             "endmodule\n"));
}

// §26.3 scope resolution applied to a package-declared type.
TEST(PackageScopeReference, PackageScopeTypeResolution) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef logic [7:0] byte_t;\n"
             "endpackage\n"
             "module m;\n"
             "  pkg::byte_t data;\n"
             "endmodule\n"));
}

// §26.3: explicit `import pkg::WIDTH;` makes the imported identifier
// directly visible in the importing scope (an unqualified `WIDTH` resolves
// in the dimension below).
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

// §26.3 opens with the example `ComplexPkg::Complex cout = ComplexPkg::mul(a,
// b);` — the scope resolution operator must work for package-declared
// functions, not just types and parameters.
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

// §26.3: "If the reference is a function or task call, all of the locally
// visible identifiers to the end of the current scope shall be searched."
// A function call appearing before the function's textual definition in
// the same module scope must still bind to that function — the search
// extends to the end of the current scope for function/task calls,
// distinguishing the rule from the point-of-reference rule used for other
// identifier references.
TEST(PackageImport, FunctionCallBindsToLaterFunctionInSameScope) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int x;\n"
             "  initial x = helper(2);\n"
             "  function int helper(int a); return a + 1; endfunction\n"
             "endmodule\n"));
}

// §26.3: "If the reference is not found within the current scope, the next
// outer lexical scope shall be searched."  A name declared at the
// compilation-unit (outer) scope must be reachable from a module's inner
// scope by the outer-scope search step (linking §26.3 search to §3.13(c)
// compilation-unit scope).
TEST(PackageImport, OuterScopeSearchFindsCompilationUnitName) {
  EXPECT_TRUE(
      ElabOk("localparam int WIDTH = 8;\n"
             "module m;\n"
             "  logic [WIDTH-1:0] data;\n"
             "endmodule\n"));
}

// §26.3: "The search algorithm shall be repeated for each outer lexical
// scope until an identifier is found that matches the reference or there
// are no more outer lexical scopes, the compilation-unit scope being the
// final scope searched.  For a reference to an identifier other than
// function or task call, it shall be illegal if no identifier can be
// found that matches the reference."  A bare reference whose name is
// neither locally declared nor brought in by any wildcard import nor
// present in an outer scope must be rejected.
TEST(PackageImport, UnresolvedReferenceIsError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int y;\n"
             "  initial y = nonexistent_identifier;\n"
             "endmodule\n"));
}

}  // namespace
