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

// Table 26-1 Row B, wildcard column, exercised on the operand kind the clause's
// own example uses: enumeration constants (the FALSE/TRUE of package p). Two
// wildcard imports each supply a package-scope enum member named FALSE, so an
// unqualified reference to FALSE is ambiguous and elaboration must fail --
// exactly as for two top-level declarations of the same name. This is the
// enum-member facet of the ambiguity rule.
TEST(PackageImport, AmbiguousWildcardImportOfEnumMemberIsIllegal) {
  EXPECT_FALSE(
      ElabOk("package p1;\n"
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
             "endmodule\n"));
}

// Positive control for the rule above: a single wildcard import makes the same
// enum member directly visible, and the unqualified reference resolves cleanly.
// Distinguishes the ambiguity error from a spurious "member never visible"
// rejection.
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

// §26.5 module m example, using its actual reference form: a net declaration
// with an initializer (`wire a = c;`) references c, which forces the wildcard
// import q::* to claim c. The subsequent explicit import p::c then conflicts
// with the already-claimed name, so elaboration must fail. The prior R5 test
// drives the reference through a procedural assignment; this drives it through
// the net-declaration initializer the clause's own example uses.
TEST(PackageImport, NetInitReferenceForcesWildcardThenExplicitImportConflicts) {
  EXPECT_FALSE(
      ElabOk("package q;\n"
             "  int c;\n"
             "endpackage\n"
             "package p;\n"
             "  int c;\n"
             "endpackage\n"
             "module m;\n"
             "  import q::*;\n"
             "  wire a = c;\n"
             "  import p::c;\n"
             "endmodule\n"));
}

// Table 26-1 Row B, wildcard column, ambiguity facet reached through a net
// declaration initializer rather than a procedural assignment: two wildcard
// imports both supply x, and the unqualified reference to x inside `wire w =
// x;` is ambiguous, so elaboration must fail.
TEST(PackageImport, AmbiguousWildcardReferenceViaNetInitIsIllegal) {
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
             "  wire w = x;\n"
             "endmodule\n"));
}

// Positive control for the two tests above: a single wildcard import lets a net
// declaration initializer reference the imported name with no conflict, so
// elaboration succeeds. Guards against a spurious rejection of the net-init
// reference form itself.
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

// R1 (import colliding with a local declaration) on a typedef operand: the
// clause's example package types are typedefs, so exercise the collision with a
// locally declared typedef of the same name rather than only a variable.
TEST(PackageImport, ExplicitImportOfTypedefCollidesWithLocalTypedef) {
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  typedef logic [3:0] T;\n"
             "endpackage\n"
             "module m;\n"
             "  typedef int T;\n"
             "  import pkg::T;\n"
             "endmodule\n"));
}

// R1 on a parameter operand: a local localparam whose name matches an
// explicitly imported package parameter is a collision.
TEST(PackageImport, ExplicitImportOfParameterCollidesWithLocalParameter) {
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  parameter int P = 1;\n"
             "endpackage\n"
             "module m;\n"
             "  localparam int P = 2;\n"
             "  import pkg::P;\n"
             "endmodule\n"));
}

// R1 on an enumeration-constant operand, local side: the importing scope
// declares an enum whose member X is directly visible in the scope (6.19), so
// explicitly importing a package name X collides with that local member.
// Verifies that a locally declared enum member participates in import-collision
// detection, not just the enum type name.
TEST(PackageImport, ExplicitImportCollidesWithLocalEnumMember) {
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  int X;\n"
             "endpackage\n"
             "module m;\n"
             "  typedef enum bit {X, Y} local_e;\n"
             "  import pkg::X;\n"
             "endmodule\n"));
}

// R5 (declaration after a wildcard-resolved reference) reached through a local
// enum member: X is referenced and claimed through the wildcard import, then a
// local enum declaring a member X appears, which is illegal.
TEST(PackageImport, LocalEnumMemberDeclAfterWildcardReferenceIsIllegal) {
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  int X;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "  int d;\n"
             "  initial d = X;\n"
             "  typedef enum bit {X, Y} local_e;\n"
             "endmodule\n"));
}

// Positive control for the two enum-member tests above: when the
// wildcard-provided name is never referenced, a local enum declaring a member
// of the same name simply shadows the candidate and elaboration succeeds (a
// different member is referenced to show the local enum is otherwise usable).
// Guards against the member-registration turning legal shadowing into a
// spurious error.
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

// R2 (same name imported from two packages) on const operands, matching the
// clause's example shape where each package supplies its own c.
TEST(PackageImport, ExplicitImportOfConstFromTwoPackagesIsIllegal) {
  EXPECT_FALSE(
      ElabOk("package p;\n"
             "  const int c = 0;\n"
             "endpackage\n"
             "package q;\n"
             "  const int c = 1;\n"
             "endpackage\n"
             "module m;\n"
             "  import p::c;\n"
             "  import q::c;\n"
             "endmodule\n"));
}

// R4 (an explicitly imported name becomes directly visible) on an enum-constant
// operand: importing a single member makes that member usable by an unqualified
// reference. Complements the wildcard-import enum-member visibility test with
// the explicit-import form.
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

}  // namespace
