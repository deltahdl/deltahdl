#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

namespace {

// §6.19.2's Table 6-10 (printed page 121) has a `name[N]` member generate the
// named constants name0 through nameN-1 and a `name[N:M]` member nameN through
// nameM, the written name naming no constant, and §26.6 (printed 815) makes an
// import of a declaration reached through an export an import of the original
// declaration. p2 hands on everything it imports from p1, so `p2::VAL2` and
// `p2::VAL1` name p1's constants. Before, PopulatePackageProvidedNames in
// src/elaborator/elaborator_scope_rules_names.cpp held the member under the
// written name VAL alone, and each read was reported as a name p2 neither
// declares nor exports; the "p1.VAL2" constant the registration records is
// keyed by the declaring package and answered for p1 only.
TEST(PackageImport, RangedEnumConstantsAreProvidedThroughAWildcardExport) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef enum {VAL[3]} t;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::*;\n"
             "  export p1::*;\n"
             "endpackage\n"
             "module top;\n"
             "  int r;\n"
             "  initial r = p2::VAL2 + p2::VAL1;\n"
             "endmodule\n"));
}

// The written name of a ranged member declares nothing (printed 121), so
// §26.3's scope resolution operator (printed 808) finds no declaration of p1
// under it: `p1::VAL` is reported at its own line while `p1::VAL2`, one of
// the constants the member generates, is not. Before, the provided-name walk
// admitted VAL as a declaration of p1 and the read passed.
TEST(PackageScopeReference, WrittenNameOfARangedMemberIsNoDeclaration) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p1;\n"
             "  typedef enum {VAL[3]} t;\n"
             "endpackage\n"
             "module top;\n"
             "  int r;\n"
             "  initial r = p1::VAL2;\n"
             "  initial r = p1::VAL;\n"
             "endmodule\n",
             f));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "reference to 'p1::VAL2', which package 'p1' "
                             "neither declares nor exports",
                             6, "26.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to 'p1::VAL', which package 'p1' "
                            "neither declares nor exports",
                            7, "26.3"));
}

// §26.3 (printed 810) makes every identifier a wildcard-imported package
// declares a candidate for a bare reference, and the constants a ranged
// member generates are such identifiers, for the `name[N]` form and the
// decrementing `name[N:M]` form alike (printed 121): VAL2 and W1 both resolve
// through the import, VAL2 the last of VAL0..VAL2 and W1 the last of W3..W1.
TEST(PackageImport, BareRangedEnumConstantResolvesThroughAWildcardImport) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef enum {VAL[3], W[3:1]} t;\n"
             "endpackage\n"
             "module top;\n"
             "  import p1::*;\n"
             "  int r;\n"
             "  initial r = VAL2 + W1;\n"
             "endmodule\n"));
}

// §26.3 (printed 809-810) has an explicit import make the one identifier it
// names locally visible, and a generated constant is an identifier p1
// declares, so `import p1::VAL2;` brings VAL2 in for a bare read.
TEST(PackageImport, ExplicitImportOfARangedEnumConstantIsClean) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef enum {VAL[3]} t;\n"
             "endpackage\n"
             "module top;\n"
             "  import p1::VAL2;\n"
             "  int r;\n"
             "  initial r = VAL2;\n"
             "endmodule\n"));
}

// Counting the generated constants as the declaring package's admits nothing
// else and conflicts as §26.3 (printed 810) rules: p and q each generate VAL1
// from a ranged member of their own, so the bare read on line 11 matches an
// identifier the wildcard imports of two packages both define and is reported
// as ambiguous, as a plain member of each would be.
TEST(PackageImport, GeneratedEnumConstantsOfTwoImportsAreAmbiguous) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p;\n"
             "  typedef enum {VAL[2]} t;\n"
             "endpackage\n"
             "package q;\n"
             "  typedef enum {VAL[2]} u;\n"
             "endpackage\n"
             "module top;\n"
             "  import p::*;\n"
             "  import q::*;\n"
             "  int r;\n"
             "  initial r = VAL1;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to 'VAL1' is ambiguous between wildcard "
                            "imports of packages 'p' and 'q'",
                            11, "26.3"));
}

// §6.19 (printed page 119) has an enumerated type declare its literals as
// named constants of the scope holding it, and Syntax 6-5 makes the enum form
// a data_type, so p's `enum {X, Y} v;` declares X and Y in p as a typedef
// would; §26.3 (printed 810) then makes each a candidate the wildcard import
// brings in. The module elaborates clean, Y has the backing variable an
// imported literal is read through, and a local parameter reading Y folds to
// 1, the second member of a zero-based enumeration (printed 120). Before,
// EmitEnumLiteralsOfItems in src/elaborator/elaborator_typedef.cpp walked a
// package's typedefs alone, so Y had no backing variable in the module and
}  // namespace
