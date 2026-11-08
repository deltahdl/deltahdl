#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

namespace {

void ExpectUnresolvedProcReadIn(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "package pkg;\n  int supplied;\nendpackage\n"
      "module m;\n  import pkg::*;\n  int r;\n  initial\n    " +
      stmt + "\nendmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'absent'",
                            LineHolding(src, "r = absent;"), "23.9"));
}

TEST(PackageImport, UnresolvedProcReadInAnAssertionPassStmt) {
  ExpectUnresolvedProcReadIn("assert (r) r = absent;");
}

TEST(PackageImport, UnresolvedProcReadInAnAssertionFailStmt) {
  ExpectUnresolvedProcReadIn("assert (r) else r = absent;");
}

TEST(PackageImport, UnresolvedProcReadInARandcaseItem) {
  ExpectUnresolvedProcReadIn("randcase 1: r = absent; endcase");
}

TEST(PackageImport, UnresolvedProcReadInARandsequenceCodeBlock) {
  ExpectUnresolvedProcReadIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { r = absent; };\n"
      "      endsequence\n"
      "    end");
}

TEST(PackageImport, UnresolvedProcReadInARandsequenceWeightCodeBlock) {
  ExpectUnresolvedProcReadIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : alt := 1 { r = absent; };\n"
      "        alt : { r = 1; };\n"
      "      endsequence\n"
      "    end");
}

TEST(PackageScopeReference,
     PackageParameterOverPackageEnumMembersSizesTheVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef bit [7:0] flag_t;\n"
      "  typedef enum flag_t {\n"
      "    DEEP = (1 << 4), SHALLOW = (1 << 5), REFERENCE = (1 << 6)\n"
      "  } policy_e;\n"
      "  parameter RECURSION = (DEEP | SHALLOW | REFERENCE);\n"
      "endpackage\n"
      "module m;\n"
      "  logic [p::RECURSION-1:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* data = FindVar(design, "m", "data");
  ASSERT_NE(data, nullptr);
  EXPECT_EQ(data->width, 112u);
}

TEST(PackageScopeReference,
     PackageParameterTypedByAPackageEnumSizesTheVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef enum {\n"
      "    UNINITIALIZED, PRE_INIT, INITIALIZING, INITIALIZED, ABORTED\n"
      "  } state_e;\n"
      "  parameter state_e POST_INIT = INITIALIZED;\n"
      "endpackage\n"
      "module m;\n"
      "  logic [p::POST_INIT:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* data = FindVar(design, "m", "data");
  ASSERT_NE(data, nullptr);
  EXPECT_EQ(data->width, 4u);
}

TEST(PackageScopeReference, PackageEnumMemberSizesTheVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef enum { RED = 3, GREEN = 5 } color_t;\n"
      "endpackage\n"
      "module m;\n"
      "  logic [p::GREEN:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* data = FindVar(design, "m", "data");
  ASSERT_NE(data, nullptr);
  EXPECT_EQ(data->width, 6u);
}

TEST(PackageImport, WildcardImportedParameterOverEnumMembersHoldsItsValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef bit [7:0] flag_t;\n"
      "  typedef enum flag_t {\n"
      "    DEEP = (1 << 4), SHALLOW = (1 << 5), REFERENCE = (1 << 6)\n"
      "  } policy_e;\n"
      "  parameter RECURSION = (DEEP | SHALLOW | REFERENCE);\n"
      "endpackage\n"
      "module m;\n"
      "  import p::*;\n"
      "  localparam int K = RECURSION;\n"
      "  localparam int J = DEEP | REFERENCE;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* k = FindParam(design, "m", "K");
  ASSERT_NE(k, nullptr);
  EXPECT_TRUE(k->is_resolved);
  EXPECT_EQ(k->resolved_value, 112);
  const auto* j = FindParam(design, "m", "J");
  ASSERT_NE(j, nullptr);
  EXPECT_TRUE(j->is_resolved);
  EXPECT_EQ(j->resolved_value, 80);
}

TEST(PackageScopeReference,
     PackageParameterReadingAnEarlierOneSizesTheVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  parameter int A = 5;\n"
      "  parameter int B = A + 2;\n"
      "endpackage\n"
      "module m;\n"
      "  logic [p::B-1:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* data = FindVar(design, "m", "data");
  ASSERT_NE(data, nullptr);
  EXPECT_EQ(data->width, 7u);
}

TEST(PackageScopeReference, WildcardImportedClassIsAScopeBase) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  class pk_t;\n"
      "    static function int get(); return 7; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "module m;\n"
      "  import p::*;\n"
      "  int c;\n"
      "  initial c = pk_t::get();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "reference to unresolved package or scope 'pk_t'",
                             9, "26.3"));
}

TEST(PackageScopeReference, ExplicitlyImportedClassIsAScopeBase) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  class pk_t;\n"
      "    static function int get(); return 7; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "module m;\n"
      "  import p::pk_t;\n"
      "  int c;\n"
      "  initial c = pk_t::get();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "reference to unresolved package or scope 'pk_t'",
                             9, "26.3"));
}

TEST(PackageScopeReference, AClassTheImportDoesNotNameIsNoScopeBase) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  class pk_t;\n"
      "    static function int get(); return 7; endfunction\n"
      "  endclass\n"
      "  class other_t; endclass\n"
      "endpackage\n"
      "module m;\n"
      "  import p::other_t;\n"
      "  int c;\n"
      "  initial c = pk_t::get();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved package or scope 'pk_t'",
                            10, "26.3"));
}

TEST(PackageImport, CompilationUnitWildcardImportResolvesABareRead) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  localparam int K = 5;\n"
      "endpackage\n"
      "import p::*;\n"
      "module m;\n"
      "  int c;\n"
      "  initial c = K;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "reference to unresolved identifier 'K'", 7,
                             "23.9"));
}

TEST(PackageImport, CompilationUnitWildcardImportedClassIsAScopeBase) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  class pk_t;\n"
      "    static function int get(); return 7; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "import p::*;\n"
      "module m;\n"
      "  int d;\n"
      "  initial d = pk_t::get();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "reference to unresolved package or scope 'pk_t'",
                             9, "26.3"));
}

TEST(PackageImport, CompilationUnitExplicitImportResolvesItsNameAlone) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  localparam int K = 5;\n"
      "  localparam int L = 6;\n"
      "endpackage\n"
      "import p::K;\n"
      "module m;\n"
      "  int c, d;\n"
      "  initial begin\n"
      "    c = K;\n"
      "    d = L;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "reference to unresolved identifier 'K'", 9,
                             "23.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'L'", 10,
                            "23.9"));
}

TEST(PackageImport, CuScopeWildcardImportedPackageClassIsAClassType) {
  ElabFixture f;
  ElaborateSrc(
      "package pk;\n"
      "  class B; int b = 3; endclass\n"
      "endpackage\n"
      "import pk::*;\n"
      "class D extends B; endclass\n"
      "module t;\n"
      "  B h; D d = new;\n"
      "  initial h = d;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(
      f.diag.Diagnostics(),
      "cannot assign class object handle to a non-class variable", 8, "8.4"));
}

TEST(PackageImport, HeaderWildcardImportedPackageClassIsAClassType) {
  ElabFixture f;
  ElaborateSrc(
      "package pk;\n"
      "  class B; int b = 3; endclass\n"
      "endpackage\n"
      "module t import pk::*; ();\n"
      "  class D extends B; endclass\n"
      "  B h; D d = new;\n"
      "  initial h = d;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(
      f.diag.Diagnostics(),
      "cannot assign class object handle to a non-class variable", 7, "8.4"));
}

TEST(PackageImport, ExplicitlyImportedPackageClassIsAClassType) {
  ElabFixture f;
  ElaborateSrc(
      "package pk;\n"
      "  class B; int b = 3; endclass\n"
      "endpackage\n"
      "module t;\n"
      "  import pk::B;\n"
      "  class D extends B; endclass\n"
      "  B h; D d = new;\n"
      "  initial h = d;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(
      f.diag.Diagnostics(),
      "cannot assign class object handle to a non-class variable", 8, "8.4"));
}

TEST(PackageImport, AClassTheImportDoesNotNameIsNoClassType) {
  ElabFixture f;
  ElaborateSrc(
      "package pk;\n"
      "  class B; int b = 3; endclass\n"
      "  class other_t; endclass\n"
      "endpackage\n"
      "module t;\n"
      "  import pk::other_t;\n"
      "  class D; endclass\n"
      "  B h; D d = new;\n"
      "  initial h = d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cannot assign class object handle to a non-class variable", 9, "8.4"));
}

TEST(PackageImport, WildcardLiteralAnExplicitImportNamesIsNotEmitted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef enum { FALSE, TRUE } bool_t;\n"
      "endpackage\n"
      "package q;\n"
      "  typedef enum { ORIGINAL, FALSE } teeth_t;\n"
      "endpackage\n"
      "module top2;\n"
      "  import p::*;\n"
      "  import q::teeth_t, q::ORIGINAL, q::FALSE;\n"
      "  teeth_t myteeth;\n"
      "  initial myteeth = FALSE;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(FindVar(design, "top2", "FALSE"), nullptr);
  EXPECT_NE(FindVar(design, "top2", "TRUE"), nullptr);
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("bool_t");
  ASSERT_NE(it, mod->enum_types.end());
  EXPECT_EQ(it->second.size(), 2u);
}

TEST(PackageImport, WildcardImportInAFunctionBodyResolvesItsReads) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  parameter int K = 3;\n"
             "  function int five(); return 5; endfunction\n"
             "endpackage\n"
             "module top;\n"
             "  function int calc();\n"
             "    import p::*;\n"
             "    int r;\n"
             "    r = K * five();\n"
             "    return r;\n"
             "  endfunction\n"
             "  int out;\n"
             "  initial out = calc();\n"
             "endmodule\n",
             f));
}

TEST(PackageImport, ExplicitImportInATaskBodyResolvesItsRead) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  parameter int K = 10;\n"
             "  function int trip(int a); return a * 3; endfunction\n"
             "endpackage\n"
             "module top;\n"
             "  task automatic t(output int r);\n"
             "    import p::K;\n"
             "    #3 r = trip(K);\n"
             "  endtask\n"
             "  int r;\n"
             "  initial t(r);\n"
             "endmodule\n",
             f));
}

TEST(PackageImport, AnImportInOneFunctionBodyReachesNoOtherBody) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p;\n"
             "  parameter int K = 3;\n"
             "endpackage\n"
             "module top;\n"
             "  function int a();\n"
             "    import p::*;\n"
             "    int r;\n"
             "    r = K;\n"
             "    return r;\n"
             "  endfunction\n"
             "  function int b();\n"
             "    int r;\n"
             "    r = K;\n"
             "    return r;\n"
             "  endfunction\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'K'", 13,
                            "23.9"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "reference to unresolved identifier 'K'", 8,
                             "23.9"));
}

TEST(PackageImport,
     DeclarationInitializerReadsAVariableReachedByTwoExportPaths) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  int x = 6;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::x;\n"
             "  export p1::*;\n"
             "endpackage\n"
             "package p4;\n"
             "  import p1::*;\n"
             "  export p1::*;\n"
             "  int y = x;\n"
             "endpackage\n"
             "module top;\n"
             "  import p2::*;\n"
             "  import p4::*;\n"
             "  int z = x;\n"
             "  initial $display(\"%0d %0d\", z, y);\n"
             "endmodule\n",
             f));
}

TEST(PackageImport, ExplicitAndStarExportPathsToOneDeclarationAreOneCandidate) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  int x = 6;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::x;\n"
             "  export p1::x;\n"
             "endpackage\n"
             "package p3;\n"
             "  import p1::*;\n"
             "  export *::*;\n"
             "  int w = x;\n"
             "endpackage\n"
             "package p4;\n"
             "  import p3::*;\n"
             "  export *::*;\n"
             "endpackage\n"
             "module top;\n"
             "  import p2::*;\n"
             "  import p4::*;\n"
             "  int z = x;\n"
             "endmodule\n",
             f));
}

TEST(PackageImport, ExportedAndOwnDeclarationsOfOneNameStayAmbiguous) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p1;\n"
             "  int x = 6;\n"
             "endpackage\n"
             "package p2;\n"
             "  int x = 7;\n"
             "endpackage\n"
             "package p3;\n"
             "  import p1::x;\n"
             "  export p1::*;\n"
             "endpackage\n"
             "module top;\n"
             "  import p2::*;\n"
             "  import p3::*;\n"
             "  int z = x;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to 'x' is ambiguous between wildcard "
                            "imports of packages 'p2' and 'p3'",
                            14, "26.3"));
}

TEST(PackageImport, BlockImportAfterTheReferenceRaisesNoAmbiguity) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  int x;\n"
             "endpackage\n"
             "package p2;\n"
             "  int x;\n"
             "endpackage\n"
             "module top;\n"
             "  import p::*;\n"
             "  int y;\n"
             "  if (1) begin : b\n"
             "    initial x = 1;\n"
             "    import p2::*;\n"
             "  end\n"
             "  initial #1 y = p::x + x;\n"
             "endmodule\n",
             f));
}

TEST(PackageImport, BlockImportBeforeTheReferenceHidesTheModulesCandidate) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  int x;\n"
             "endpackage\n"
             "package p2;\n"
             "  int x;\n"
             "endpackage\n"
             "module top;\n"
             "  import p::*;\n"
             "  int y, z;\n"
             "  if (1) begin : b\n"
             "    import p2::*;\n"
             "    initial z = x;\n"
             "  end\n"
             "  initial #1 y = x;\n"
             "endmodule\n",
             f));
}

TEST(PackageImport, TwoModuleImportsReachedFromABlockAreAmbiguous) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p;\n"
             "  int x;\n"
             "endpackage\n"
             "package p2;\n"
             "  int x;\n"
             "endpackage\n"
             "module top;\n"
             "  import p::*;\n"
             "  import p2::*;\n"
             "  if (1) begin : b\n"
             "    initial x = 1;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to 'x' is ambiguous between wildcard "
                            "imports of packages 'p' and 'p2'",
                            11, "26.3"));
}

TEST(PackageImport, ModuleDeclarationAfterABlocksClaimIsIllegal) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p;\n"
             "  int x;\n"
             "endpackage\n"
             "module top;\n"
             "  import p::*;\n"
             "  if (1) begin : b\n"
             "    initial x = 1;\n"
             "    int x;\n"
             "    initial x = 1;\n"
             "  end\n"
             "  int y;\n"
             "  int x;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of 'x' follows a reference resolved "
                            "through a wildcard package import",
                            12, "26.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "declaration of 'x' follows a reference resolved "
                             "through a wildcard package import",
                             8, "26.3"));
}

TEST(PackageImport, ScopedReferenceToAStructMemberEnumLiteral) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  typedef struct { enum {A, B} e; int n; } s_t;\n"
             "endpackage\n"
             "module top;\n"
             "  int r;\n"
             "  initial r = p::A + p::B;\n"
             "endmodule\n"));
}

TEST(PackageImport, WildcardImportSuppliesAStructMemberEnumLiteral) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  typedef struct { enum {A, B} e; int n; } s_t;\n"
             "endpackage\n"
             "module top;\n"
             "  import p::*;\n"
             "  int r;\n"
             "  initial r = B;\n"
             "endmodule\n"));
}

TEST(PackageImport, UnionAndNestedStructMemberEnumLiteralsAreProvided) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  typedef union { enum {U0, U1} tag; int n; } u_t;\n"
             "  typedef struct {\n"
             "    struct { enum {D0, D1 = 5} deep; int m; } inner;\n"
             "    int n;\n"
             "  } outer_t;\n"
             "  struct { enum {V0, V1} v; } sv;\n"
             "endpackage\n"
             "module top;\n"
             "  int r;\n"
             "  initial r = p::U1 + p::D1 + p::V1;\n"
             "endmodule\n"));
}

TEST(PackageImport, StructMemberEnumLiteralsOfTwoImportsAreAmbiguous) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p;\n"
             "  typedef struct { enum {A, B} e; } s_t;\n"
             "endpackage\n"
             "package q;\n"
             "  typedef struct { enum {B, C} e; } t_t;\n"
             "endpackage\n"
             "module top;\n"
             "  import p::*;\n"
             "  import q::*;\n"
             "  int r;\n"
             "  initial r = B;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to 'B' is ambiguous between wildcard "
                            "imports of packages 'p' and 'q'",
                            11, "26.3"));
}

TEST(PackageImport, ScopedReferenceToNoMemberOfTheStructStaysReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p;\n"
             "  typedef struct { enum {A, B} e; int n; } s_t;\n"
             "endpackage\n"
             "module top;\n"
             "  int r;\n"
             "  initial r = p::Z;\n"
             "  initial r = p::e;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to 'p::Z', which package 'p' neither "
                            "declares nor exports",
                            6, "26.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to 'p::e', which package 'p' neither "
                            "declares nor exports",
                            7, "26.3"));
}

}  // namespace
