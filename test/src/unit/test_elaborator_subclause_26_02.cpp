#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

namespace {

TEST(PackageDeclarationElaboration,
     NetWithImplicitContinuousAssignmentRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  wire w = 1'b0;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net declaration with implicit continuous "
                            "assignment is not allowed in a package",
                            2, "26.2"));
}

TEST(PackageDeclarationElaboration, InitialBlockInPackageRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  int x;\n"
             "  initial x = 1;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "process is not allowed in a package", 3, "26.2"));
}

TEST(PackageDeclarationElaboration, AlwaysBlockInPackageRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  int x;\n"
             "  always @(*) x = 1;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "process is not allowed in a package", 3, "26.2"));
}

TEST(PackageDeclarationElaboration, FinalBlockInPackageRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  int x;\n"
             "  final x = 1;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "process is not allowed in a package", 3, "26.2"));
}

// §26.2: because a package may hold processes only inside checkers, a
// combinational always procedure sitting directly in the package body is
// rejected, like the general always/initial/final cases above.
TEST(PackageDeclarationElaboration, AlwaysCombBlockInPackageRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  int x;\n"
             "  always_comb x = 1;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "process is not allowed in a package", 3, "26.2"));
}

TEST(PackageDeclarationElaboration, AlwaysFfBlockInPackageRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  int x;\n"
             "  logic clk;\n"
             "  always_ff @(posedge clk) x <= 1;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "process is not allowed in a package", 4, "26.2"));
}

TEST(PackageDeclarationElaboration, AlwaysLatchBlockInPackageRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  int x;\n"
             "  logic en;\n"
             "  always_latch if (en) x = 1;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "process is not allowed in a package", 4, "26.2"));
}

// §26.2 explicitly permits populating a package with nets; only a net carrying
// an implicit continuous assignment is barred. A bare net declaration therefore
// elaborates cleanly — the accepting boundary of the rule negated above.
TEST(PackageDeclarationElaboration, NetWithoutContinuousAssignmentAccepted) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  wire w;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n"));
}

TEST(PackageDeclarationElaboration, HierarchicalReferenceFromPackageRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module other;\n"
             "  int hidden;\n"
             "endmodule\n"
             "package pkg;\n"
             "  int leak = other.hidden;\n"
             "endpackage\n"
             "module m;\n"
             "  other o();\n"
             "  import pkg::*;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "package item contains a hierarchical reference "
                            "'other'",
                            5, "26.2"));
}

TEST(PackageDeclarationElaboration,
     CompilationUnitScopeReferenceFromPackageRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("int cu_scope_var = 7;\n"
             "package pkg;\n"
             "  int leak = cu_scope_var;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "package item references 'cu_scope_var' from the "
                            "compilation-unit scope",
                            3, "26.2"));
}

TEST(PackageDeclarationElaboration, SingleTimeunitInPackageHeadAccepted) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  timeunit 1ns;\n"
             "endpackage\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(PackageDeclarationElaboration,
     TimeunitFollowedByTimeprecisionInPackageHeadAccepted) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  timeunit 1ns;\n"
             "  timeprecision 1ps;\n"
             "endpackage\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(PackageDeclarationElaboration, TimeunitsRepeatMatchAccepted) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  timeunit 1ns;\n"
             "  timeunit 1ns;\n"
             "endpackage\n"
             "module m;\n"
             "endmodule\n"));
}

// §26.2 (printed page 808 of ~/LRM.pdf): a package shall not refer to an
// item declared in the compilation-unit scope, and a package item shall hold
// no hierarchical reference to an identifier outside the package. The
// checks read a package variable's initializer alone, so a package
// function's body reading `cu_var` or `top.v` elaborated clean.
TEST(PackageDeclarationElaboration,
     CompilationUnitScopeReferenceInPackageFunctionBodyRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("int cu_var = 3;\n"
             "package p;\n"
             "  function int f(); return cu_var; endfunction\n"
             "endpackage\n"
             "module top;\n"
             "  int r;\n"
             "  initial r = p::f();\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "package item references 'cu_var' from the "
                            "compilation-unit scope",
                            3, "26.2"));
}

TEST(PackageDeclarationElaboration,
     HierarchicalReferenceInPackageFunctionBodyRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p;\n"
             "  function int f(); return top.v; endfunction\n"
             "endpackage\n"
             "module top;\n"
             "  int v = 4;\n"
             "  int r;\n"
             "  initial r = p::f();\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "package item contains a hierarchical reference "
                            "'top'",
                            2, "26.2"));
}

// The names a package subroutine declares itself -- a formal, a local of the
// body or of a block in it, the function's result -- and those the package
// declares or imports are the package's, whatever a compilation-unit item
// spells the same; a member access through such a name is no hierarchical
// reference.
TEST(PackageDeclarationElaboration,
     PackageFunctionBodyNamingItsOwnLocalsAndPackageItemsAccepted) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("int x = 1;\n"
             "int y = 2;\n"
             "int z = 3;\n"
             "int h = 4;\n"
             "package q;\n"
             "  int w = 5;\n"
             "endpackage\n"
             "package p;\n"
             "  import q::*;\n"
             "  typedef struct { int a; } pair_t;\n"
             "  int k = 6;\n"
             "  function int g(int x);\n"
             "    return x;\n"
             "  endfunction\n"
             "  function automatic int f(pair_t h);\n"
             "    int y;\n"
             "    y = h.a + k + w + g(2);\n"
             "    begin\n"
             "      int z;\n"
             "      z = y;\n"
             "      f = z;\n"
             "    end\n"
             "  endfunction\n"
             "endpackage\n"
             "module top;\n"
             "endmodule\n",
             f));
}

// §26.2 with §6.20.1: a package localparam initialized from an earlier
// parameter of the package by its bare name folds to the computed value, and
// a module reads that value through the package scope resolution operator, a
// wildcard import and a parameter the package derived through `p::K`. Each
// is 34; a fold that lost K left the localparam unrecorded and the module's
// reads unresolved.
TEST(PackageDeclarationElaboration,
     LocalparamDerivedFromPackageParameterByBareNameFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  parameter int K = 17;\n"
      "  localparam int L = K * 2;\n"
      "  parameter int M = p::K * 2;\n"
      "endpackage\n"
      "module top;\n"
      "  import p::*;\n"
      "  localparam int SCOPED = p::L;\n"
      "  localparam int IMPORTED = L;\n"
      "  localparam int VIAPKG = M;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto expect_34 = [design](const char* name) {
    const auto* param = FindParam(design, "top", name);
    ASSERT_NE(param, nullptr) << name;
    EXPECT_TRUE(param->is_resolved) << name;
    EXPECT_EQ(param->resolved_value, 34) << name;
  };
  expect_34("SCOPED");
  expect_34("IMPORTED");
  expect_34("VIAPKG");
}

}  // namespace
