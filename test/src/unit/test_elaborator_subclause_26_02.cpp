#include <gtest/gtest.h>

#include <cstdint>

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

// §26.2 (printed page 808 of ~/IEEE 1800-2023.pdf): a package shall not refer
// to an item declared in the compilation-unit scope, and a package item shall
// hold no hierarchical reference to an identifier outside the package. The
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

// §26.2 (printed page 808): a package item may reference what the package
// declares and what an import makes visible in it, and §26.3 (printed 810)
// has a wildcard import make every declaration of the imported package
// visible, so `r.push_back(v)` in p1's function names p0's queue r through
// p1's `import p0::*`; the head of that member access is no hierarchical
// reference. Held to p1's own names and the packages' names alone, the check
// reported r at line 7.
TEST(PackageDeclarationElaboration,
     WildcardImportedQueueNamedBareInPackageFunctionAccepted) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("package p0;\n"
             "  int r[$];\n"
             "endpackage\n"
             "package p1;\n"
             "  import p0::*;\n"
             "  function void addr(int v);\n"
             "    r.push_back(v);\n"
             "  endfunction\n"
             "endpackage\n"
             "module top;\n"
             "  initial p1::addr(3);\n"
             "endmodule\n",
             f));
}

// §26.3 (printed page 810): an explicit import makes its one name visible,
// so `import p0::r` admits `r.push_back(v)` as the wildcard form does.
TEST(PackageDeclarationElaboration,
     ExplicitlyImportedQueueNamedBareInPackageFunctionAccepted) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("package p0;\n"
             "  int r[$];\n"
             "endpackage\n"
             "package p1;\n"
             "  import p0::r;\n"
             "  function void addr(int v);\n"
             "    r.push_back(v);\n"
             "  endfunction\n"
             "endpackage\n"
             "module top;\n"
             "  initial p1::addr(3);\n"
             "endmodule\n",
             f));
}

// The import admits the names the imported package provides and nothing
// else: `top.x` inside the same function is a hierarchical reference to a
// module, which §26.2 forbids a package item, and it is reported at its own
// line, the wildcard import beside it notwithstanding. A check that took an
// importing package's every member access for an imported name would let it
// through.
TEST(PackageDeclarationElaboration,
     HierarchicalReferenceBesideAWildcardImportRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p0;\n"
             "  int r[$];\n"
             "endpackage\n"
             "package p1;\n"
             "  import p0::*;\n"
             "  function void addr(int v);\n"
             "    r.push_back(v);\n"
             "    r.push_back(top.x);\n"
             "  endfunction\n"
             "endpackage\n"
             "module top;\n"
             "  int x = 4;\n"
             "  initial p1::addr(3);\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "package item contains a hierarchical reference "
                            "'top' that does not target the package itself "
                            "or an imported package",
                            8, "26.2"));
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

// §26.2 lets a package's items name what an import of another package makes
// visible, and §26.3 makes an explicit or a wildcard import do so from where
// it is written; §6.20.1 has a parameter's value a constant expression. A
// package parameter initialized from base's K reached by explicit import, by
// wildcard import and through `base::K` therefore folds to 21 and is no
// breach of §6.20.4, which the two bare forms were reported as. §26.5's
// Table 26-1 has a declaration of the importing scope win over a wildcard's
// candidate, so d4's own K, 4, is what its KK reads.
TEST(PackageDeclarationElaboration,
     PackageParameterFromImportedPackageParameterIsConstant) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package base;\n"
      "  parameter int K = 21;\n"
      "endpackage\n"
      "package d1;\n"
      "  parameter int KK = base::K;\n"
      "endpackage\n"
      "package d2;\n"
      "  import base::K;\n"
      "  parameter int KK = K;\n"
      "endpackage\n"
      "package d3;\n"
      "  import base::*;\n"
      "  localparam int KK = K;\n"
      "endpackage\n"
      "package d4;\n"
      "  parameter int K = 4;\n"
      "  import base::*;\n"
      "  parameter int KK = K;\n"
      "endpackage\n"
      "module top;\n"
      "  localparam int A = d1::KK;\n"
      "  localparam int B = d2::KK;\n"
      "  localparam int C = d3::KK;\n"
      "  localparam int D = d4::KK;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto expect_value = [design](const char* name, int64_t value) {
    const auto* param = FindParam(design, "top", name);
    ASSERT_NE(param, nullptr) << name;
    EXPECT_TRUE(param->is_resolved) << name;
    EXPECT_EQ(param->resolved_value, value) << name;
  };
  expect_value("A", 21);
  expect_value("B", 21);
  expect_value("C", 21);
  expect_value("D", 4);
}

// The binding reaches no further than the import: a package that imports
// nothing and names base's K bare still reads a name no constant of its scope
// holds, which §6.20.4 rejects as it did before.
TEST(PackageDeclarationElaboration,
     PackageParameterNamingUnimportedPackageParameterRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package base;\n"
             "  parameter int K = 21;\n"
             "endpackage\n"
             "package d5;\n"
             "  parameter int KK = K;\n"
             "endpackage\n"
             "module top;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "localparam 'KK' initializer is not a constant "
                            "expression",
                            5, "6.20.4"));
}

// §26.7 (printed pages 816-817 of ~/IEEE 1800-2023.pdf) gives every compilation
// unit the built-in package std, whose declarations -- Annex G's semaphore,
// mailbox, randomize, process and weak_reference (printed 1257-1258) -- are
// visible everywhere as a wildcard import makes them, and names them behind
// the `std::` qualifier as well. A package function's `process::self()`,
// `std::process::self()` and a `semaphore` local's `s.put(1)` are therefore
// references to an imported package, not §26.2's forbidden hierarchical
// reference; the shape is uvm_globals.svh's, every uvm-tagged file of
// sv-tests standing on it.
TEST(PackageDeclarationElaboration,
     StdPackageMemberAsAScopeRootInsideAPackageFunctionAccepted) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  function void f();\n"
             "    process h;\n"
             "    semaphore s = new(1);\n"
             "    h = process::self();\n"
             "    h = std::process::self();\n"
             "    s.put(1);\n"
             "  endfunction\n"
             "endpackage\n"
             "module top;\n"
             "  initial p::f();\n"
             "endmodule\n",
             f));
  EXPECT_FALSE(f.has_errors);
}

// A root that is neither std nor one of its members is still the
// hierarchical reference §26.2 forbids, beside the accepted `process::`.
TEST(PackageDeclarationElaboration,
     UnknownScopeRootBesideAStdPackageMemberStillRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p;\n"
             "  function int f();\n"
             "    process h;\n"
             "    h = process::self();\n"
             "    return top.x;\n"
             "  endfunction\n"
             "endpackage\n"
             "module top;\n"
             "  int x = 4;\n"
             "  int y;\n"
             "  initial y = p::f();\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "package item contains a hierarchical reference "
                            "'top' that does not target the package itself "
                            "or an imported package",
                            5, "26.2"));
}

}  // namespace
