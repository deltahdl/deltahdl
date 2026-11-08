#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>

#include "common/diagnostic.h"
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

TEST(PackageDeclarationElaboration, NettypeNetWithInitializerRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package pkg;\n"
             "  nettype logic [7:0] byte_net;\n"
             "  byte_net w = 8'd5;\n"
             "  byte_net u;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net declaration with implicit continuous "
                            "assignment is not allowed in a package",
                            3, "26.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "net declaration with implicit continuous "
                             "assignment is not allowed in a package",
                             4, "26.2"));
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
             "  timeunit 1ns;\n"
             "  timeprecision 1ps;\n"
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

TEST(PackageDeclarationElaboration,
     StdPackageMemberAsAScopeRootInsideAPackageFunctionAccepted) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  function void f();\n"
             "    process h;\n"
             "    static semaphore s = new(1);\n"
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

TEST(PackageDeclarationElaboration, LetFormalsAreTheLetsOwnNames) {
  EXPECT_TRUE(
      ElabOk("int a = 100;\n"
             "package p;\n"
             "  typedef struct { int m; } s_t;\n"
             "  let twice(a) = a * 2;\n"
             "  let get_m(s_t v) = v.m;\n"
             "endpackage\n"
             "module top;\n"
             "  int r;\n"
             "  initial r = p::twice(7);\n"
             "endmodule\n"));
}

TEST(PackageDeclarationElaboration, HierarchicalRefInAPackageClassMethod) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p;\n"
             "  class B; int inherited; endclass\n"
             "  class C #(int W = 2) extends B;\n"
             "    int own = W;\n"
             "    C next;\n"
             "    function int get();\n"
             "      return own + next.own + inherited + top.x;\n"
             "    endfunction\n"
             "    extern function int later();\n"
             "  endclass\n"
             "  function int C::later(); return top.x; endfunction\n"
             "endpackage\n"
             "module top;\n"
             "  int x = 4;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "package item contains a hierarchical reference "
                            "'top'",
                            7, "26.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "package item contains a hierarchical reference "
                            "'top'",
                            11, "26.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "package item contains a hierarchical reference "
                             "'next'",
                             7, "26.2"));
}

TEST(PackageDeclarationElaboration, HierarchicalRefInAPackageProperty) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p;\n"
             "  property pr; @(posedge top.clk) top.a; endproperty\n"
             "  property pq(b); @(posedge b) b |-> top.a; endproperty\n"
             "endpackage\n"
             "module top; logic clk = 0, a = 1; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "package item contains a hierarchical reference "
                            "'top'",
                            2, "26.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "package item contains a hierarchical reference "
                            "'top'",
                            3, "26.2"));
}

TEST(PackageDeclarationElaboration, HierarchicalRefInAPackageSequence) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("int v;\n"
             "package p;\n"
             "  sequence s; top.a ##1 top.b; endsequence\n"
             "  sequence sc; @(posedge top.clk) 1; endsequence\n"
             "  sequence sf(v); v ##1 v; endsequence\n"
             "  sequence sl; int v; (1, v = 1) ##1 (v == 1); endsequence\n"
             "endpackage\n"
             "module top; logic clk = 0, a = 1, b = 1; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "package item contains a hierarchical reference "
                            "'top'",
                            3, "26.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "package item contains a hierarchical reference "
                            "'top'",
                            4, "26.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "package item references 'v' from the "
                             "compilation-unit scope",
                             5, "26.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "package item references 'v' from the "
                             "compilation-unit scope",
                             6, "26.2"));
}

TEST(PackageDeclarationElaboration, HierarchicalRefInAPackagePropertySequence) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p;\n"
             "  property pa(b); @(posedge b) top.a |-> b; endproperty\n"
             "  property ps(b); @(posedge b) b ##1 top.a; endproperty\n"
             "endpackage\n"
             "module top; logic a = 1; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "package item contains a hierarchical reference "
                            "'top'",
                            2, "26.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "package item contains a hierarchical reference "
                            "'top'",
                            3, "26.2"));
}

TEST(PackageDeclarationElaboration,
     HierarchicalRefInAPackageSequenceOfAnyShape) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p;\n"
             "  typedef struct packed { logic f; } st_t;\n"
             "  st_t w;\n"
             "  sequence s; 1 ##1 first_match(top.a ##1 1); endsequence\n"
             "  sequence sc; @(posedge top.clk) 1 ##1 first_match(w ##1 1); "
             "endsequence\n"
             "  sequence sw; 1 ##1 first_match(w.f ##1 1); endsequence\n"
             "  sequence sf(v); 1 ##1 first_match(v.f ##1 1); endsequence\n"
             "endpackage\n"
             "module top; logic clk = 0, a = 1; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "package item contains a hierarchical reference "
                            "'top'",
                            4, "26.2"));
  const auto& diags = f.diag.Diagnostics();
  EXPECT_EQ(std::count_if(diags.begin(), diags.end(),
                          [](const Diagnostic& d) {
                            return d.loc.line == 5 &&
                                   d.message.find(
                                       "hierarchical reference "
                                       "'top'") != std::string::npos;
                          }),
            1);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "package item contains a hierarchical reference "
                             "'w'",
                             6, "26.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "package item contains a hierarchical reference "
                             "'v'",
                             7, "26.2"));
}

TEST(PackageDeclarationElaboration, CuNameInAPackageSequenceOfAnyShape) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("int v;\n"
             "package p;\n"
             "  sequence su; 1 ##1 first_match(v ##1 1); endsequence\n"
             "  sequence sf(v); 1 ##1 first_match(v ##1 1); endsequence\n"
             "  sequence sl; int v = 0; 1 ##1 first_match(v ##1 1); "
             "endsequence\n"
             "endpackage\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "package item references 'v' from the "
                            "compilation-unit scope",
                            3, "26.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "package item references 'v' from the "
                             "compilation-unit scope",
                             4, "26.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "package item references 'v' from the "
                             "compilation-unit scope",
                             5, "26.2"));
}

TEST(PackageDeclarationElaboration,
     NamesInANestedGroupOrASequenceActualOfAPackageItem) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("int v;\n"
             "package p;\n"
             "  typedef struct packed { logic f; } st_t;\n"
             "  st_t w;\n"
             "  sequence s; (top.a and 1) ##0 1; endsequence\n"
             "  sequence su; (v and 1) ##0 1; endsequence\n"
             "  sequence sw; (w.f and 1) ##0 1; endsequence\n"
             "  sequence sf(v); (v.f and v) ##0 1; endsequence\n"
             "  sequence s2(x); x ##1 1; endsequence\n"
             "  sequence sa; s2(top.b ##1 1) ##1 1; endsequence\n"
             "  property q; s2(top.c ##1 1); endproperty\n"
             "endpackage\n"
             "module top; logic a = 1, b = 1, c = 1; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "package item contains a hierarchical reference "
                            "'top'",
                            5, "26.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "package item references 'v' from the "
                            "compilation-unit scope",
                            6, "26.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "package item contains a hierarchical reference "
                             "'w'",
                             7, "26.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "package item contains a hierarchical reference "
                             "'v'",
                             8, "26.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "package item references 'v' from the "
                             "compilation-unit scope",
                             8, "26.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "package item contains a hierarchical reference "
                            "'top'",
                            10, "26.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "package item contains a hierarchical reference "
                            "'top'",
                            11, "26.2"));
}

}  // namespace
