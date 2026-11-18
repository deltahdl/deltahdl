#include <gtest/gtest.h>

#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(UpwardNameReferenceElaboration, UpwardVariableReferenceResolves) {
  EXPECT_TRUE(
      ElabOk("module child;\n"
             "  initial parent.v = 1;\n"
             "endmodule\n"
             "module parent;\n"
             "  integer v;\n"
             "  child c1();\n"
             "endmodule\n"));
}

TEST(UpwardNameReferenceElaboration, UpwardNetReferenceResolves) {
  EXPECT_TRUE(
      ElabOk("module child;\n"
             "  wire w;\n"
             "  assign w = parent.n;\n"
             "endmodule\n"
             "module parent;\n"
             "  wire n;\n"
             "  child c1();\n"
             "endmodule\n"));
}

TEST(UpwardNameReferenceElaboration, UpwardParameterReferenceResolves) {
  EXPECT_TRUE(
      ElabOk("module child;\n"
             "  integer k;\n"
             "  initial k = parent.P;\n"
             "endmodule\n"
             "module parent;\n"
             "  parameter int P = 8;\n"
             "  child c1();\n"
             "endmodule\n"));
}

TEST(UpwardNameReferenceElaboration, UpwardTaskReferenceResolves) {
  EXPECT_TRUE(
      ElabOk("module child;\n"
             "  initial parent.t();\n"
             "endmodule\n"
             "module parent;\n"
             "  task t;\n"
             "  endtask\n"
             "  child c1();\n"
             "endmodule\n"));
}

TEST(UpwardNameReferenceElaboration, UpwardFunctionReferenceResolves) {
  EXPECT_TRUE(
      ElabOk("module child;\n"
             "  integer x;\n"
             "  initial x = parent.f(1);\n"
             "endmodule\n"
             "module parent;\n"
             "  function int f(int y);\n"
             "    return y + 1;\n"
             "  endfunction\n"
             "  child c1();\n"
             "endmodule\n"));
}

TEST(UpwardNameReferenceElaboration, UpwardNamedBlockReferenceResolves) {
  EXPECT_TRUE(
      ElabOk("module child;\n"
             "  integer r;\n"
             "  initial r = parent.blk.v;\n"
             "endmodule\n"
             "module parent;\n"
             "  initial begin : blk\n"
             "    integer v;\n"
             "    v = 7;\n"
             "  end\n"
             "  child c1();\n"
             "endmodule\n"));
}

TEST(UpwardNameReferenceElaboration, UpwardPortReferenceResolves) {
  EXPECT_TRUE(
      ElabOk("module child;\n"
             "  integer x;\n"
             "  initial x = parent.p;\n"
             "endmodule\n"
             "module parent(input logic p);\n"
             "  child c1();\n"
             "endmodule\n"));
}

TEST(UpwardNameReferenceElaboration, CanonicalFourModuleExampleElaborates) {
  EXPECT_TRUE(
      ElabOk("module c;\n"
             "  integer i;\n"
             "  initial begin\n"
             "    i = 1;\n"
             "    b.i = 1;\n"
             "  end\n"
             "endmodule\n"
             "module b;\n"
             "  integer i;\n"
             "  c b_c1();\n"
             "  c b_c2();\n"
             "endmodule\n"
             "module a;\n"
             "  integer i;\n"
             "  b a_b1();\n"
             "endmodule\n"));
}

TEST(UpwardNameReferenceElaboration,
     ScopeNameFoundInCurrentScopeResolvesDownward) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  integer r;\n"
             "  initial begin : blk\n"
             "    integer v;\n"
             "    v = 5;\n"
             "    r = blk.v;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(UpwardNameReferenceElaboration,
     DISABLED_ScopeNameFoundInInstantiationParentScope) {
  ElabFixture f;
  ElaborateSrc(
      "module leaf;\n"
      "  integer r;\n"
      "  initial r = sib.v;\n"
      "endmodule\n"
      "module parent;\n"
      "  integer v;\n"
      "  leaf sib();\n"
      "  leaf ref_src();\n"
      "endmodule\n",
      f, "parent");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference 'sib.v' is unresolved", 3,
                            "23.8"));
}

TEST(UpwardNameReferenceElaboration, AScopeNameInTheParentReachesItsItem) {
  EXPECT_TRUE(
      ElabOk("module leaf;\n"
             "  integer v;\n"
             "endmodule\n"
             "module probe;\n"
             "  integer r;\n"
             "  initial r = sib.v;\n"
             "endmodule\n"
             "module parent;\n"
             "  leaf sib();\n"
             "  probe ref_src();\n"
             "endmodule\n"));
}

TEST(UpwardNameReferenceElaboration, FirstNameDeclaredNowhereIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  rand bit [1:0] a;\n"
      "endclass\n"
      "module m;\n"
      "  int x;\n"
      "  initial void'(nosuch.x.randomize() with { a > 0; });\n"
      "  initial void'(nosuch2.randomize());\n"
      "  initial x = nosuch3.y;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical name 'nosuch' resolves to no "
                            "declaration",
                            6, "23.8"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical name 'nosuch2' resolves to no "
                            "declaration",
                            7, "23.8"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical name 'nosuch3' resolves to no "
                            "declaration",
                            8, "23.8"));
}

TEST(UpwardNameReferenceElaboration, FirstNameDeclaredNowhereInAFunction) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int g();\n"
      "    return nosuch.v;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical name 'nosuch' resolves to no "
                            "declaration",
                            3, "23.8"));
}

TEST(UpwardNameReferenceElaboration, DeclaredFirstNamesAreNotReported) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  int pv;\n"
             "endpackage\n"
             "interface ifc(input logic clk);\n"
             "  logic v;\n"
             "endinterface\n"
             "class K;\n"
             "  int n;\n"
             "endclass\n"
             "module leaf;\n"
             "  int w;\n"
             "  initial w = top.tv;\n"
             "endmodule\n"
             "module top(ifc bus);\n"
             "  import p::*;\n"
             "  typedef struct { int a; } s_t;\n"
             "  s_t s;\n"
             "  K h = new;\n"
             "  string str;\n"
             "  int q[$];\n"
             "  event e;\n"
             "  int tv, r;\n"
             "  logic clk;\n"
             "  clocking cb @(posedge clk); input tv; endclocking\n"
             "  function int f(); static int cnt; return cnt; endfunction\n"
             "  if (1) begin : g\n"
             "    int gv;\n"
             "  end\n"
             "  leaf u();\n"
             "  initial begin : blk\n"
             "    int bv;\n"
             "    r = s.a + h.n + str.len() + q.size() + bus.v + f.cnt;\n"
             "    r = blk.bv + g.gv + u.w + cb.tv + top.tv;\n"
             "    r = q.sum() with (item * 2);\n"
             "    if (e.triggered) r = 1;\n"
             "    r = p::pv;\n"
             "  end\n"
             "endmodule\n"
             "module tb;\n"
             "  logic clk;\n"
             "  ifc i(clk);\n"
             "  top t(i);\n"
             "endmodule\n"));
}

TEST(UpwardNameReferenceElaboration,
     DISABLED_AChildInstancesNamedOrGenerateBlockIsNotReachedByItsBareName) {
  ElabFixture f;
  ElaborateSrc(
      "module sub(input logic clk);\n"
      "  initial begin : blk static int x = 3; end\n"
      "  if (1) begin : gb int y = 4; end\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk;\n"
      "  int r;\n"
      "  sub u(clk);\n"
      "  initial begin\n"
      "    r = blk.x;\n"
      "    r = gb.y;\n"
      "    r = u.blk.x + u.gb.y;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical name 'blk' resolves to no declaration", 10, "23.8"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical name 'gb' resolves to no declaration",
                            11, "23.8"));
  EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), 12));
}

TEST(UnresolvedFirstNameScopes, InATaskOfAModule) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n  int r;\n  task tk;\n    r = nosuch.v;\n  "
      "endtask\nendmodule\n",
      f, "t");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical name 'nosuch' resolves to no declaration", 4, "23.8"));
}

TEST(UnresolvedFirstNameScopes, DISABLED_InAMethodOfAClassInAModule) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n  class C;\n    function int f();\n      return nosuch.v;\n  "
      "  endfunction\n  endclass\nendmodule\n",
      f, "t");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical name 'nosuch' resolves to no declaration", 4, "23.8"));
}

TEST(UnresolvedFirstNameScopes, InAProgram) {
  ElabFixture f;
  ElaborateSrc("program t;\n  int r;\n  initial r = nosuch.v;\nendprogram\n", f,
               "t");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical name 'nosuch' resolves to no declaration", 3, "23.8"));
}

TEST(UnresolvedFirstNameScopes, InAnInterface) {
  ElabFixture f;
  ElaborateSrc(
      "interface i;\n  int r;\n  initial r = nosuch.v;\nendinterface\nmodule "
      "t;\n  i u();\nendmodule\n",
      f, "t");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical name 'nosuch' resolves to no declaration", 3, "23.8"));
}

TEST(UnresolvedFirstNameScopes, DISABLED_InsideANamedGenerateBlock) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n  if (1) begin : g\n    int r;\n    initial r = nosuch.v;\n  "
      "end\nendmodule\n",
      f, "t");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical name 'nosuch' resolves to no declaration", 4, "23.8"));
}

TEST(UnresolvedFirstNameScopes, InAPackageSubroutine) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n  function int f();\n    return nosuch.v;\n  "
      "endfunction\nendpackage\nmodule t;\nendmodule\n",
      f, "t");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "package item contains a hierarchical reference 'nosuch' that does not "
      "target the package itself or an imported package",
      3, "26.2"));
}

TEST(UnresolvedFirstNameScopes, InACompilationUnitSubroutine) {
  ElabFixture f;
  ElaborateSrc(
      "function int f();\n  return nosuch.v;\nendfunction\nmodule "
      "t;\nendmodule\n",
      f, "t");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical name 'nosuch' in a compilation-unit task or function is "
      "read from $root, where no top-level instance 'nosuch' stands",
      2, "3.12.1"));
}

TEST(RootedNameResolution, DISABLED_NamesThatMatchNothingAreReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int y = 1, r;\n"
      "  initial begin\n"
      "    r = $root.nosuch;\n"
      "    r = $root.nosuch.v;\n"
      "    r = $root.t.nosuch;\n"
      "  end\n"
      "endmodule\n",
      f, "t");
  const std::vector<Diagnostic>& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "hierarchical reference '$root.nosuch' is unresolved", 4, "23.6"));
  EXPECT_TRUE(ReportedError(
      diags, "hierarchical reference '$root.nosuch.v' is unresolved", 5,
      "23.6"));
  EXPECT_TRUE(ReportedError(
      diags, "hierarchical reference '$root.t.nosuch' is unresolved", 6,
      "23.6"));
}

TEST(RootedNameResolution, ANameToADeclaredVariableIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int y = 1, r;\n"
             "  initial r = $root.t.y;\n"
             "endmodule\n"));
}

}  // namespace
