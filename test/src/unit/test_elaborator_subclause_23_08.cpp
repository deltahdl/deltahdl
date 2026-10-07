#include <gtest/gtest.h>

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

// §23.8: the upward reference is read in a procedural assignment rather than in
// a localparam initializer, because §6.20.2 rules that a value parameter may be
// set only to an expression of literals, value parameters or local parameters,
// genvars, enumerated names, or a constant function of those, and forbids
// hierarchical names. The vehicle a §23.8 case uses has to be one the vehicle's
// own clause permits, and every other case in this file reads its upward name
// the same way.
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

TEST(UpwardNameReferenceElaboration, ScopeNameFoundInInstantiationParentScope) {
  EXPECT_TRUE(
      ElabOk("module leaf;\n"
             "  integer r;\n"
             "  initial r = sib.v;\n"
             "endmodule\n"
             "module parent;\n"
             "  integer v;\n"
             "  leaf sib();\n"
             "  leaf ref_src();\n"
             "endmodule\n"));
}

// §23.8: the first name of a hierarchical name is looked for downward and
// then upward, as an instance, a scope or a module name, and one no scope
// answers names nothing. nosuch, nosuch2 and nosuch3 are declared nowhere,
// as a method call's receiver, alone and with a member between, and on an
// assignment's right side; each was accepted.
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

// The same in a function of the module: a read nothing declares the head of.
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

// Every head here is something a name resolves to: a variable of a structure,
// a class handle, a string, a queue and an event of the module, a port of an
// interface, a clocking block, a function's static local through the
// function's name, a named block, a generate block, an instance, a module
// name reached upward, a package's variable brought in by an import, and an
// array method's `with` clause reading its iterator. None is reported.
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

}  // namespace
