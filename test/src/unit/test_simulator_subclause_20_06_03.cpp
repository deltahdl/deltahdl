#include <gtest/gtest.h>

#include <string>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(RangeSystemFunctionSim, UnboundedParameterReturnsTrue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter int p = $;\n"
      "  int result;\n"
      "  initial result = $isunbounded(p);\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(RangeSystemFunctionSim, BoundedParameterReturnsFalse) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter int p = 42;\n"
      "  int result;\n"
      "  initial result = $isunbounded(p);\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(RangeSystemFunctionSim, ResolvesPerParameterName) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter int hi = $;\n"
      "  parameter int lo = 7;\n"
      "  int r_hi;\n"
      "  int r_lo;\n"
      "  initial begin\n"
      "    r_hi = $isunbounded(hi);\n"
      "    r_lo = $isunbounded(lo);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r_hi = f.ctx.FindVariable("r_hi");
  auto* r_lo = f.ctx.FindVariable("r_lo");
  ASSERT_NE(r_hi, nullptr);
  ASSERT_NE(r_lo, nullptr);
  EXPECT_EQ(r_hi->value.ToUint64(), 1u);
  EXPECT_EQ(r_lo->value.ToUint64(), 0u);
}

TEST(RangeSystemFunctionSim, TrueResultIsOneBitWide) {
  SimFixture f;
  f.ctx.RegisterUnboundedParam("u");
  auto* expr = MakeSysCall(f.arena, "$isunbounded", {MakeId(f.arena, "u")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(RangeSystemFunctionSim, NonParameterArgumentReturnsFalse) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$isunbounded", {MakeInt(f.arena, 8)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(RangeSystemFunctionSim, HierarchicalUnboundedParameterReturnsTrue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module sub #(parameter int P = $);\n"
      "endmodule\n"
      "module t;\n"
      "  sub s();\n"
      "  int result;\n"
      "  initial result = $isunbounded(s.P);\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(RangeSystemFunctionSim, InstanceOverrideOfDollarIsUnbounded) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module sub #(parameter int P = 4, parameter Q = 4);\n"
                 "endmodule\n"
                 "interface itf #(parameter int P = 4);\n"
                 "endinterface\n"
                 "module t;\n"
                 "  sub #(.P($)) a();\n"
                 "  sub #($) b();\n"
                 "  sub #(.Q(5)) c();\n"
                 "  itf #($) i();\n"
                 "  initial $display(\"%0d %0d %0d %0d %0d\",\n"
                 "                   $isunbounded(a.P), $isunbounded(b.P),\n"
                 "                   $isunbounded(b.Q), $isunbounded(c.Q),\n"
                 "                   $isunbounded(i.P));\n"
                 "endmodule\n",
                 f),
      "1 1 0 0 1\n");
}

TEST(RangeSystemFunctionSim, HierarchicalBoundedParameterReturnsFalse) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module sub #(parameter int P = 13);\n"
      "endmodule\n"
      "module t;\n"
      "  sub s();\n"
      "  int result;\n"
      "  initial result = $isunbounded(s.P);\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(RangeSystemFunctionSim, ClassParameterHoldingDollarIsUnbounded) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("class C #(int N = $);\n"
                 "  function int ub();\n"
                 "    return $isunbounded(N);\n"
                 "  endfunction\n"
                 "endclass\n"
                 "module t;\n"
                 "  parameter int i = $;\n"
                 "  parameter int j = 5;\n"
                 "  C #() cd = new;\n"
                 "  C #(4) cs = new;\n"
                 "  initial $display(\"%0d %0d %0d %0d\", $isunbounded(i),\n"
                 "                   $isunbounded(j), cd.ub(), cs.ub());\n"
                 "endmodule\n",
                 f),
      "1 0 1 0\n");
}

TEST(RangeSystemFunctionSim, ClassParameterAssignedADollarParameterFollowsIt) {
  SimFixture f;
  EXPECT_EQ(RunCapture(
                "class C #(int N = $, int M = N);\n"
                "  localparam int L = $;\n"
                "  function int ub();\n"
                "    return $isunbounded(N) * 100 + $isunbounded(M) * 10\n"
                "           + $isunbounded(L);\n"
                "  endfunction\n"
                "endclass\n"
                "module t;\n"
                "  C a = new; C #(4) b = new; C #(.M(3)) c = new;\n"
                "  initial $display(\"%0d %0d %0d\", a.ub(), b.ub(), c.ub());\n"
                "endmodule\n",
                f),
            "111 1 101\n");
}

TEST(RangeSystemFunctionSim, OverrideNamingADollarParameterIsUnbounded) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("class C #(int N = 4);\n"
                 "  function int ub(); return $isunbounded(N); endfunction\n"
                 "endclass\n"
                 "module t;\n"
                 "  parameter int P = $;\n"
                 "  parameter int Q = 7;\n"
                 "  C #(P) d = new;\n"
                 "  C #(Q) e = new;\n"
                 "  initial $display(\"%0d %0d\", d.ub(), e.ub());\n"
                 "endmodule\n",
                 f),
      "1 0\n");
}

std::string RunIsunbounded(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

TEST(RangeSystemFunctionSim,
     DISABLED_AClassScopedOrGenerateScopedNameIsAnswered) {
  EXPECT_EQ(RunIsunbounded(
                "class C #(int N = 1);\n"
                "endclass\n"
                "module t;\n"
                "  if (1) begin : g\n"
                "    localparam Q = $;\n"
                "    localparam B = 2;\n"
                "  end\n"
                "  initial $display(\"%b %b %b %b\", $isunbounded(C#($)::N),\n"
                "    $isunbounded(C#(4)::N), $isunbounded(g.Q),\n"
                "    $isunbounded(g.B));\n"
                "endmodule\n"),
            "1 0 1 0\n");
}

TEST(RangeSystemFunctionSim, DISABLED_APackageParameterIsAnswered) {
  EXPECT_EQ(
      RunIsunbounded("package pk;\n"
                     "  parameter Q = $;\n"
                     "  parameter R = 4;\n"
                     "endpackage\n"
                     "module t;\n"
                     "  initial $display(\"%b %b\", $isunbounded(pk::Q),\n"
                     "    $isunbounded(pk::R));\n"
                     "endmodule\n"),
      "1 0\n");
}

TEST(RangeSystemFunctionSim, DISABLED_AGenerateConditionSelectsTheBlock) {
  std::string out = RunIsunbounded(
      "package pk;\n"
      "  parameter Q = $;\n"
      "endpackage\n"
      "interface qtc #(parameter int min_quiet = 0,\n"
      "                parameter int max_quiet = 0) (input logic clk);\n"
      "  if (!$isunbounded(max_quiet) && (max_quiet == 0)) begin : quiet\n"
      "    initial $display(\"%m\");\n"
      "  end else begin : bounded\n"
      "    initial $display(\"%m\");\n"
      "  end\n"
      "  if ($isunbounded(pk::Q)) begin : yes\n"
      "    initial $display(\"%m\");\n"
      "  end\n"
      "endinterface\n"
      "module t;\n"
      "  logic clk;\n"
      "  qtc #(0, 0) a(clk);\n"
      "  qtc #(0, $) b(clk);\n"
      "endmodule\n");
  EXPECT_NE(out.find("a.quiet"), std::string::npos) << out;
  EXPECT_NE(out.find("b.bounded"), std::string::npos) << out;
  EXPECT_EQ(out.find("a.bounded"), std::string::npos) << out;
  EXPECT_EQ(out.find("b.quiet"), std::string::npos) << out;
  EXPECT_NE(out.find("a.yes"), std::string::npos) << out;
  EXPECT_NE(out.find("b.yes"), std::string::npos) << out;
}

TEST(RangeSystemFunctionSim, DISABLED_ALocalparamInitializerIsAnswered) {
  EXPECT_EQ(RunIsunbounded("package pk;\n"
                           "  parameter Q = $;\n"
                           "endpackage\n"
                           "module m #(parameter P = 3);\n"
                           "  localparam bit U = $isunbounded(P);\n"
                           "  localparam bit V = $isunbounded(pk::Q);\n"
                           "  initial #(U ? 1 : 2) $display(\"%b %b\", U, V);\n"
                           "endmodule\n"
                           "module t;\n"
                           "  m #(.P($)) u();\n"
                           "  m v();\n"
                           "endmodule\n"),
            "1 1\n0 1\n");
}

TEST(RangeSystemFunctionSim,
     DISABLED_AModuleParameterOverriddenToDollarIsUnbounded) {
  EXPECT_EQ(RunIsunbounded("module m #(parameter P = 1);\n"
                           "  initial #($isunbounded(P) ? 1 : 2)\n"
                           "    $display(\"%b\", $isunbounded(P));\n"
                           "endmodule\n"
                           "module t;\n"
                           "  m #(.P($)) u();\n"
                           "  m u2();\n"
                           "endmodule\n"),
            "1\n0\n");
}

TEST(RangeSystemFunctionSim,
     InstanceOverrideNamingADollarParameterIsUnbounded) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module s #(parameter int N = 4);\n"
                       "  bit run_ub;\n"
                       "  initial run_ub = $isunbounded(N);\n"
                       "endmodule\n"
                       "module b;\n"
                       "  parameter int N = 4;\n"
                       "  bit run_ub;\n"
                       "  initial run_ub = $isunbounded(N);\n"
                       "endmodule\n"
                       "module mid #(parameter M = 4);\n"
                       "  s #(.N(M)) leaf();\n"
                       "endmodule\n"
                       "module t;\n"
                       "  parameter int P = $;\n"
                       "  parameter int Q = 5;\n"
                       "  s #(.N(P)) a();\n"
                       "  s #(P) c();\n"
                       "  s #(.N(Q)) d();\n"
                       "  b #(.N(P)) e();\n"
                       "  mid #(.M(P)) h();\n"
                       "  mid #(.M(Q)) k();\n"
                       "  if (1) begin : g\n"
                       "    localparam int G = $;\n"
                       "    s #(.N(P)) a();\n"
                       "    s #(P) c();\n"
                       "    s #(.N(G)) l();\n"
                       "  end\n"
                       "  initial #1 $display(\"%0d%0d %0d%0d %0d%0d%0d %0d%0d "
                       "%0d%0d %0d%0d%0d %0d%0d %0d %0d%0d\",\n"
                       "    $isunbounded(a.N), a.run_ub,\n"
                       "    $isunbounded(c.N), c.run_ub,\n"
                       "    $isunbounded(d.N), d.run_ub, d.N,\n"
                       "    $isunbounded(e.N), e.run_ub,\n"
                       "    $isunbounded(h.M), h.leaf.run_ub,\n"
                       "    $isunbounded(k.M), k.leaf.run_ub, k.leaf.N,\n"
                       "    $isunbounded(g.a.N), g.a.run_ub, g.c.run_ub,\n"
                       "    $isunbounded(g.l.N), g.l.run_ub);\n"
                       "endmodule\n",
                       f),
            "11 11 005 11 11 005 11 1 11\n");
}

}  // namespace
