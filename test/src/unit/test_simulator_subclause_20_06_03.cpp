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

}  // namespace
