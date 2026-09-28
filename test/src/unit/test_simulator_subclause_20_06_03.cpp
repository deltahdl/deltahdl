#include <gtest/gtest.h>

#include <string>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §20.6.3: $isunbounded returns true (1'b1) when its argument is an unbounded
// parameter (one declared with $). This is the LRM example: parameter int i =
// $; then $isunbounded(i) returns true.
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

// §20.6.3: for any argument that is not $, $isunbounded returns false (1'b0).
// A parameter given an ordinary bounded value is therefore not unbounded.
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

// §20.6.3: the result is resolved per argument name, so when one parameter is
// unbounded and another is bounded the two queries disagree within the same
// design.
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

// §20.6.3: the true result is a single-bit value (1'b1), not a wider integer.
// Evaluating the call directly against a registered unbounded parameter shows
// the 1-bit width the LRM specifies.
TEST(RangeSystemFunctionSim, TrueResultIsOneBitWide) {
  SimFixture f;
  f.ctx.RegisterUnboundedParam("u");
  auto* expr = MakeSysCall(f.arena, "$isunbounded", {MakeId(f.arena, "u")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// §20.6.3: an argument that is not a parameter name at all (here a plain
// integer literal) is still not $, so the "otherwise" branch applies and the
// call returns the 1-bit false value (1'b0).
TEST(RangeSystemFunctionSim, NonParameterArgumentReturnsFalse) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$isunbounded", {MakeInt(f.arena, 8)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// §20.6.3 BNF (Syntax 20-8): the operand may be a hierarchical_parameter_
// identifier, not only a simple ps_parameter_identifier. A dotted reference to
// an unbounded parameter inside an instantiated submodule shall evaluate to the
// same true (1'b1) result. Built from real source and driven through the full
// pipeline so the instance-qualified name is produced by elaboration/lowering,
// not hand-registered.
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

// §20.6.3: the "otherwise returns false" branch holds for the hierarchical
// operand form too — a submodule parameter given an ordinary bounded value is
// not $, so a dotted query of it yields 1'b0.
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

// §20.6.3 answers 1'b1 where the parameter's value is `$`, and §6.20.7 lets
// `$` be a class value parameter's value as it is a module's. The default
// specialization holds `$` and `C #(4)` holds 4, so the two method calls
// disagree; beside them a module parameter of each kind gives the same pair.
// This fails on a class that rejects `$` as its default, and on one that
// answers every class parameter as bounded.
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

// §6.20.7 makes it legal to assign a `$` parameter to another parameter, and
// the one assigned holds `$` in its turn: `M = N` does in the default
// specialization, and so does the body localparam `L = $`. Under `C #(4)` N
// holds 4, so M, whose default names N, holds 4 and is bounded; under
// `C #(.M(3))` M is overridden and bounded while N keeps `$`. Each digit of
// ub() is one parameter, N M L. This fails on a mark taken from a default
// alone, which left M unbounded under `C #(4)`.
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

// §6.20.7: an override naming a parameter that holds `$` hands the class's
// parameter `$`, so $isunbounded on it answers 1; one naming a bounded
// parameter answers 0. This fails on an override that reads the name's value
// alone, which `$` does not have.
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
