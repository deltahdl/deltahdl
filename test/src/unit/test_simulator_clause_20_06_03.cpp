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
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter int p = $;\n"
      "  int result;\n"
      "  initial result = $isunbounded(p);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §20.6.3: for any argument that is not $, $isunbounded returns false (1'b0).
// A parameter given an ordinary bounded value is therefore not unbounded.
TEST(RangeSystemFunctionSim, BoundedParameterReturnsFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter int p = 42;\n"
      "  int result;\n"
      "  initial result = $isunbounded(p);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
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

// §20.6.3: a name that is not a registered unbounded parameter is not $, so the
// call yields the 1-bit false value (1'b0).
TEST(RangeSystemFunctionSim, FalseResultIsOneBitWide) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$isunbounded", {MakeId(f.arena, "b")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 0u);
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

}  // namespace
