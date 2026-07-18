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
  auto* design = ElaborateSrc(
      "module sub #(parameter int P = $);\n"
      "endmodule\n"
      "module t;\n"
      "  sub s();\n"
      "  int result;\n"
      "  initial result = $isunbounded(s.P);\n"
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

// §20.6.3: the "otherwise returns false" branch holds for the hierarchical
// operand form too — a submodule parameter given an ordinary bounded value is
// not $, so a dotted query of it yields 1'b0.
TEST(RangeSystemFunctionSim, HierarchicalBoundedParameterReturnsFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module sub #(parameter int P = 13);\n"
      "endmodule\n"
      "module t;\n"
      "  sub s();\n"
      "  int result;\n"
      "  initial result = $isunbounded(s.P);\n"
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

}  // namespace
