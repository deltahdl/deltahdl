// §20.8.1: Integer math functions

#include "builders_ast.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "fixture_simulator.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(ConstEval, Clog2) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(256)", f)), 8);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(1)", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(5)", f)), 3);
}

// § system_tf_call — $clog2 as expression elaborates
TEST(ElabA82, SystemTfCallAsExprElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial x = $clog2(256);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § primary — system call elaborates
TEST(ElabA84, PrimarySystemCallElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int W = $clog2(16);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// ============================================================================
// §20.8.1 — $clog2
// ============================================================================
TEST(Section20, Clog2Zero) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$clog2", {MakeInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Section20, Clog2Two) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$clog2", {MakeInt(f.arena, 2)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Section20, Clog2Three) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$clog2", {MakeInt(f.arena, 3)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 2u);
}

// ---------------------------------------------------------------------------
// 14. Blocking assignment with system function ($clog2) on RHS.
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignSysClog2) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = $clog2(256);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // $clog2(256) = 8
  EXPECT_EQ(var->value.ToUint64(), 8u);
}

}  // namespace
