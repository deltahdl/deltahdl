#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(ConstEval, TernarySelectsCorrectBranch) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("1 ? 42 : 99", f)), 42);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("0 ? 42 : 99", f)), 99);
}

TEST(ConstEval, ScopedTernary) {
  EvalFixture f;
  ScopeMap scope_big = {{"WIDTH", 16}};
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("WIDTH > 8 ? WIDTH : 8", f), scope_big),
            16);
  ScopeMap scope_small = {{"WIDTH", 4}};
  EXPECT_EQ(
      ConstEvalInt(ParseExprFrom("WIDTH > 8 ? WIDTH : 8", f), scope_small), 8);
}

TEST(ExpressionElaboration, TernaryInContAssignElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic sel;\n"
      "  wire [7:0] a, b, y;\n"
      "  assign y = sel ? a : b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombBasicSim, AlwaysCombTernaryTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] result;\n"
      "  initial sel = 1;\n"
      "  always_comb begin\n"
      "    result = sel ? 8'd42 : 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(AlwaysCombBasicSim, AlwaysCombTernaryFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] result;\n"
      "  initial sel = 0;\n"
      "  always_comb begin\n"
      "    result = sel ? 8'd42 : 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(AlwaysCombBasicSim, AlwaysCombChainedTernary) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] result;\n"
      "  initial sel = 2'd1;\n"
      "  always_comb begin\n"
      "    result = (sel == 2'd0) ? 8'd10 :\n"
      "             (sel == 2'd1) ? 8'd20 :\n"
      "             (sel == 2'd2) ? 8'd30 : 8'd40;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(AlwaysLatchBasicSim, TernarySelectsFirst) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b, q;\n"
      "  initial begin\n"
      "    sel = 1;\n"
      "    a = 8'hCA;\n"
      "    b = 8'hFE;\n"
      "  end\n"
      "  always_latch\n"
      "    q = sel ? a : b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 0xCAu);
}

TEST(AlwaysLatchBasicSim, TernarySelectsSecond) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b, q;\n"
      "  initial begin\n"
      "    sel = 0;\n"
      "    a = 8'hCA;\n"
      "    b = 8'hFE;\n"
      "  end\n"
      "  always_latch\n"
      "    q = sel ? a : b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 0xFEu);
}

TEST(BlockingAssignSim, BlockingAssignTernary) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int sel, result;\n"
      "  initial begin\n"
      "    sel = 1;\n"
      "    result = sel ? 42 : 99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(BlockingAssignSim, BlockingAssignTernaryFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int sel, result;\n"
      "  initial begin\n"
      "    sel = 0;\n"
      "    result = sel ? 42 : 99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

// --- Moved from test_parser_clause_11_04_11_b.cpp ---

TEST(ConstEvalReal, TernaryOnReals) {
  EvalFixture f;
  auto* e = ParseExprFrom("1 ? 2.5 : 3.5", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(val.value_or(0.0), 2.5);
}

TEST(ExpressionElaboration, TernaryWidthIsMaxOfBranches) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  logic [7:0] wide;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    narrow = 4'hF;\n"
      "    wide = 8'hAA;\n"
      "    result = 1 ? narrow : wide;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

TEST(ExpressionElaboration, TernaryWidthEqualBranches) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, result;\n"
      "  initial begin\n"
      "    a = 8'hAB;\n"
      "    b = 8'hCD;\n"
      "    result = 1 ? a : b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
}

TEST(ExpressionElaboration, TernarySignedBothBranchesSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b;\n"
      "  int result;\n"
      "  assign result = 1 ? a : b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, TernaryUnsignedMixedSignedness) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int signed_val;\n"
      "  logic [31:0] unsigned_val;\n"
      "  logic [31:0] result;\n"
      "  assign result = 1 ? signed_val : unsigned_val;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstEvalReal, TernaryFalseConditionSelectsSecondReal) {
  EvalFixture f;
  auto* e = ParseExprFrom("0 ? 2.5 : 3.5", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(val.value_or(0.0), 3.5);
}

TEST(ConstEval, NestedTernaryConstEval) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("1 ? (0 ? 10 : 20) : 30", f)), 20);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("0 ? 10 : (1 ? 20 : 30)", f)), 20);
}

TEST(ConstEval, ChainedTernaryConstEval) {
  EvalFixture f;
  ScopeMap scope = {{"SEL", 2}};
  EXPECT_EQ(ConstEvalInt(
                ParseExprFrom("SEL == 0 ? 10 : SEL == 1 ? 20 : 30", f), scope),
            30);
  scope["SEL"] = 1;
  EXPECT_EQ(ConstEvalInt(
                ParseExprFrom("SEL == 0 ? 10 : SEL == 1 ? 20 : 30", f), scope),
            20);
}

}  // namespace
