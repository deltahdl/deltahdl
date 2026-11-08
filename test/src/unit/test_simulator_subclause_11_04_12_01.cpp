#include <gtest/gtest.h>

#include <string>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(ReplicationSim, ReplicationBasic) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = {2{4'hA}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAAu);
}

TEST(ReplicationSim, ReplicationFourCopies) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = {4{2'b10}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xAAu);
}

TEST(ReplicationSim, ReplicationMultipleInner) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] result;\n"
      "  initial result = {2{4'hA, 4'h5}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xA5A5u);
}

TEST(ReplicationSim, LocalparamMultiplierCopyCount) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  localparam N = 3;\n"
      "  logic [11:0] result;\n"
      "  initial result = {N{4'hA}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 12u);
  EXPECT_EQ(var->value.ToUint64(), 0xAAAu);
}

TEST(ReplicationSim, ParameterMultiplierCopyCount) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter N = 3;\n"
      "  logic [11:0] result;\n"
      "  initial result = {N{4'hA}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 12u);
  EXPECT_EQ(var->value.ToUint64(), 0xAAAu);
}

TEST(ReplicationEval, ReplicationSingleCopy) {
  SimFixture f;

  auto* rep = f.arena.Create<Expr>();
  rep->kind = ExprKind::kReplicate;
  rep->repeat_count = MakeInt(f.arena, 1);
  rep->elements.push_back(MakeInt(f.arena, 42));
  auto result = EvalExpr(rep, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(ReplicationEval, ReplicationXZPropagation) {
  SimFixture f;

  MakeVar4(f, "rv", 4, 0b1001, 0b0101);

  auto* rep = f.arena.Create<Expr>();
  rep->kind = ExprKind::kReplicate;
  rep->repeat_count = MakeInt(f.arena, 2);
  rep->elements.push_back(MakeId(f.arena, "rv"));

  auto result = EvalExpr(rep, f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);

  EXPECT_EQ(result.words[0].aval, 0x99u);
  EXPECT_EQ(result.words[0].bval, 0x55u);
}

TEST(ReplicationSim, ReplicationNestedInConcatValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic [27:0] result;\n"
      "  initial begin\n"
      "    a = 4'h1;\n"
      "    b = 4'h2;\n"
      "    result = {b, {3{a, b}}};\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x2121212u);
}

TEST(ReplicationEval, ReplicationWidthIsCountTimesInnerWidth) {
  SimFixture f;

  auto* var = f.ctx.CreateVariable("v", 4);
  var->value = MakeLogic4VecVal(f.arena, 4, 0xA);

  auto* rep = f.arena.Create<Expr>();
  rep->kind = ExprKind::kReplicate;
  rep->repeat_count = MakeInt(f.arena, 5);
  rep->elements.push_back(MakeId(f.arena, "v"));
  auto result = EvalExpr(rep, f.ctx, f.arena);

  EXPECT_EQ(result.width, 20u);
  EXPECT_EQ(result.ToUint64(), 0xAAAAAu);
}

TEST(ReplicationEval, ZeroReplicationWidth) {
  SimFixture f;

  auto* rep = f.arena.Create<Expr>();
  rep->kind = ExprKind::kReplicate;
  rep->repeat_count = MakeInt(f.arena, 0);
  rep->elements.push_back(MakeInt(f.arena, 42));
  auto result = EvalExpr(rep, f.ctx, f.arena);

  EXPECT_EQ(result.width, 0u);
}

TEST(ReplicationSim, ZeroReplicationIgnoredInConcat) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic [3:0] result;\n"
      "  initial begin\n"
      "    a = 4'hA;\n"
      "    b = 4'hF;\n"
      "    result = {a, {0{b}}};\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

TEST(ReplicationSim, ParameterZeroMultiplierIgnoredInConcat) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter P = 0;\n"
      "  logic [7:0] a, b;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 8'hA5;\n"
      "    b = 8'hFF;\n"
      "    result = {a, {P{b}}};\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

TEST(ReplicationSim, OperandsEvaluatedOnce) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] i;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    i = 8'd5;\n"
      "    result = {4{i++}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("i")->value.ToUint64(), 6u);
  EXPECT_EQ(f.ctx.FindVariable("result")->value.ToUint64(), 0x05050505u);
}

TEST(ReplicationSim, OperandsEvaluatedOnceWithZeroMultiplier) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] i;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    i = 8'd5;\n"
      "    a = 8'hA5;\n"
      "    result = {a, {0{i++}}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("i")->value.ToUint64(), 6u);
  EXPECT_EQ(f.ctx.FindVariable("result")->value.ToUint64(), 0xA5u);
}

TEST(ReplicationSim, WideOperandsAndLongStringsAreCopiedWhole) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic [99:0] w = '1;\n"
                       "  logic [199:0] y;\n"
                       "  string s = \"abcdefghij\", r;\n"
                       "  initial begin\n"
                       "    y = {2{w}};\n"
                       "    r = {2{s}};\n"
                       "    $display(\"%h %s\", y, r);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            std::string(50, 'f') + " abcdefghijabcdefghij\n");
}

}  // namespace
