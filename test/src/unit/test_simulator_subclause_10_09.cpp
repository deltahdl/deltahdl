#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_string_var.h"
#include "parser/ast_expr.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(AssignmentPatternSimulation, PositionalTwoElements) {
  SimFixture f;
  auto* a = f.ctx.CreateVariable("a", 8);
  auto* b = f.ctx.CreateVariable("b", 8);
  a->value = MakeLogic4VecVal(f.arena, 8, 5);
  b->value = MakeLogic4VecVal(f.arena, 8, 10);
  auto* expr = ParseExprFrom("'{a, b}", f);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kAssignmentPattern);
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0x050Au);
}

TEST(AssignmentPatternSimulation, PositionalThreeElements) {
  SimFixture f;
  auto* a = f.ctx.CreateVariable("a", 4);
  auto* b = f.ctx.CreateVariable("b", 4);
  auto* c = f.ctx.CreateVariable("c", 4);
  a->value = MakeLogic4VecVal(f.arena, 4, 1);
  b->value = MakeLogic4VecVal(f.arena, 4, 2);
  c->value = MakeLogic4VecVal(f.arena, 4, 3);
  auto* expr = ParseExprFrom("'{a, b, c}", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.width, 12u);
  EXPECT_EQ(result.ToUint64(), 0x123u);
}

TEST(AssignmentPatternSimulation, SingleElement) {
  SimFixture f;
  auto* a = f.ctx.CreateVariable("a", 32);
  a->value = MakeLogic4VecVal(f.arena, 32, 42);
  auto* expr = ParseExprFrom("'{a}", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(AssignmentPatternSimulation, EmptyPatternRejectedBeforeEvaluation) {
  SimFixture f;
  ParseExprFrom("'{}", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern needs at least one expression",
                            1, "10.9"));
}

TEST(AssignmentPatternSimulation, SizedLiterals) {
  SimFixture f;
  auto* expr = ParseExprFrom("'{32'd5, 32'd10}", f);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kAssignmentPattern);
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.width, 64u);
  uint64_t expected = (uint64_t{5} << 32) | 10;
  EXPECT_EQ(result.ToUint64(), expected);
}

TEST(AssignmentPatternSimulation, ReplicationPatternEvaluates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0][7:0] x;\n"
      "  initial begin\n"
      "    x = '{4{8'hAB}};\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABABABABu);
}

TEST(AssignmentPatternSimulation, IntegerAtomTypePatternEvaluates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = int'{42};\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(AssignmentPatternSimulation, LhsPositionalUnpackingTwoElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    '{a, b} = 16'hABCD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 0xABu);
  EXPECT_EQ(vb->value.ToUint64(), 0xCDu);
}

TEST(AssignmentPatternSimulation, TypedLhsPatternUnpacks) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    pair_t'{a, b} = 16'hABCD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors) << "source reported an elaboration error";
  LowerAndRun(design, f);
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 0xABu);
  EXPECT_EQ(vb->value.ToUint64(), 0xCDu);
}

TEST(AssignmentPatternSimulation, ByteTypePrefixEvaluates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte b;\n"
      "  initial begin\n"
      "    b = byte'{8'd42};\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(AssignmentPatternSimulation, TypeReferencePrefixYieldsValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [1:0][7:0] x;\n"
      "  initial begin\n"
      "    x = type(x)'{8'd1, 8'd2};\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x0102u);
}

TEST(AssignmentPatternSimulation, StructTypePrefixYieldsValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{8'h12, 8'h34};\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x1234u);
}

TEST(AssignmentPatternSimulation, TypedPatternExpressionAsOperandYieldsValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = int'{40} + 2;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(AssignmentPatternSimulation, PositionalPatternYieldsCorrectValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [1:0][7:0] x;\n"
      "  initial begin\n"
      "    x = '{8'hAB, 8'hCD};\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCDu);
}

TEST(AssignmentPatternSimulation, SingleElementPositionalPattern) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [0:0][7:0] x;\n"
      "  initial begin\n"
      "    x = '{8'd42};\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(AssignmentPatternSimulation, FourElementPositionalPattern) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0][7:0] x;\n"
      "  initial begin\n"
      "    x = '{8'd1, 8'd2, 8'd3, 8'd4};\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x01020304u);
}

TEST(AssignmentPatternSimulation, PatternInConditionalBranch) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [1:0][7:0] x;\n"
      "  initial begin\n"
      "    if (1) x = '{8'd5, 8'd6};\n"
      "    else x = '{8'd0, 8'd0};\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1286u);
}

TEST(AssignmentPatternSimulation, PatternInCaseItemBody) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] sel;\n"
      "  logic [1:0][7:0] x;\n"
      "  initial begin\n"
      "    sel = 8'd1;\n"
      "    case(sel)\n"
      "      8'd0: x = '{8'd0, 8'd0};\n"
      "      8'd1: x = '{8'd10, 8'd20};\n"
      "      default: x = '{8'd0, 8'd0};\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 2580u);
}

TEST(AssignmentPatternSimulation, PatternInForLoop) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [1:0][7:0] x;\n"
      "  initial begin\n"
      "    x = 16'd0;\n"
      "    for (int i = 0; i < 3; i = i + 1) begin\n"
      "      x = '{8'd7, 8'd8};\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1800u);
}

TEST(AssignmentPatternSimulation, PositionalStringLiteralsSeedAStringQueue) {
  RunAndExpectStringQueue(
      "module t;\n"
      "  string SQ[$];\n"
      "  initial SQ = '{\"element 0\", \"element 1\"};\n"
      "endmodule\n",
      "SQ", {"element 0", "element 1"});
}

TEST(AssignmentPatternSimulation, SizeMismatchIsReportedAtTheConcatenation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a [0:2];\n"
      "  int b [0:2];\n"
      "  initial begin\n"
      "    a = {1, 2, 3};\n"
      "    b = {1, 2};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation size mismatch", 6,
                            "10.10"));
}

TEST(AssignmentPatternSim, PackedArrayPatternFillsEachElement) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef logic [1:0][3:0] T;\n"
      "  logic [7:0] z; logic [1:0][3:0] x; logic [2:0][7:0] y;\n"
      "  shortint v; logic [1:0][1:0][3:0] w;\n"
      "  initial begin\n"
      "    z = T'{1,2}; x = '{3,4}; y = '{8'h1, 2, 3};\n"
      "    v = shortint'({T'{1,2}, T'{3,4}});\n"
      "    w = '{'{1,2}, '{3,4}};\n"
      "    $display(\"%h %h %h %h %h\", z, x, y, v, w);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "12 34 010203 1234 1234\n");
}

TEST(AssignmentPatternSim, PatternTargetDeconstructsAnUnpackedArray) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef byte U[3];\n"
      "  U A = '{1, 2, 3}; byte a, b, c; byte q[$] = '{7, 8, 9};\n"
      "  initial begin\n"
      "    U'{a, b, c} = A; $display(\"%0d %0d %0d\", a, b, c);\n"
      "    U'{c, a, b} = '{a+1, b+1, c+1};\n"
      "    $display(\"%0d %0d %0d\", a, b, c);\n"
      "    '{a, b, c} = q; $display(\"%0d %0d %0d\", a, b, c);\n"
      "    '{A[2], A[0], A[1]} = A;\n"
      "    $display(\"%0d %0d %0d\", A[0], A[1], A[2]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 2 3\n3 4 2\n7 8 9\n2 3 1\n");
}

TEST(AssignmentPatternSim, TypedStructurePatternIsPackedWhereverWritten) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct packed {byte a; byte b;} st;\n"
      "  st s; st sq[$];\n"
      "  initial begin\n"
      "    s = st'{3,4};\n"
      "    $display(\"%h %h\", s, st'{3,4});\n"
      "    sq = {st'{1,2}, st'{3,4}};\n"
      "    $display(\"%0d %h %h\", sq.size(), sq[0], sq[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0304 0304\n2 0102 0304\n");
}

}  // namespace
