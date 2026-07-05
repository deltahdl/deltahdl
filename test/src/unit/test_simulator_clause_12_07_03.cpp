#include <cstdint>
#include <string_view>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_stmt_exec.h"
#include "parser/ast.h"
#include "simulator/awaiters.h"
#include "simulator/exec_task.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(StmtExec, ForeachEmptyArrayNoOp) {
  StmtFixture f;

  auto* arr = f.ctx.CreateVariable("empty", 0);
  (void)arr;
  auto* sum = f.ctx.CreateVariable("count", 32);
  sum->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* body = MakeBlockAssign(f.arena, "count", 1);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kForeach;
  stmt->expr = MakeId(f.arena, "empty");
  stmt->foreach_vars.push_back("i");
  stmt->body = body;

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(sum->value.ToUint64(), 0u);
}

TEST(StmtExec, ForeachNoVarsStillIterates) {
  StmtFixture f;
  auto* arr = f.ctx.CreateVariable("arr2", 3);
  arr->value = MakeLogic4VecVal(f.arena, 3, 0);

  auto* cnt = f.ctx.CreateVariable("cnt", 32);
  cnt->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* add = f.arena.Create<Expr>();
  add->kind = ExprKind::kBinary;
  add->op = TokenKind::kPlus;
  add->lhs = MakeId(f.arena, "cnt");
  add->rhs = MakeInt(f.arena, 1);

  auto* body = f.arena.Create<Stmt>();
  body->kind = StmtKind::kBlockingAssign;
  body->lhs = MakeId(f.arena, "cnt");
  body->rhs = add;

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kForeach;
  stmt->expr = MakeId(f.arena, "arr2");

  stmt->body = body;

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(cnt->value.ToUint64(), 3u);
}

TEST(LoopStatementSim, ForeachBasic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [4];\n"
      "  logic [7:0] total;\n"
      "  initial begin\n"
      "    arr[0] = 8'd1;\n"
      "    arr[1] = 8'd2;\n"
      "    arr[2] = 8'd3;\n"
      "    arr[3] = 8'd4;\n"
      "    total = 8'd0;\n"
      "    foreach (arr[i]) total = total + arr[i];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("total");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(LoopStatementSim, ForeachBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [3];\n"
      "  logic [7:0] sum, cnt;\n"
      "  initial begin\n"
      "    arr[0] = 8'd10;\n"
      "    arr[1] = 8'd20;\n"
      "    arr[2] = 8'd30;\n"
      "    sum = 8'd0;\n"
      "    cnt = 8'd0;\n"
      "    foreach (arr[i]) begin\n"
      "      sum = sum + arr[i];\n"
      "      cnt = cnt + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* vs = f.ctx.FindVariable("sum");
  auto* vc = f.ctx.FindVariable("cnt");
  ASSERT_NE(vs, nullptr);
  ASSERT_NE(vc, nullptr);
  EXPECT_EQ(vs->value.ToUint64(), 60u);
  EXPECT_EQ(vc->value.ToUint64(), 3u);
}

TEST(LoopStatementSim, ForeachBreak) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [5];\n"
      "  logic [7:0] cnt;\n"
      "  initial begin\n"
      "    foreach (arr[i]) arr[i] = 8'd0;\n"
      "    cnt = 8'd0;\n"
      "    foreach (arr[i]) begin\n"
      "      cnt = cnt + 8'd1;\n"
      "      if (cnt == 8'd3) break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("cnt");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(LoopStatementSim, ForeachIteratorValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [4];\n"
      "  logic [7:0] last_i;\n"
      "  initial begin\n"
      "    foreach (arr[i]) arr[i] = 8'd0;\n"
      "    last_i = 8'd0;\n"
      "    foreach (arr[i]) last_i = i[7:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("last_i");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(LoopStatementSim, ForeachContinue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [4];\n"
      "  logic [7:0] sum;\n"
      "  initial begin\n"
      "    arr[0] = 8'd1;\n"
      "    arr[1] = 8'd2;\n"
      "    arr[2] = 8'd3;\n"
      "    arr[3] = 8'd4;\n"
      "    sum = 8'd0;\n"
      "    foreach (arr[i]) begin\n"
      "      if (i[7:0] == 8'd1) continue;\n"
      "      sum = sum + arr[i];\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("sum");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 8u);
}

TEST(LoopStatementSim, ForeachWriteArrayElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [3];\n"
      "  initial begin\n"
      "    foreach (arr[i]) arr[i] = i[7:0] + 8'd10;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a0 = f.ctx.FindVariable("arr[0]");
  auto* a1 = f.ctx.FindVariable("arr[1]");
  auto* a2 = f.ctx.FindVariable("arr[2]");
  ASSERT_NE(a0, nullptr);
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(a2, nullptr);
  EXPECT_EQ(a0->value.ToUint64(), 10u);
  EXPECT_EQ(a1->value.ToUint64(), 11u);
  EXPECT_EQ(a2->value.ToUint64(), 12u);
}

// §12.7.3 — the loop variable takes the array's declared index values, so a
// non-zero base is honored: the writes land in data[1], data[2], data[3].
TEST(LoopStatementSim, ForeachUsesDeclaredIndexBase) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data [1:3];\n"
      "  initial begin\n"
      "    foreach (data[i]) data[i] = i[7:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* d1 = f.ctx.FindVariable("data[1]");
  auto* d2 = f.ctx.FindVariable("data[2]");
  auto* d3 = f.ctx.FindVariable("data[3]");
  ASSERT_NE(d1, nullptr);
  ASSERT_NE(d2, nullptr);
  ASSERT_NE(d3, nullptr);
  EXPECT_EQ(d1->value.ToUint64(), 1u);
  EXPECT_EQ(d2->value.ToUint64(), 2u);
  EXPECT_EQ(d3->value.ToUint64(), 3u);
}

// §12.7.3 — each loop variable corresponds to one array dimension, and the
// loop variables map to nested loops whose innermost (highest-cardinality)
// index changes most rapidly. Stamping an increasing order counter into each
// element records the visit sequence: for a 2x3 array the row index advances
// only after the column index has swept its full range, so element [1][0]
// (order 4) is visited immediately after [0][2] (order 3).
TEST(LoopStatementSim, ForeachMultiDimIteratesInnermostFastest) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] matrix [2][3];\n"
      "  logic [7:0] ord;\n"
      "  initial begin\n"
      "    ord = 8'd0;\n"
      "    foreach (matrix[i, j]) begin\n"
      "      ord = ord + 8'd1;\n"
      "      matrix[i][j] = ord;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* m00 = f.ctx.FindVariable("matrix[0][0]");
  auto* m02 = f.ctx.FindVariable("matrix[0][2]");
  auto* m10 = f.ctx.FindVariable("matrix[1][0]");
  auto* m12 = f.ctx.FindVariable("matrix[1][2]");
  ASSERT_NE(m00, nullptr);
  ASSERT_NE(m02, nullptr);
  ASSERT_NE(m10, nullptr);
  ASSERT_NE(m12, nullptr);
  EXPECT_EQ(m00->value.ToUint64(), 1u);  // first visited
  EXPECT_EQ(m02->value.ToUint64(), 3u);  // end of first row
  EXPECT_EQ(m10->value.ToUint64(), 4u);  // row advances only after column sweep
  EXPECT_EQ(m12->value.ToUint64(), 6u);  // last visited
}

// §12.7.3 — for a descending dimension the loop variable counts down from the
// high declared index to the low one (the LRM's B[5:1] iterates 5 down to 1).
// Stamping an increasing order counter into each visited element records the
// visit order: the first-visited element (index 5) gets 1 and the last-visited
// (index 1) gets 5, which is only possible if the loop walked the range
// downward.
TEST(LoopStatementSim, ForeachDescendingRangeIteratesHighToLow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data [5:1];\n"
      "  logic [7:0] ord;\n"
      "  initial begin\n"
      "    ord = 8'd0;\n"
      "    foreach (data[i]) begin\n"
      "      ord = ord + 8'd1;\n"
      "      data[i] = ord;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* d5 = f.ctx.FindVariable("data[5]");
  auto* d1 = f.ctx.FindVariable("data[1]");
  ASSERT_NE(d5, nullptr);
  ASSERT_NE(d1, nullptr);
  EXPECT_EQ(d5->value.ToUint64(), 1u);  // index 5 visited first
  EXPECT_EQ(d1->value.ToUint64(), 5u);  // index 1 visited last
}

// §12.7.3 — a string is iterated as a dynamic array of bytes: the loop runs
// once per character, so the counter reaches the character count (3), not the
// bit width (24).
TEST(LoopStatementSim, ForeachOverStringIteratesPerCharacter) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  string s;\n"
      "  logic [7:0] cnt;\n"
      "  initial begin\n"
      "    s = \"abc\";\n"
      "    cnt = 8'd0;\n"
      "    foreach (s[i]) cnt = cnt + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("cnt");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

// §12.7.3 — when a loop variable appears in an expression other than as an
// index into the designated array it takes an integer value (for a fixed-size
// array, int). Accumulating the loop variable itself sums the visited indices
// 0..3, giving 6, which is only meaningful if the variable is a usable integer
// operand outside the index position.
TEST(LoopStatementSim, ForeachLoopVarUsableAsIntInExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [4];\n"
      "  logic [7:0] total;\n"
      "  initial begin\n"
      "    total = 8'd0;\n"
      "    foreach (arr[i]) total = total + i;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("total");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

// §12.7.3 — the foreach-loop creates an implicit begin-end block whose loop
// variable has automatic lifetime local to that scope. Driven from real source:
// a module variable `i` is set to 99, then a foreach whose loop variable is
// also named `i` runs. Inside the loop the local loop variable shadows the
// outer one (last_seen records the final index 3), and after the loop the outer
// `i` still holds 99 because the loop variable was a distinct, scope-local
// declaration.
TEST(LoopStatementSim, ForeachImplicitScopeShadowsOuterVar) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [4];\n"
      "  logic [7:0] i;\n"
      "  logic [7:0] last_seen;\n"
      "  initial begin\n"
      "    i = 8'd99;\n"
      "    last_seen = 8'd0;\n"
      "    foreach (arr[i]) last_seen = i[7:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* seen = f.ctx.FindVariable("last_seen");
  auto* outer = f.ctx.FindVariable("i");
  ASSERT_NE(seen, nullptr);
  ASSERT_NE(outer, nullptr);
  EXPECT_EQ(seen->value.ToUint64(), 3u);    // local loop var swept the indices
  EXPECT_EQ(outer->value.ToUint64(), 99u);  // outer `i` untouched by the loop
}

// §12.7.3 — a foreach may iterate any packed OR unpacked array. A packed vector
// is a packed array, so foreach runs once per bit position: for a [7:0] packed
// value the loop body executes exactly eight times.
TEST(LoopStatementSim, ForeachOverPackedArrayIteratesPerBit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] pk;\n"
      "  logic [7:0] cnt;\n"
      "  initial begin\n"
      "    cnt = 8'd0;\n"
      "    foreach (pk[i]) cnt = cnt + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("cnt");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 8u);
}

// §12.7.3 — a loop variable may be omitted to indicate no iteration over that
// dimension. For a 2x3 array, naming only the first slot iterates just the
// leading dimension (2 steps), and naming only the second slot iterates just
// the trailing dimension (3 steps); the omitted dimension is not walked, so
// neither loop runs the full 2*3 element count.
TEST(LoopStatementSim, ForeachOmittedDimensionIsNotIterated) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] m [2][3];\n"
      "  logic [7:0] outer_cnt;\n"
      "  logic [7:0] inner_cnt;\n"
      "  initial begin\n"
      "    outer_cnt = 8'd0;\n"
      "    inner_cnt = 8'd0;\n"
      "    foreach (m[i, ]) outer_cnt = outer_cnt + 8'd1;\n"
      "    foreach (m[, j]) inner_cnt = inner_cnt + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* vo = f.ctx.FindVariable("outer_cnt");
  auto* vi = f.ctx.FindVariable("inner_cnt");
  ASSERT_NE(vo, nullptr);
  ASSERT_NE(vi, nullptr);
  EXPECT_EQ(vo->value.ToUint64(), 2u);  // only the leading dimension iterated
  EXPECT_EQ(vi->value.ToUint64(), 3u);  // only the trailing dimension iterated
}

// §12.7.3 — the implicit block a foreach creates is unnamed by default but can
// be named by prefixing the statement with a label; naming it makes the loop a
// disable target. Driven end-to-end from real label (§9.3.5) and disable
// (§9.6.2) source syntax: once the counter reaches 2 the body disables the
// loop's own label, which ends the loop like a break, so the counter stops at 2
// even though the array has five elements.
TEST(LoopStatementSim, ForeachNamedByLabelIsDisableTarget) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [5];\n"
      "  logic [7:0] cnt;\n"
      "  initial begin\n"
      "    cnt = 8'd0;\n"
      "    walk: foreach (arr[i]) begin\n"
      "      cnt = cnt + 8'd1;\n"
      "      if (cnt == 8'd2) disable walk;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("cnt");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

}  // namespace
