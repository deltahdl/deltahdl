#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "helpers_stmt_exec.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/lowerer.h"
#include "simulator/stmt_exec.h"
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
  auto* var = RunAndFindVar(
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
      f, "total");
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
  auto* var = RunAndFindVar(
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
      f, "cnt");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(LoopStatementSim, ForeachIteratorValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] arr [4];\n"
      "  logic [7:0] last_i;\n"
      "  initial begin\n"
      "    foreach (arr[i]) arr[i] = 8'd0;\n"
      "    last_i = 8'd0;\n"
      "    foreach (arr[i]) last_i = i[7:0];\n"
      "  end\n"
      "endmodule\n",
      f, "last_i");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(LoopStatementSim, ForeachContinue) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "sum");
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
  auto* var = RunAndFindVar(
      "module t;\n"
      "  string s;\n"
      "  logic [7:0] cnt;\n"
      "  initial begin\n"
      "    s = \"abc\";\n"
      "    cnt = 8'd0;\n"
      "    foreach (s[i]) cnt = cnt + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "cnt");
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
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] arr [4];\n"
      "  logic [7:0] total;\n"
      "  initial begin\n"
      "    total = 8'd0;\n"
      "    foreach (arr[i]) total = total + i;\n"
      "  end\n"
      "endmodule\n",
      f, "total");
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
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] pk;\n"
      "  logic [7:0] cnt;\n"
      "  initial begin\n"
      "    cnt = 8'd0;\n"
      "    foreach (pk[i]) cnt = cnt + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "cnt");
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
  auto* var = RunAndFindVar(
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
      f, "cnt");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// §12.7.3: a foreach over an associative array steps its loop variable
// through the indices the array holds, in the array's order (§7.8.4:
// numerical for an integral index). The loop ran over the variable under the
// array's name before -- elem_width iterations from 0 -- so the keys 3 and 10
// summed as 0 through 31 do.
TEST(LoopStatementSim, ForeachOverAnAssociativeArrayVisitsItsIndices) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[3] = 30;\n"
      "    result = 0;\n"
      "    foreach (aa[k]) result = result + k + aa[k];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 143u);
}

// §12.7.3 with §7.8.2: a string index orders its keys lexicographically and
// the loop variable is the key itself, so the entries are visited a, b, c
// whatever order they were written in.
TEST(LoopStatementSim, ForeachOverAStringKeyedAssociativeArrayVisitsItsKeys) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int sa[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    sa[\"c\"] = 3;\n"
      "    sa[\"a\"] = 1;\n"
      "    sa[\"b\"] = 2;\n"
      "    result = 0;\n"
      "    foreach (sa[k]) result = result * 10 + sa[k];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 123u);
}

// §12.7.3 over a class property (§8.5 restricts no property's type) reached
// through a handle: the loop visits the entries a method of the object wrote
// and reads each through the same handle.
TEST(LoopStatementSim, ForeachOverAnAssociativePropertySumsWhatAMethodWrote) {
  uint64_t v = RunAndGet(
      "class C;\n"
      "  int m[int];\n"
      "  function void fill();\n"
      "    m[1] = 10;\n"
      "    m[2] = 20;\n"
      "    m[3] = 30;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c = new;\n"
      "    c.fill();\n"
      "    result = 0;\n"
      "    foreach (c.m[k]) result = result + c.m[k];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 60u);
}

// §12.7.3 inside a method: a foreach over the object's own associative
// property, named bare, steps through the keys a method wrote, each loop
// variable value a key rather than a count; the function interpreter stepped
// a counter from 0 to a size no variable answered, so the sum stayed 0.
TEST(LoopStatementSim, ForeachOverAnAssociativePropertyInsideAMethod) {
  uint64_t v = RunAndGet(
      "class C;\n"
      "  int m[int];\n"
      "  function int total();\n"
      "    int sum = 0;\n"
      "    m[4] = 10;\n"
      "    m[9] = 20;\n"
      "    m[16] = 30;\n"
      "    foreach (m[k]) sum = sum + k * 100 + m[k];\n"
      "    return sum;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c = new;\n"
      "    result = c.total();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2960u);
}

// §12.7.3 with §7.8.2: a string-keyed property's foreach inside a method hands
// the loop variable each key as a string, in lexicographical order.
TEST(LoopStatementSim, ForeachOverAStringKeyedPropertyInsideAMethod) {
  uint64_t v = RunAndGet(
      "class C;\n"
      "  int m[string];\n"
      "  function int weighted();\n"
      "    int sum = 0;\n"
      "    int pos = 1;\n"
      "    m[\"b\"] = 2;\n"
      "    m[\"a\"] = 1;\n"
      "    m[\"c\"] = 3;\n"
      "    foreach (m[k]) begin\n"
      "      sum = sum + pos * m[k];\n"
      "      pos = pos * 10;\n"
      "    end\n"
      "    return sum;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c = new;\n"
      "    result = c.weighted();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 321u);
}

// §12.7.3 with §7.10 and §8.5: a foreach over a queue property steps once per
// element the queue holds, in a method by the property's bare name (§8.11)
// and at module level through the handle: 4 + 5 + 6 twice, and the last loop
// variable's value 2.
TEST(LoopStatementSim, ForeachOverAQueuePropertyInAMethodAndThroughAHandle) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int q[$];\n"
                      "  function int total();\n"
                      "    int s = 0;\n"
                      "    foreach (q[i]) s += q[i];\n"
                      "    return s;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  int last;\n"
                      "  initial begin\n"
                      "    C c = new;\n"
                      "    c.q.push_back(4);\n"
                      "    c.q.push_back(5);\n"
                      "    c.q.push_back(6);\n"
                      "    out = 0;\n"
                      "    foreach (c.q[i]) begin\n"
                      "      out = out + c.q[i];\n"
                      "      last = i;\n"
                      "    end\n"
                      "    out = (out + c.total()) * 10 + last;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            302u);
}

// §12.7.3 with §7.4 and §8.5: a foreach over a fixed-size unpacked array
// property named bare in a method (§8.11) steps once per declared index, so
// the sum of 12, 14, 16 and 18 a for loop wrote is 60. Before this the loop
// found no array of the name and ran its body no times, answering 0.
TEST(LoopStatementSim, ForeachOverAFixedSizeArrayPropertyInsideAMethod) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int a[4];\n"
                      "  function void fill(int base);\n"
                      "    for (int i = 0; i < 4; i++) a[i] = base + i * 2;\n"
                      "  endfunction\n"
                      "  function int sum();\n"
                      "    int s = 0;\n"
                      "    foreach (a[i]) s += a[i];\n"
                      "    return s;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c = new;\n"
                      "    c.fill(12);\n"
                      "    result = c.sum();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            60u);
}

// §12.7.3 with §7.4.2: the loop variable takes the dimension's own indices,
// so a property declared `[2:5]` iterated through the handle at module level
// hands the body 2, 3, 4 and 5 in turn, and nothing else: 2345.
TEST(LoopStatementSim,
     ForeachOverAFixedSizeArrayPropertyStepsItsDeclaredIndices) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int b[2:5];\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c = new;\n"
                      "    result = 0;\n"
                      "    foreach (c.b[i]) result = result * 10 + i;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            2345u);
}

// §12.7.3 with §7.5 and §8.5: a foreach over a dynamic array property sized 5
// by `new[n]` in the same method steps 0 to 4, so `d[i] = i * 3` leaves d[3]
// holding 9. Before this the loop ran no times and d[3] stayed 0.
TEST(LoopStatementSim, ForeachOverADynamicArrayPropertyWritesEachElement) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int d[];\n"
                      "  function void alloc(int n);\n"
                      "    d = new[n];\n"
                      "    foreach (d[i]) d[i] = i * 3;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c = new;\n"
                      "    c.alloc(5);\n"
                      "    result = c.d[3];\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            9u);
}

// §12.7.3 with §7.5.1: the elements a foreach wrote survive a `new[8](d)`
// that grows the property, so d[3] is still 9 beside the new size 8: 98.
TEST(LoopStatementSim, ForeachWrittenDynamicArrayPropertySurvivesAResize) {
  EXPECT_EQ(
      RunAndGet("class C;\n"
                "  int d[];\n"
                "  function void alloc(int n);\n"
                "    d = new[n];\n"
                "    foreach (d[i]) d[i] = i * 3;\n"
                "  endfunction\n"
                "  function void grow(int n); d = new[n](d); endfunction\n"
                "endclass\n"
                "module t;\n"
                "  int result;\n"
                "  initial begin\n"
                "    C c = new;\n"
                "    c.alloc(5);\n"
                "    c.grow(8);\n"
                "    result = c.d[3] * 10 + c.d.size();\n"
                "  end\n"
                "endmodule\n",
                "result"),
      98u);
}

// §12.7.3 with §8.5 and §13.3: the same loop inside a class task called
// through a handle, which the scheduler runs statement by statement, with a
// delay in the body so each element is visited in its own time step: 5 + 8 +
// 11 + 14 is 38, read after the task's four steps have passed.
TEST(LoopStatementSim, ForeachOverAFixedSizeArrayPropertyInsideAClassTask) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int a[4];\n"
                      "  int total;\n"
                      "  task run();\n"
                      "    for (int i = 0; i < 4; i++) a[i] = 5 + i * 3;\n"
                      "    total = 0;\n"
                      "    foreach (a[i]) begin\n"
                      "      #1 total = total + a[i];\n"
                      "    end\n"
                      "  endtask\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  C c;\n"
                      "  initial begin\n"
                      "    c = new;\n"
                      "    c.run();\n"
                      "    #1 result = c.total;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            38u);
}

// §12.7.3 with §7.8.3: the loop variable has the index type, so over an
// array keyed by a class it is a handle of that class, and a method called
// through it runs on the object the key designates -- uvm_phase's
// `foreach (m_successors[succ]) succ.m_find_successor(...)`. The keys are
// objects holding 3 and 40, summed through their get() inside a method: 43.
// Typed as the 32-bit counter it was, the variable named no class and each
// call answered 0.
TEST(LoopStatementSim, ForeachKeyOfAClassKeyedPropertyIsAHandle) {
  EXPECT_EQ(RunAndGet("class N;\n"
                      "  int v;\n"
                      "  function int get(); return v; endfunction\n"
                      "endclass\n"
                      "class G;\n"
                      "  bit succ[N];\n"
                      "  function int sum();\n"
                      "    int s = 0;\n"
                      "    foreach (succ[k]) s += k.get();\n"
                      "    return s;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    N a = new;\n"
                      "    N b = new;\n"
                      "    G g = new;\n"
                      "    a.v = 3;\n"
                      "    b.v = 40;\n"
                      "    g.succ[a] = 1;\n"
                      "    g.succ[b] = 1;\n"
                      "    result = g.sum();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            43u);
}

// §12.7.3 with §7.8.3: the same for a module's array iterated by a procedural
// foreach, which creates its loop variable apart from a subroutine body's.
TEST(LoopStatementSim, ForeachKeyOfAClassKeyedModuleArrayIsAHandle) {
  EXPECT_EQ(RunAndGet("class N;\n"
                      "  int v;\n"
                      "  function int get(); return v; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  bit m[N];\n"
                      "  initial begin\n"
                      "    N a = new;\n"
                      "    N b = new;\n"
                      "    a.v = 3;\n"
                      "    b.v = 40;\n"
                      "    m[a] = 1;\n"
                      "    m[b] = 1;\n"
                      "    result = 0;\n"
                      "    foreach (m[k]) result += k.get();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            43u);
}

}  // namespace
