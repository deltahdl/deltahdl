#include <gtest/gtest.h>

#include <cstdint>
#include <string>
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
  EXPECT_EQ(m00->value.ToUint64(), 1u);
  EXPECT_EQ(m02->value.ToUint64(), 3u);
  EXPECT_EQ(m10->value.ToUint64(), 4u);
  EXPECT_EQ(m12->value.ToUint64(), 6u);
}

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
  EXPECT_EQ(d5->value.ToUint64(), 1u);
  EXPECT_EQ(d1->value.ToUint64(), 5u);
}

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
  EXPECT_EQ(seen->value.ToUint64(), 3u);
  EXPECT_EQ(outer->value.ToUint64(), 99u);
}

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
  EXPECT_EQ(vo->value.ToUint64(), 2u);
  EXPECT_EQ(vi->value.ToUint64(), 3u);
}

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
      "    static C c = new;\n"
      "    c.fill();\n"
      "    result = 0;\n"
      "    foreach (c.m[k]) result = result + c.m[k];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 60u);
}

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
      "    static C c = new;\n"
      "    result = c.total();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2960u);
}

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
      "    static C c = new;\n"
      "    result = c.weighted();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 321u);
}

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
                      "    static C c = new;\n"
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
                      "    static C c = new;\n"
                      "    c.fill(12);\n"
                      "    result = c.sum();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            60u);
}

TEST(LoopStatementSim,
     ForeachOverAFixedSizeArrayPropertyStepsItsDeclaredIndices) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int b[2:5];\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    result = 0;\n"
                      "    foreach (c.b[i]) result = result * 10 + i;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            2345u);
}

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
                      "    static C c = new;\n"
                      "    c.alloc(5);\n"
                      "    result = c.d[3];\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            9u);
}

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
                "    static C c = new;\n"
                "    c.alloc(5);\n"
                "    c.grow(8);\n"
                "    result = c.d[3] * 10 + c.d.size();\n"
                "  end\n"
                "endmodule\n",
                "result"),
      98u);
}

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
                      "    static N a = new;\n"
                      "    static N b = new;\n"
                      "    static G g = new;\n"
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

TEST(LoopStatementSim, ForeachKeyOfAClassKeyedModuleArrayIsAHandle) {
  EXPECT_EQ(RunAndGet("class N;\n"
                      "  int v;\n"
                      "  function int get(); return v; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  bit m[N];\n"
                      "  initial begin\n"
                      "    static N a = new;\n"
                      "    static N b = new;\n"
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

TEST(ForeachEnumKeySim, LoopVariableOverAnEnumKeyedArrayIsOfTheEnum) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef enum {RED, GREEN, BLUE} color_t;\n"
                       "  int m [color_t];\n"
                       "  string acc;\n"
                       "  initial begin\n"
                       "    m[BLUE] = 7; m[RED] = 5;\n"
                       "    acc = \"\";\n"
                       "    foreach (m[c]) acc = {acc, c.name(), \"=\", "
                       "$sformatf(\"%0d \", m[c])};\n"
                       "    $display(\"%s\", acc);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "RED=5 BLUE=7 \n");
}

TEST(ForeachEnumKeySim, LoopVariableInASubroutineIsOfTheEnum) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef enum {RED, GREEN, BLUE} color_t;\n"
                       "class H;\n"
                       "  int m [color_t];\n"
                       "  function string walk();\n"
                       "    string acc = \"\";\n"
                       "    foreach (m[c]) acc = {acc, c.name(), \" \"};\n"
                       "    return acc;\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  function string loc();\n"
                       "    int n [color_t];\n"
                       "    static string acc = \"\";\n"
                       "    n[GREEN] = 1; n[RED] = 2;\n"
                       "    foreach (n[k]) acc = {acc, k.name(), \" \"};\n"
                       "    return acc;\n"
                       "  endfunction\n"
                       "  H h;\n"
                       "  initial begin\n"
                       "    h = new; h.m[BLUE] = 1; h.m[GREEN] = 2;\n"
                       "    $display(\"[%s] [%s]\", h.walk(), loc());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "[GREEN BLUE ] [RED GREEN ]\n");
}

TEST(LoopStatementSim, ForeachOverArrayPropertiesInMethods) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class C;\n"
      "    int arr[4];\n"
      "    int d[];\n"
      "    function new(int n); d = new[n]; foreach (d[i]) d[i] = i * 10;\n"
      "    endfunction\n"
      "    function void fill(); foreach (arr[i]) arr[i] = (i + 1) * 10;\n"
      "    endfunction\n"
      "    function int total(); int s = 0; foreach (arr[i]) s += arr[i];\n"
      "      foreach (d[i]) s += d[i] * 100; return s; endfunction\n"
      "  endclass\n"
      "  C h;\n"
      "  initial begin\n"
      "    h = new(3); h.fill();\n"
      "    $display(\"%0d %0d %0d %0d\", h.arr[0], h.arr[3], h.d[2],\n"
      "             h.total());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "10 40 20 3100\n");
}

TEST(LoopStatementSim, ForeachOverASignedAssociativeIndex) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef bit signed [4:1] SNibble;\n"
      "  int b[byte];\n"
      "  int s[SNibble];\n"
      "  int u[bit [3:0]];\n"
      "  function automatic void f(); foreach (b[i]) $write(\" f%0d\", i);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    b[5] = 1; b[-3] = 2;\n"
      "    s[-3] = 2; s[0] = 3;\n"
      "    u[-1] = 1;\n"
      "    foreach (b[i]) $write(\" %0d\", i);\n"
      "    f();\n"
      "    foreach (s[k]) $write(\" %0d\", k);\n"
      "    foreach (u[k]) $write(\" u%0d\", k);\n"
      "    $display(\"\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, " -3 5 f-3 f5 -3 0 u15\n");
}

TEST(LoopStatementSim, ForeachSecondVariableStepsThroughElementArrays) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int r[$][2];\n"
      "  int aq[int][$];\n"
      "  int rd[$][2:0];\n"
      "  int n, m;\n"
      "  initial begin\n"
      "    r.push_back('{5, 6}); r.push_back('{7, 8});\n"
      "    aq[1] = '{3, 4};\n"
      "    rd.push_back('{1, 2, 3});\n"
      "    foreach (r[k, j]) n += r[k][j];\n"
      "    foreach (aq[k, j]) m += aq[k][j];\n"
      "    foreach (rd[k, j]) $write(\"%0d=%0d \", j, rd[k][j]);\n"
      "    $display(\"%0d %0d\", n, m);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2=1 1=2 0=3 26 7\n");
}

}  // namespace
