#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/compiled_sim.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(BlockingAssignSim, BlockingOverwriteInOrder) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd100;\n"
      "    x = 8'd200;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 200u);
}

TEST(BlockingAssignCompiledSim, ExecuteBlockingAssign) {
  CompiledSimFixture f;
  auto* x_var = f.ctx.CreateVariable("x", 32);
  x_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* lhs = f.arena.Create<Expr>();
  lhs->kind = ExprKind::kIdentifier;
  lhs->text = "x";
  auto* rhs = f.arena.Create<Expr>();
  rhs->kind = ExprKind::kIntegerLiteral;
  rhs->int_val = 42;
  auto* assign = f.arena.Create<Stmt>();
  assign->kind = StmtKind::kBlockingAssign;
  assign->lhs = lhs;
  assign->rhs = rhs;

  auto* block = f.arena.Create<Stmt>();
  block->kind = StmtKind::kBlock;
  block->stmts.push_back(assign);

  auto compiled = ProcessCompiler::Compile(1, block);
  EXPECT_TRUE(compiled.IsValid());
  compiled.Execute(f.ctx);
  EXPECT_EQ(x_var->value.ToUint64(), 42u);
}

TEST(BlockingAssignSim, EightBitAssignPreservesWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] val;\n"
      "  initial begin\n"
      "    val = 8'hAB;\n"
      "  end\n"
      "endmodule\n",
      f, "val");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(BlockingAssignSim, ParallelBlockDoesNotPreventExecution) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, c;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin a = 1; b = a + 1; end\n"
      "      c = 99;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 2u}, {"c", 99u}});
}

TEST(BlockingAssignSim, SelfAssignmentPreservesValue) {
  auto result = RunAndGet(
      "module t;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = 42;\n"
      "    x = x;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 42u);
}

TEST(BlockingAssignSim, IntraAssignmentDelayEvaluatesLvalueAfterDelay) {
  SimFixture f;
  auto* arr1 = RunAndFindVar(
      "module t;\n"
      "  int arr [0:3];\n"
      "  int idx;\n"
      "  initial begin\n"
      "    arr[0] = 0; arr[1] = 0; arr[2] = 0; arr[3] = 0;\n"
      "    idx = 1;\n"
      "    arr[idx] = #5 99;\n"
      "  end\n"
      "  initial begin\n"
      "    #2 idx = 3;\n"
      "  end\n"
      "endmodule\n",
      f, "arr[1]");
  ASSERT_NE(arr1, nullptr);
  auto* arr3 = f.ctx.FindVariable("arr[3]");
  ASSERT_NE(arr3, nullptr);
  EXPECT_EQ(arr1->value.ToUint64(), 0u);
  EXPECT_EQ(arr3->value.ToUint64(), 99u);
}

TEST(BlockingAssignSim,
     NegativeIntraAssignmentDelayReinterpretedAsTimeVariable) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int d;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    d = -1;\n"
      "    x = #d 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
  EXPECT_EQ(f.ctx.CurrentTime().ticks, ~uint64_t{0});
}

TEST(BlockingAssignSim, MultibitUnknownIntraAssignmentDelayTreatedAsZero) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd1;\n"
      "    x = #(4'b10xx) 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.CurrentTime().ticks, 0u);
}

TEST(BlockingAssignSim, StructMemberLhsWritesComposeFullStruct) {
  auto result = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } w_t;\n"
      "  w_t s;\n"
      "  initial begin\n"
      "    s.hi = 8'hAB;\n"
      "    s.lo = 8'hCD;\n"
      "  end\n"
      "endmodule\n",
      "s");
  EXPECT_EQ(result, 0xABCDu);
}

TEST(BlockingAssignSim, TwoStateTargetCoercionLeavesSourceUnknownBitsIntact) {
  SimFixture f;
  auto* src_var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  bit [7:0] y;\n"
      "  initial begin\n"
      "    x = 8'b1010xxxx;\n"
      "    y = x;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(src_var, nullptr);
  auto* dst_var = f.ctx.FindVariable("y");
  ASSERT_NE(dst_var, nullptr);
  EXPECT_EQ(src_var->value.words[0].aval & 0xFFu, 0xAFu);
  EXPECT_EQ(src_var->value.words[0].bval & 0xFFu, 0x0Fu);
  EXPECT_EQ(dst_var->value.words[0].aval & 0xFFu, 0xA0u);
  EXPECT_EQ(dst_var->value.words[0].bval & 0xFFu, 0x00u);
}

TEST(BlockingAssignSim, PackedMemberDepositOnCopyLeavesSourceIntact) {
  SimFixture f;
  auto* whole = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } p_t;\n"
      "  p_t s;\n"
      "  p_t d;\n"
      "  initial begin\n"
      "    s.a = 8'hA5;\n"
      "    s.b = 8'h3C;\n"
      "    d = s;\n"
      "    d.b = 8'h00;\n"
      "  end\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(whole, nullptr);
  auto* copy = f.ctx.FindVariable("d");
  ASSERT_NE(copy, nullptr);
  EXPECT_EQ(whole->value.ToUint64(), 0xA53Cu);
  EXPECT_EQ(copy->value.ToUint64(), 0xA500u);
}

TEST(BlockingAssignSim, BitSelectWriteOnCopyLeavesSourceIntact) {
  SimFixture f;
  auto* original = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] p;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    p = 8'hA5;\n"
      "    q = p;\n"
      "    q[0] = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(original, nullptr);
  auto* selected = f.ctx.FindVariable("q");
  ASSERT_NE(selected, nullptr);
  EXPECT_EQ(original->value.ToUint64(), 0xA5u);
  EXPECT_EQ(selected->value.ToUint64(), 0xA4u);
}

TEST(BlockingAssignSim, DynamicArrayElementIndexEvaluatedOnce) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int d[];\n"
      "  int j;\n"
      "  initial begin\n"
      "    d = new[4];\n"
      "    d[j++] = 7;\n"
      "    $display(\"%0d %0d %0d\", j, d[0], d[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 7 0\n");
}

TEST(BlockingAssignSim, QueueElementIndexEvaluatedOnce) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int q[$];\n"
      "  int k;\n"
      "  initial begin\n"
      "    q = '{0, 0, 0, 0};\n"
      "    q[k++] = 7;\n"
      "    $display(\"%0d %0d %0d\", k, q[0], q[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 7 0\n");
}

TEST(BlockingAssignSim, AssocElementIndexEvaluatedOnce) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int aa[int];\n"
      "  int m;\n"
      "  initial begin\n"
      "    aa[m++] = 7;\n"
      "    $display(\"%0d %0d %0d %0d\", m, aa.num(), aa.exists(0), aa[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 1 7\n");
}

TEST(BlockingAssignSim, PackedBitSelectIndexEvaluatedOnce) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  int i;\n"
      "  initial begin\n"
      "    v = 8'h00;\n"
      "    v[i++] = 1'b1;\n"
      "    $display(\"%0d %b\", i, v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 00000001\n");
}

TEST(BlockingAssignSim, RefDynamicArrayFilledThroughPostIncrementIndex) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  function automatic void fill(ref int succ[]);\n"
      "    int idx;\n"
      "    succ = new[3];\n"
      "    foreach (succ[i]) succ[idx++] = i + 10;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    int d[];\n"
      "    fill(d);\n"
      "    $display(\"%0d %0d %0d %0d\", d.size(), d[0], d[1], d[2]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 10 11 12\n");
}

TEST(BlockingAssignSim, ConcatQueueElementIndexEvaluatedOnce) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  byte q[$];\n"
      "  byte b;\n"
      "  int k;\n"
      "  initial begin\n"
      "    q = '{0, 0};\n"
      "    {q[k++], b} = 16'h0703;\n"
      "    $display(\"%0d %0d %0d %0d\", k, q[0], q[1], b);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 7 0 3\n");
}

TEST(BlockingAssignSim, DelayedDynamicArrayElementIndexEvaluatedOnce) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int d[];\n"
      "  int j;\n"
      "  initial begin\n"
      "    d = new[4];\n"
      "    d[j++] = #1 7;\n"
      "    $display(\"%0d %0d %0d\", j, d[0], d[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 7 0\n");
}

TEST(BlockingAssignSim, SelectsOfAPropertyByItsBareNameInAMethod) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  class C;\n"
      "    logic [7:0] v;\n"
      "    function void f();\n"
      "      v = 0; this.v[3] = 1; v[0] = 1; v[6:5] = 2'b11;\n"
      "    endfunction\n"
      "    function void g(); v = 0; v[7 -: 4] = 4'hB; endfunction\n"
      "  endclass\n"
      "  C h;\n"
      "  initial begin\n"
      "    h = new; h.f(); $display(\"%0d\", h.v);\n"
      "    h.g(); $display(\"%0d\", h.v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "105\n176\n");
}

TEST(BlockingAssignSim, SelectOfAPropertyByItsBareNameInAnOutOfBlockBody) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  class C;\n"
      "    logic [7:0] v;\n"
      "    extern function void f();\n"
      "  endclass\n"
      "  function void C::f(); v = 0; v[0] = 1; v[2 +: 2] = 2'b11; "
      "endfunction\n"
      "  C h;\n"
      "  initial begin h = new; h.f(); $display(\"%0d\", h.v); end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "13\n");
}

TEST(BlockingAssignSim, ConcatenationTargetHandsAPropertyItsSlice) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  class C; logic [3:0] p; endclass\n"
      "  C h; logic [1:0] c; logic [3:0] a[2];\n"
      "  initial begin\n"
      "    h = new;\n"
      "    {c, h.p, a[1]} = 10'b10_0101_0011;\n"
      "    $display(\"%0d %0d %0d\", c, h.p, a[1]);\n"
      "    {c, {a[1], h.p}} = 10'b01_1100_0110;\n"
      "    $display(\"%0d %0d %0d\", c, h.p, a[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 5 3\n1 6 12\n");
}

TEST(BlockingAssignSim, TaggedElementTargetIndexEvaluatedOnce) {
  EXPECT_EQ(
      RunAndGet("module t;\n"
                "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
                "  VInt arr [4];\n"
                "  int i = 0;\n"
                "  int n;\n"
                "  function automatic VInt f();\n"
                "    return tagged Valid 4;\n"
                "  endfunction\n"
                "  initial begin\n"
                "    arr[i++] = tagged Valid 3;\n"
                "    arr[i++] = f();\n"
                "    n = i * 100 + arr[0].Valid * 10 + arr[1].Valid;\n"
                "  end\n"
                "endmodule\n",
                "n"),
      234u);
}

}  // namespace
