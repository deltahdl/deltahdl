
#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "helpers_stmt_exec.h"
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
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] val;\n"
      "  initial begin\n"
      "    val = 8'hAB;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("val");
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
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* arr1 = f.ctx.FindVariable("arr[1]");
  ASSERT_NE(arr1, nullptr);
  auto* arr3 = f.ctx.FindVariable("arr[3]");
  ASSERT_NE(arr3, nullptr);
  EXPECT_EQ(arr1->value.ToUint64(), 0u);
  EXPECT_EQ(arr3->value.ToUint64(), 99u);
}

// The intra-assignment delay of a blocking assignment (§10.4.1) is a §9.4.1
// delay control, so a negative delay must be reinterpreted as a
// two's-complement unsigned integer the width of a time variable, exactly as a
// standalone delay does. A 32-bit -1 delay therefore advances time by the full
// 64-bit all-ones value, not by the raw zero-extended 0xFFFFFFFF. This
// discriminates against taking the delay's raw bits.
TEST(BlockingAssignSim,
     NegativeIntraAssignmentDelayReinterpretedAsTimeVariable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    d = -1;\n"
      "    x = #d 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
  EXPECT_EQ(f.ctx.CurrentTime().ticks, ~uint64_t{0});
}

// An intra-assignment delay whose value has any unknown bits (§9.4.1) must be
// treated as a zero delay, even when the known bits are nonzero. Here the delay
// 4'b10xx has known high bits worth 8, but the unknown low bits force a zero
// delay, so the assignment completes at time 0. This discriminates against a
// raw-bits reading that would advance time by 8.
TEST(BlockingAssignSim, MultibitUnknownIntraAssignmentDelayTreatedAsZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd1;\n"
      "    x = #(4'b10xx) 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.CurrentTime().ticks, 0u);
}

// §10.4.1 permits a variable of any of the assignment-compatible LHS forms; a
// struct member select (§7.2) is one such form and reaches production through
// the kMemberAccess lvalue-resolution path (ResolveLhsVariable/BuildLhsName),
// distinct from the plain-identifier and select forms already exercised. Each
// member write lands at its own field offset within the packed struct, so
// writing both members from scratch and reading back the whole struct verifies
// the full pipeline resolves and composes member-LHS blocking assignments. The
// existing §7.2.1 coverage overwrites a single member of a pre-initialized
// struct; this drives two distinct member LHS targets and observes the result.
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

}  // namespace
