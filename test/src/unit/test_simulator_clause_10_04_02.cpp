
#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "helpers_stmt_exec.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(NonblockingAssignSim, BitSelect) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("nb", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "nb");
  sel->index = MakeInt(f.arena, 5);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kNonblockingAssign;
  stmt->lhs = sel;
  stmt->rhs = MakeInt(f.arena, 1);

  RunStmt(stmt, f.ctx, f.arena);

  f.scheduler.Run();
  EXPECT_EQ(var->value.ToUint64(), 0x20u);
}

TEST(NonblockingAssignSim, OrderingPreservedAcrossInitials) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'd99;\n"
      "    #8 a <= #8 8'd1;\n"
      "  end\n"
      "  initial begin\n"
      "    #12 a <= #4 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0u);
}

TEST(NonblockingAssignSim, BlockingEventsFromNbaProcessedAfter) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic q;\n"
      "  logic post_q;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    q = 0;\n"
      "    post_q = 0;\n"
      "    #1 clk = 1;\n"
      "  end\n"
      "  always_ff @(posedge clk) q <= 1;\n"
      "  always @(q) post_q = q;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("q")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("post_q")->value.ToUint64(), 1u);
}

TEST(NonblockingAssignSim, ProceduralFlowNotBlockedBySubsequent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] tgt;\n"
      "  logic [7:0] sample;\n"
      "  initial begin\n"
      "    tgt = 8'd5;\n"
      "    tgt <= 8'd99;\n"
      "    sample = tgt;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("sample")->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("tgt")->value.ToUint64(), 99u);
}

TEST(NonblockingAssignSim, LhsRequiringEvaluationBindsAtScheduleTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [0:1];\n"
      "  int idx;\n"
      "  initial begin\n"
      "    arr[0] = 8'd0;\n"
      "    arr[1] = 8'd0;\n"
      "    idx = 0;\n"
      "    arr[idx] <= 8'hAA;\n"
      "    idx = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0xAAu);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0u);
}

}  // namespace
