#include <cstdint>
#include <string_view>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_stmt_exec.h"
#include "parser/ast.h"
#include "simulator/awaiters.h"
#include "simulator/exec_task.h"
#include "simulator/process.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(StmtExec, CasexMatchesIgnoringXZ) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("cx", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCasex;

  stmt->condition = MakeInt(f.arena, 2);

  CaseItem item1;
  item1.patterns.push_back(MakeInt(f.arena, 2));
  item1.body = MakeBlockAssign(f.arena, "cx", 1);
  stmt->case_items.push_back(item1);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "cx", 99);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 1u);
}

TEST(StmtExec, CasexNoMatchFallsToDefault) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("cxd", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCasex;
  stmt->condition = MakeInt(f.arena, 5);

  CaseItem item1;
  item1.patterns.push_back(MakeInt(f.arena, 10));
  item1.body = MakeBlockAssign(f.arena, "cxd", 1);
  stmt->case_items.push_back(item1);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "cxd", 99);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 99u);
}

TEST(StmtExec, CasezExactMatchWorks) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("cz", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCasez;
  stmt->condition = MakeInt(f.arena, 3);

  CaseItem item1;
  item1.patterns.push_back(MakeInt(f.arena, 3));
  item1.body = MakeBlockAssign(f.arena, "cz", 42);
  stmt->case_items.push_back(item1);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "cz", 0);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 42u);
}

TEST(StmtExec, CasezNoMatchFallsToDefault) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("czd", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCasez;
  stmt->condition = MakeInt(f.arena, 7);

  CaseItem item1;
  item1.patterns.push_back(MakeInt(f.arena, 3));
  item1.body = MakeBlockAssign(f.arena, "czd", 1);
  stmt->case_items.push_back(item1);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "czd", 55);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 55u);
}

TEST(StmtExec, CasexWithXZInSelector) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("cxz", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* sel_var = f.ctx.CreateVariable("sel_xz", 8);
  sel_var->value = MakeLogic4Vec(f.arena, 8);
  sel_var->value.words[0].aval = 0x02;
  sel_var->value.words[0].bval = 0x01;

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCasex;
  stmt->condition = MakeId(f.arena, "sel_xz");

  CaseItem item1;
  item1.patterns.push_back(MakeInt(f.arena, 2));
  item1.body = MakeBlockAssign(f.arena, "cxz", 42);
  stmt->case_items.push_back(item1);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "cxz", 0);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 42u);
}

TEST(StmtExec, CasezWithZInSelector) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("czz", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* sel_var = f.ctx.CreateVariable("sel_z", 8);
  sel_var->value = MakeLogic4Vec(f.arena, 8);
  sel_var->value.words[0].aval = 0x03;
  sel_var->value.words[0].bval = 0x01;

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCasez;
  stmt->condition = MakeId(f.arena, "sel_z");

  CaseItem item1;
  item1.patterns.push_back(MakeInt(f.arena, 2));
  item1.body = MakeBlockAssign(f.arena, "czz", 55);
  stmt->case_items.push_back(item1);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "czz", 0);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 55u);
}

TEST(SimA60701, CasezQuestionMarkDontCare) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] ir, x;\n"
      "  initial begin\n"
      "    ir = 8'b10110010;\n"
      "    casez (ir)\n"
      "      8'b1???????: x = 8'd1;\n"
      "      8'b01??????: x = 8'd2;\n"
      "      8'b00010???: x = 8'd3;\n"
      "      default: x = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(SimA60701, CasezSecondItemMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] ir, x;\n"
      "  initial begin\n"
      "    ir = 8'b01110010;\n"
      "    casez (ir)\n"
      "      8'b1???????: x = 8'd1;\n"
      "      8'b01??????: x = 8'd2;\n"
      "      8'b00010???: x = 8'd3;\n"
      "      default: x = 8'd0;\n"
      "    endcase\n"
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
}

TEST(SimA60701, CasexXInSelectorTreatedAsDontCare) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] r, x;\n"
      "  initial begin\n"
      "    r = 8'b01100110;\n"
      "    casex (r ^ 8'b0x0x0x0x)\n"
      "      8'b001100xx: x = 8'd1;\n"
      "      8'b1100xx00: x = 8'd2;\n"
      "      default: x = 8'd99;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
}

TEST(SimA60701, CasezZInSelectorIsDontCare) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] sel;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    sel = 4'bz1z0;\n"
      "    casez (sel)\n"
      "      4'b0100: x = 8'd10;\n"
      "      4'b1100: x = 8'd20;\n"
      "      default: x = 8'd99;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(SimA60701, CasezDontCareInPatternOnly) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] sel;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    sel = 4'b1010;\n"
      "    casez (sel)\n"
      "      4'b1??0: x = 8'd10;\n"
      "      4'b1010: x = 8'd20;\n"
      "      default: x = 8'd99;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 10u);
}

}
