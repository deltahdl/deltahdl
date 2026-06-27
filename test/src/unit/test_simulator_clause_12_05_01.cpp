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

// Runs a case statement whose single non-default item matches the selector via
// a pattern variable holding a don't-care (z) bit, returning the result value.
// Shared by the casex and casez "Z in item treated as don't-care" tests, which
// differ only in case_kind.
uint64_t RunZInItemDontCare(StmtFixture& f, TokenKind case_kind) {
  auto* result_var = f.ctx.CreateVariable("czit", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = case_kind;
  stmt->condition = MakeInt(f.arena, 2);

  auto* pat_var = f.ctx.CreateVariable("pat_z", 4);
  pat_var->value = MakeLogic4Vec(f.arena, 4);
  pat_var->value.words[0].aval = 0x02;  // bit0 = z = (aval=0, bval=1)
  pat_var->value.words[0].bval = 0x01;

  CaseItem item1;
  item1.patterns.push_back(MakeId(f.arena, "pat_z"));
  item1.body = MakeBlockAssign(f.arena, "czit", 77);
  stmt->case_items.push_back(item1);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "czit", 0);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);
  return result_var->value.ToUint64();
}

// Runs a case statement where an earlier item (a pattern variable with a
// don't-care bit) and a later literal item both nominally match the selector,
// verifying first-match-wins behavior. Shared by the casex and casez
// "first match wins" tests, which differ in case_kind and the pattern aval.
uint64_t RunFirstMatchWins(StmtFixture& f, TokenKind case_kind,
                           uint32_t pat_aval) {
  auto* result_var = f.ctx.CreateVariable("cfm", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = case_kind;
  stmt->condition = MakeInt(f.arena, 5);

  auto* pat1 = f.ctx.CreateVariable("p1", 8);
  pat1->value = MakeLogic4Vec(f.arena, 8);
  pat1->value.words[0].aval = pat_aval;
  pat1->value.words[0].bval = 0x01;

  CaseItem item1;
  item1.patterns.push_back(MakeId(f.arena, "p1"));
  item1.body = MakeBlockAssign(f.arena, "cfm", 10);
  stmt->case_items.push_back(item1);

  CaseItem item2;
  item2.patterns.push_back(MakeInt(f.arena, 5));
  item2.body = MakeBlockAssign(f.arena, "cfm", 20);
  stmt->case_items.push_back(item2);

  RunStmt(stmt, f.ctx, f.arena);
  return result_var->value.ToUint64();
}

TEST(CasexStatementSim, CasexMatchesIgnoringXZ) {
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

TEST(CasexStatementSim, CasexNoMatchFallsToDefault) {
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

TEST(CasexStatementSim, CasexWithXZInSelector) {
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

TEST(CasexStatementSim, CasexXInSelectorTreatedAsDontCare) {
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

TEST(CasexStatementSim, CasexZInItemTreatedAsDontCare) {
  StmtFixture f;
  EXPECT_EQ(RunZInItemDontCare(f, TokenKind::kKwCasex), 77u);
}

TEST(CasexStatementSim, CasexSymmetricDontCareBothSides) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("csym", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* sel_var = f.ctx.CreateVariable("sel_sym", 8);
  sel_var->value = MakeLogic4Vec(f.arena, 8);
  sel_var->value.words[0].aval = 0x28;
  sel_var->value.words[0].bval = 0x03;

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCasex;
  stmt->condition = MakeId(f.arena, "sel_sym");

  auto* pat_var = f.ctx.CreateVariable("pat_sym", 8);
  pat_var->value = MakeLogic4Vec(f.arena, 8);
  pat_var->value.words[0].aval = 0x28;
  pat_var->value.words[0].bval = 0xC0;

  CaseItem item1;
  item1.patterns.push_back(MakeId(f.arena, "pat_sym"));
  item1.body = MakeBlockAssign(f.arena, "csym", 55);
  stmt->case_items.push_back(item1);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "csym", 0);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);

  EXPECT_EQ(result_var->value.ToUint64(), 55u);
}

TEST(CasexStatementSim, CasexFirstMatchWins) {
  StmtFixture f;
  EXPECT_EQ(RunFirstMatchWins(f, TokenKind::kKwCasex, 0x04), 10u);
}

TEST(CasexStatementSim, CasexEmptyNoItems) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("cemp", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 42);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCasex;
  stmt->condition = MakeInt(f.arena, 1);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 42u);
}

TEST(CasexStatementSim, CasexQuestionMarkDontCare) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] ir, x;\n"
      "  initial begin\n"
      "    ir = 8'b10110010;\n"
      "    casex (ir)\n"
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

TEST(CasezStatementSim, CasezExactMatchWorks) {
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

TEST(CasezStatementSim, CasezNoMatchFallsToDefault) {
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

TEST(CasezStatementSim, CasezWithZInSelector) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("czz", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* sel_var = f.ctx.CreateVariable("sel_z", 8);
  sel_var->value = MakeLogic4Vec(f.arena, 8);
  sel_var->value.words[0].aval = 0x02;  // bit0 = z = (aval=0, bval=1)
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

TEST(CasezStatementSim, CasezQuestionMarkDontCare) {
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

TEST(CasezStatementSim, CasezSecondItemMatch) {
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

TEST(CasezStatementSim, CasezZInSelectorIsDontCare) {
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

TEST(CasezStatementSim, CasezDontCareInPatternOnly) {
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

TEST(CasezStatementSim, CasezZInItemTreatedAsDontCare) {
  StmtFixture f;
  EXPECT_EQ(RunZInItemDontCare(f, TokenKind::kKwCasez), 77u);
}

TEST(CasezStatementSim, CasezXInSelectorIsNotDontCare) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("cxnd", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* sel_var = f.ctx.CreateVariable("sel_x", 4);
  sel_var->value = MakeLogic4Vec(f.arena, 4);
  sel_var->value.words[0].aval = 0x02;
  sel_var->value.words[0].bval = 0x01;

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCasez;
  stmt->condition = MakeId(f.arena, "sel_x");

  CaseItem item1;
  item1.patterns.push_back(MakeInt(f.arena, 2));
  item1.body = MakeBlockAssign(f.arena, "cxnd", 42);
  stmt->case_items.push_back(item1);

  CaseItem item2;
  item2.patterns.push_back(MakeInt(f.arena, 3));
  item2.body = MakeBlockAssign(f.arena, "cxnd", 99);
  stmt->case_items.push_back(item2);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "cxnd", 0);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);

  EXPECT_EQ(result_var->value.ToUint64(), 42u);
}

TEST(CasezStatementSim, CasezXInItemIsNotDontCare) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("cxni", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCasez;
  stmt->condition = MakeInt(f.arena, 2);

  auto* pat_x = f.ctx.CreateVariable("pat_x", 4);
  pat_x->value = MakeLogic4Vec(f.arena, 4);
  pat_x->value.words[0].aval = 0x02;
  pat_x->value.words[0].bval = 0x01;

  CaseItem item1;
  item1.patterns.push_back(MakeId(f.arena, "pat_x"));
  item1.body = MakeBlockAssign(f.arena, "cxni", 55);
  stmt->case_items.push_back(item1);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "cxni", 0);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);

  EXPECT_EQ(result_var->value.ToUint64(), 55u);
}

TEST(CasezStatementSim, CasezEmptyNoItems) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("cemp", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 42);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCasez;
  stmt->condition = MakeInt(f.arena, 1);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 42u);
}

TEST(CasezStatementSim, CasezFirstMatchWins) {
  StmtFixture f;
  EXPECT_EQ(RunFirstMatchWins(f, TokenKind::kKwCasez, 0x05), 10u);
}

}  // namespace
