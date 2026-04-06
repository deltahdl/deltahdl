#include <string_view>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_stmt_exec.h"
#include "parser/ast.h"
#include "simulator/lowerer.h"
#include "simulator/stmt_exec.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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

// Z in item expression is treated as don't-care (symmetric with X).
TEST(CasexStatementSim, CasexZInItemTreatedAsDontCare) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("czit", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // Selector: plain value 0b0010 (decimal 2).
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCasex;
  stmt->condition = MakeInt(f.arena, 2);

  // Item pattern: 4-bit value with bit 0 = Z (aval=1, bval=1).
  // Pattern value = 0b??11 where bit 0 is Z — should be don't-care.
  auto* pat_var = f.ctx.CreateVariable("pat_z", 4);
  pat_var->value = MakeLogic4Vec(f.arena, 4);
  pat_var->value.words[0].aval = 0x03;  // bits: 0011
  pat_var->value.words[0].bval = 0x01;  // bit 0 is Z (aval=1, bval=1)

  CaseItem item1;
  item1.patterns.push_back(MakeId(f.arena, "pat_z"));
  item1.body = MakeBlockAssign(f.arena, "czit", 77);
  stmt->case_items.push_back(item1);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "czit", 0);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 77u);
}

// Both selector and item have X/Z bits — symmetric don't-care on both sides.
TEST(CasexStatementSim, CasexSymmetricDontCareBothSides) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("csym", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // Selector: 8-bit, bits [1:0] are X (bval=1).
  // Known bits [7:2] = 0b001010 → aval = 0x2A, bval = 0x03.
  auto* sel_var = f.ctx.CreateVariable("sel_sym", 8);
  sel_var->value = MakeLogic4Vec(f.arena, 8);
  sel_var->value.words[0].aval = 0x28;  // 0b00101000
  sel_var->value.words[0].bval = 0x03;  // bits [1:0] are X/Z

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCasex;
  stmt->condition = MakeId(f.arena, "sel_sym");

  // Item pattern: 8-bit, bits [7:6] are X (bval on those bits).
  // Known bits [5:0] = 0b101000 → aval = 0x28, bval = 0xC0.
  auto* pat_var = f.ctx.CreateVariable("pat_sym", 8);
  pat_var->value = MakeLogic4Vec(f.arena, 8);
  pat_var->value.words[0].aval = 0x28;  // 0b00101000
  pat_var->value.words[0].bval = 0xC0;  // bits [7:6] are X/Z

  CaseItem item1;
  item1.patterns.push_back(MakeId(f.arena, "pat_sym"));
  item1.body = MakeBlockAssign(f.arena, "csym", 55);
  stmt->case_items.push_back(item1);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "csym", 0);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);
  // Bits [1:0] from selector and [7:6] from pattern are don't-cares.
  // Remaining bits [5:2] match (both 0b1010). Should match.
  EXPECT_EQ(result_var->value.ToUint64(), 55u);
}

// First-match-wins: when multiple items match, casex selects the first.
TEST(CasexStatementSim, CasexFirstMatchWins) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("cfm", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCasex;
  stmt->condition = MakeInt(f.arena, 5);

  // Item 1 pattern has X in low bit → matches 4 and 5.
  auto* pat1 = f.ctx.CreateVariable("p1", 8);
  pat1->value = MakeLogic4Vec(f.arena, 8);
  pat1->value.words[0].aval = 0x04;  // 0b00000100
  pat1->value.words[0].bval = 0x01;  // bit 0 is X → don't-care

  // Item 2: exact match 5.
  CaseItem item1;
  item1.patterns.push_back(MakeId(f.arena, "p1"));
  item1.body = MakeBlockAssign(f.arena, "cfm", 10);
  stmt->case_items.push_back(item1);

  CaseItem item2;
  item2.patterns.push_back(MakeInt(f.arena, 5));
  item2.body = MakeBlockAssign(f.arena, "cfm", 20);
  stmt->case_items.push_back(item2);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 10u);
}

// Empty casex (no items) — no match, no crash.
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

}  // namespace
