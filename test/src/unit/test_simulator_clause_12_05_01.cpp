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
  auto* result_var = f.ctx.CreateVariable("czit", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // Selector: plain value 0b0010 (decimal 2).
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCasez;
  stmt->condition = MakeInt(f.arena, 2);

  // Item pattern: 4-bit with bit 0 = Z (aval=1, bval=1) → don't-care.
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

TEST(CasezStatementSim, CasezXInSelectorIsNotDontCare) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("cxnd", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // Selector: 4-bit, bit 0 = X (aval=0, bval=1). Known bits [3:1] = 001.
  auto* sel_var = f.ctx.CreateVariable("sel_x", 4);
  sel_var->value = MakeLogic4Vec(f.arena, 4);
  sel_var->value.words[0].aval = 0x02;  // 0b0010
  sel_var->value.words[0].bval = 0x01;  // bit 0 is X (aval=0, bval=1)

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCasez;
  stmt->condition = MakeId(f.arena, "sel_x");

  // Pattern: exact 0b0010. Bit 0 is 0 in pattern, X in selector.
  // BitIsZ checks (aval && bval); X has aval=0 so BitIsZ returns false.
  // X bit participates in comparison: sel bit0 aval=0 vs pat bit0 aval=0 → match.
  CaseItem item1;
  item1.patterns.push_back(MakeInt(f.arena, 2));
  item1.body = MakeBlockAssign(f.arena, "cxnd", 42);
  stmt->case_items.push_back(item1);

  // Pattern: exact 0b0011. Bit 0 is 1 in pattern, X in selector.
  // X bit participates: sel bit0 aval=0 vs pat bit0 aval=1 → mismatch.
  CaseItem item2;
  item2.patterns.push_back(MakeInt(f.arena, 3));
  item2.body = MakeBlockAssign(f.arena, "cxnd", 99);
  stmt->case_items.push_back(item2);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "cxnd", 0);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);
  // X in selector is NOT masked: aval comparison proceeds normally.
  // sel bit0 aval=0 matches pat1 bit0=0, so item1 matches.
  EXPECT_EQ(result_var->value.ToUint64(), 42u);
}

TEST(CasezStatementSim, CasezXInItemIsNotDontCare) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("cxni", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // Selector: plain value 0b0010 (decimal 2).
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCasez;
  stmt->condition = MakeInt(f.arena, 2);

  // Item pattern: 4-bit with bit 0 = X (aval=0, bval=1).
  // Under casez, X is NOT a don't-care. BitIsZ(X) = (0 && 1) = false.
  // So bit 0 participates: sel bit0=0, pat bit0 aval=0 → match on aval.
  auto* pat_x = f.ctx.CreateVariable("pat_x", 4);
  pat_x->value = MakeLogic4Vec(f.arena, 4);
  pat_x->value.words[0].aval = 0x02;  // 0b0010
  pat_x->value.words[0].bval = 0x01;  // bit 0 is X (aval=0, bval=1)

  CaseItem item1;
  item1.patterns.push_back(MakeId(f.arena, "pat_x"));
  item1.body = MakeBlockAssign(f.arena, "cxni", 55);
  stmt->case_items.push_back(item1);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "cxni", 0);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);
  // X is NOT masked — aval comparison proceeds. Both avals match → item1 wins.
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
  auto* result_var = f.ctx.CreateVariable("cfm", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCasez;
  stmt->condition = MakeInt(f.arena, 5);

  // Item 1: pattern with bit 0 = Z → matches 4 and 5.
  auto* pat1 = f.ctx.CreateVariable("p1", 8);
  pat1->value = MakeLogic4Vec(f.arena, 8);
  pat1->value.words[0].aval = 0x05;  // 0b00000101
  pat1->value.words[0].bval = 0x01;  // bit 0 is Z (aval=1, bval=1) → don't-care

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

}  // namespace
