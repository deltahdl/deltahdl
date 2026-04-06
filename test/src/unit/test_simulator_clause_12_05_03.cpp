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

// Z in item pattern (raw Z encoding, not ?) is treated as don't-care.
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

// X in selector is NOT a don't-care under casez (only Z is).
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

// X in item pattern is NOT a don't-care under casez (only Z is).
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

// Empty casez (no items) — no match, no crash.
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

// First-match-wins with Z-wildcard patterns.
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
