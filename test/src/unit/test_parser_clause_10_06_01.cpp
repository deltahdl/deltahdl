// §10.6.1: The assign and deassign procedural statements

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

// Return all statements from the first initial block's begin/end.
static std::vector<Stmt*> AllInitialStmts(ParseResult& r) {
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  if (!item || !item->body) return {};
  if (item->body->kind == StmtKind::kBlock) return item->body->stmts;
  return {item->body};
}

namespace {

// =============================================================================
// A.6.2 Production: procedural_continuous_assignment
// procedural_continuous_assignment ::=
//   assign variable_assignment
//   | deassign variable_lvalue
//   | force variable_assignment
//   | force net_assignment
//   | release variable_lvalue
//   | release net_lvalue
// =============================================================================
TEST(ParserA602, ProceduralAssign_Basic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin assign q = d; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  EXPECT_NE(stmt->lhs, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(ParserA602, ProceduralDeassign_Basic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin deassign q; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDeassign);
  EXPECT_NE(stmt->lhs, nullptr);
}

TEST(ParserA602, ProceduralAssign_WithBitSelect) {
  auto r = Parse(
      "module m;\n"
      "  initial begin assign q[0] = d; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

// --- 28. Assign in task body ---
TEST(ParserSection10, Sec10_6_1_AssignInTaskBody) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  reg q;\n"
              "  task set_q;\n"
              "    assign q = 1;\n"
              "  endtask\n"
              "  task clear_q;\n"
              "    deassign q;\n"
              "  endtask\n"
              "endmodule\n"));
}

}  // namespace
