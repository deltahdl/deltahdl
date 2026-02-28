// Non-LRM tests

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

TEST(ParserA602, NonblockingAssignment_WithRepeatEvent) {
  // Nonblocking with repeat(N) @(event) intra-assignment timing
  auto r = Parse(
      "module m;\n"
      "  initial begin q <= repeat(2) @(posedge clk) d; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  EXPECT_FALSE(stmt->events.empty());
}

TEST(ParserA602, NonblockingAssignment_ConcatLhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin {q, r} <= {d, e}; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
}

TEST(ParserA602, NonblockingAssignment_BitSelectLhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin mem[0] <= 8'hFF; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

TEST(ParserA602, NonblockingAssignment_ParenthesizedIntraDelay) {
  auto r = Parse(
      "module m;\n"
      "  initial begin q <= #(5:10:15) d; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->delay, nullptr);
}

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

TEST(ParserA602, Force_Variable) {
  // force variable_assignment
  auto r = Parse(
      "module m;\n"
      "  initial begin force q = 1; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForce);
  EXPECT_NE(stmt->lhs, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(ParserA602, Force_Net) {
  // force net_assignment
  auto r = Parse(
      "module m;\n"
      "  initial begin force net_a = 0; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForce);
}

TEST(ParserA602, Release_Variable) {
  auto r = Parse(
      "module m;\n"
      "  initial begin release q; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRelease);
  EXPECT_NE(stmt->lhs, nullptr);
}

TEST(ParserA602, Release_Net) {
  auto r = Parse(
      "module m;\n"
      "  initial begin release net_a; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRelease);
}

TEST(ParserA602, ProceduralContinuous_AllForms) {
  // All four procedural continuous assignment forms in one block
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assign q = d;\n"
      "    deassign q;\n"
      "    force y = 0;\n"
      "    release y;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto stmts = AllInitialStmts(r);
  ASSERT_EQ(stmts.size(), 4u);
  EXPECT_EQ(stmts[0]->kind, StmtKind::kAssign);
  EXPECT_EQ(stmts[1]->kind, StmtKind::kDeassign);
  EXPECT_EQ(stmts[2]->kind, StmtKind::kForce);
  EXPECT_EQ(stmts[3]->kind, StmtKind::kRelease);
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

TEST(ParserA602, Force_WithConcat) {
  auto r = Parse(
      "module m;\n"
      "  initial begin force {a, b} = 2'b11; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForce);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
}

TEST(ParserA602, Release_WithConcat) {
  auto r = Parse(
      "module m;\n"
      "  initial begin release {a, b}; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRelease);
}

// =============================================================================
// A.6.2 Production: variable_assignment
// variable_assignment ::= variable_lvalue = expression
// =============================================================================
TEST(ParserA602, VariableAssignment_SimpleExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin x = a + b * c; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
}

TEST(ParserA602, VariableAssignment_TernaryRhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin x = sel ? a : b; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kTernary);
}

TEST(ParserA602, VariableAssignment_CallRhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin x = func(a, b); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
}

// =============================================================================
// Integration: Mixing blocking and nonblocking in the same block
// =============================================================================
TEST(ParserA602, MixedAssignments_BlockingAndNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b <= 2;\n"
      "    c += 3;\n"
      "    d <= #10 4;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto stmts = AllInitialStmts(r);
  ASSERT_EQ(stmts.size(), 4u);
  EXPECT_EQ(stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmts[1]->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(stmts[2]->kind, StmtKind::kBlockingAssign);  // compound
  EXPECT_EQ(stmts[3]->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmts[3]->delay, nullptr);
}

// =============================================================================
// Integration: Procedural blocks containing various assignment forms
// =============================================================================
TEST(ParserA602, Integration_AlwaysFFWithBlockingAndNonblocking) {
  // Typical always_ff pattern with reset
  auto r = Parse(
      "module m;\n"
      "  always_ff @(posedge clk or negedge rst_n) begin\n"
      "    if (!rst_n) begin\n"
      "      q <= 0;\n"
      "      r <= 0;\n"
      "    end else begin\n"
      "      q <= d;\n"
      "      r <= e;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysFF);
  EXPECT_EQ(item->sensitivity.size(), 2u);
}

TEST(ParserA602, Integration_InitialWithTimingAndAssign) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "    @(posedge done) $finish;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto stmts = AllInitialStmts(r);
  ASSERT_EQ(stmts.size(), 4u);
  EXPECT_EQ(stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmts[1]->kind, StmtKind::kDelay);
  EXPECT_EQ(stmts[2]->kind, StmtKind::kDelay);
  EXPECT_EQ(stmts[3]->kind, StmtKind::kEventControl);
}

}  // namespace
