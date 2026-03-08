// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA602, BlockingAssignment_Simple) {
  auto r = Parse(
      "module m;\n"
      "  initial begin a = 42; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(ParserA602, BlockingAssignment_ConcatLhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin {a, b} = {c, d}; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
}

TEST(ParserA602, BlockingAssignment_BitSelectLhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin mem[3] = 8'hFF; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

TEST(ParserA602, BlockingAssignment_PartSelectLhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin data[7:0] = 8'hAB; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

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

TEST(ParserSection10, Sec10_4_1_SimpleBlocking) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(stmt->lhs->text, "a");
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(stmt->rhs->text, "b");
}

TEST(ParserSection4, Sec4_5_BlockingAssignInAlways) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  always @(b) a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(item->body->lhs, nullptr);
  EXPECT_NE(item->body->rhs, nullptr);
}

TEST(ParserSection10, Sec10_4_1_InBeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'h00;\n"
      "    y = 8'hFF;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s1->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s0->lhs->text, "x");
  EXPECT_EQ(s1->lhs->text, "y");
}

TEST(ParserSection10, Sec10_4_1_MultipleSequential) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    b = 1;\n"
      "    c = 0;\n"
      "    a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto [s0, s1, s2, s3] = Get4InitialStmts(r);
  EXPECT_EQ(s0->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s1->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s2->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s3->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s0->lhs->text, "a");
  EXPECT_EQ(s1->lhs->text, "b");
  EXPECT_EQ(s2->lhs->text, "c");
  EXPECT_EQ(s3->lhs->text, "a");
}

TEST(ParserSection10, Sec10_4_1_ArrayElementLhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] arr [0:3];\n"
      "  initial begin\n"
      "    arr[2] = 8'hAB;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(ParserA604, StmtItemBlockingAssignment) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection10, Sec10_4_1_NestedStructMemberLhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    s.inner.field = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}

TEST(ParserSection10, Sec10_4_1_ComplexLhsRhsCombinations) {
  auto r = Parse(
      "module m;\n"
      "  reg [15:0] data;\n"
      "  reg [7:0] arr [0:3];\n"
      "  initial begin\n"
      "    data[7:0] = arr[0] + arr[1];\n"
      "    data[15:8] = arr[2] & arr[3];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s1->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s0->lhs->kind, ExprKind::kSelect);
  EXPECT_EQ(s1->lhs->kind, ExprKind::kSelect);
  EXPECT_EQ(s0->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(s1->rhs->kind, ExprKind::kBinary);
}

TEST(ParserSection9b, BlockingAssignSimple) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    rega = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserA85, NonrangeVarLvalueMemberAccess) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } s_t;\n"
      "  s_t s;\n"
      "  initial s.a = 8'h12;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}

TEST(ParserSection10, Sec10_4_1_StructMemberLhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    s.field = 42;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}

TEST(ParserSection9b, BlockingAssignBitSelect) {
  auto r = Parse(
      "module m;\n"
      "  initial rega[3] = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

TEST(ParserSection9b, BlockingAssignPartSelect) {
  auto r = Parse(
      "module m;\n"
      "  initial rega[3:5] = 7;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection9b, BlockingAssignConcatLhs) {
  auto r = Parse(
      "module m;\n"
      "  initial {carry, acc} = rega + regb;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
}

// §10.4.1: Blocking assignment in task body.
TEST(ParserSection10, Sec10_4_1_InTaskBody) {
  auto r = Parse(
      "module m;\n"
      "  task t();\n"
      "    int x;\n"
      "    x = 42;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* task = FindItemByKind(r, ModuleItemKind::kTaskDecl);
  ASSERT_NE(task, nullptr);
  ASSERT_NE(task->body, nullptr);
  ASSERT_GE(task->body->stmts.size(), 1u);
  auto* assign = task->body->stmts.back();
  EXPECT_EQ(assign->kind, StmtKind::kBlockingAssign);
}

// §10.4.1: Blocking assignment in function body.
TEST(ParserSection10, Sec10_4_1_InFunctionBody) {
  auto r = Parse(
      "module m;\n"
      "  function int compute(int a, int b);\n"
      "    int tmp;\n"
      "    tmp = a + b;\n"
      "    return tmp;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  ASSERT_NE(func->body, nullptr);
  auto* assign = FindStmtByKind(func->body->stmts, StmtKind::kBlockingAssign);
  ASSERT_NE(assign, nullptr);
  EXPECT_EQ(assign->lhs->text, "tmp");
}

// §10.4.1: Blocking with intra-assignment event control.
TEST(ParserSection10, Sec10_4_1_IntraAssignEventControl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = @(posedge clk) b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_FALSE(stmt->events.empty());
  ASSERT_NE(stmt->rhs, nullptr);
}

// §10.4.1: Blocking does not prevent execution in parallel block (§9.3.2).
TEST(ParserSection10, Sec10_4_1_InForkJoinBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "  join\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->stmts.size(), 2u);
  EXPECT_EQ(stmt->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->stmts[1]->kind, StmtKind::kBlockingAssign);
}

}  // namespace
