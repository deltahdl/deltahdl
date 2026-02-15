#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult10c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult10c Parse(const std::string& src) {
  ParseResult10c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static Stmt* FirstInitialStmt(ParseResult10c& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

static Stmt* NthInitialStmt(ParseResult10c& r, size_t n) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      if (n < item->body->stmts.size()) return item->body->stmts[n];
    }
  }
  return nullptr;
}

// =============================================================================
// LRM section 10.4.1 -- Blocking procedural assignments
// =============================================================================

// --- 1. Simple blocking assignment: a = b ---
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

// --- 2. Blocking assignment with intra-assignment delay: a = #10 b ---
TEST(ParserSection10, Sec10_4_1_IntraAssignDelay) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    a = #10 b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->delay, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->text, "a");
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->text, "b");
}

// --- 3. Blocking assignment with intra-assignment event control ---
TEST(ParserSection10, Sec10_4_1_IntraAssignEvent) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, clk;\n"
      "  initial begin\n"
      "    a = @(posedge clk) b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  ASSERT_NE(stmt->lhs, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

// --- 4. Blocking assignment with addition expression ---
TEST(ParserSection10, Sec10_4_1_ExprAddition) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = b + c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
}

// --- 5. Blocking assignment with bitwise AND expression ---
TEST(ParserSection10, Sec10_4_1_ExprBitwiseAnd) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = b & c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
}

// --- 6. Blocking assignment to bit-select: a[3] = 1 ---
TEST(ParserSection10, Sec10_4_1_BitSelect) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] a;\n"
      "  initial begin\n"
      "    a[3] = 1;\n"
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

// --- 7. Blocking assignment to part-select: a[7:4] = 4'hF ---
TEST(ParserSection10, Sec10_4_1_PartSelect) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] a;\n"
      "  initial begin\n"
      "    a[7:4] = 4'hF;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->lhs->index_end, nullptr);
}

// --- 8. Blocking assignment to concatenation: {a, b} = {c, d} ---
TEST(ParserSection10, Sec10_4_1_Concatenation) {
  auto r = Parse(
      "module m;\n"
      "  reg [3:0] a, b, c, d;\n"
      "  initial begin\n"
      "    {a, b} = {c, d};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->lhs->elements.size(), 2u);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->rhs->elements.size(), 2u);
}

// --- 9. Blocking assignment with ternary RHS ---
TEST(ParserSection10, Sec10_4_1_TernaryRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c, sel;\n"
      "  initial begin\n"
      "    a = sel ? b : c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kTernary);
}

// --- 10. Blocking assignment in begin-end block ---
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

// --- 11. Blocking assignment in if-else branches ---
TEST(ParserSection10, Sec10_4_1_InIfElseBranches) {
  auto r = Parse(
      "module m;\n"
      "  reg a, sel;\n"
      "  initial begin\n"
      "    if (sel)\n"
      "      a = 1;\n"
      "    else\n"
      "      a = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kBlockingAssign);
}

// --- 12. Blocking assignment in case items ---
TEST(ParserSection10, Sec10_4_1_InCaseItems) {
  auto r = Parse(
      "module m;\n"
      "  reg [1:0] sel;\n"
      "  reg [7:0] out;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      2'b00: out = 8'h00;\n"
      "      2'b01: out = 8'h11;\n"
      "      2'b10: out = 8'h22;\n"
      "      default: out = 8'hFF;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_GE(stmt->case_items.size(), 4u);
  EXPECT_EQ(stmt->case_items[0].body->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->case_items[1].body->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->case_items[2].body->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->case_items[3].body->kind, StmtKind::kBlockingAssign);
}

// --- 13. Blocking assignment in for loop body ---
TEST(ParserSection10, Sec10_4_1_InForLoopBody) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    for (int i = 0; i < 4; i++)\n"
      "      mem[i] = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  ASSERT_NE(stmt->for_body, nullptr);
  EXPECT_EQ(stmt->for_body->kind, StmtKind::kBlockingAssign);
}

// --- 14. Blocking assignment with function call RHS ---
TEST(ParserSection10, Sec10_4_1_FunctionCallRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] result;\n"
      "  initial begin\n"
      "    result = compute(a, b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
}

// --- 15. Blocking assignment with system call RHS: a = $random ---
TEST(ParserSection10, Sec10_4_1_SystemCallRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [31:0] val;\n"
      "  initial begin\n"
      "    val = $random;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
}

// --- 16. Multiple sequential blocking assignments ---
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
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  auto* s2 = NthInitialStmt(r, 2);
  auto* s3 = NthInitialStmt(r, 3);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  ASSERT_NE(s2, nullptr);
  ASSERT_NE(s3, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s1->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s2->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s3->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(s0->lhs->text, "a");
  EXPECT_EQ(s1->lhs->text, "b");
  EXPECT_EQ(s2->lhs->text, "c");
  EXPECT_EQ(s3->lhs->text, "a");
}

// --- 17. Blocking assignment to struct member: s.field = val ---
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

// --- 18. Blocking assignment to array element: arr[i] = val ---
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

// --- 19. Compound assignment operator += ---
TEST(ParserSection10, Sec10_4_1_CompoundPlusEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a += 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kPlusEq);
}

// --- 20. Compound assignment operator -= ---
TEST(ParserSection10, Sec10_4_1_CompoundMinusEq) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    count -= 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kMinusEq);
}

// --- 21. Compound assignment operators *=, /=, %= ---
TEST(ParserSection10, Sec10_4_1_CompoundMulDivMod) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    a *= 3;\n"
              "    b /= 4;\n"
              "    c %= 5;\n"
              "  end\n"
              "endmodule\n"));
}

// --- 22. Compound assignment operators &=, |=, ^= ---
TEST(ParserSection10, Sec10_4_1_CompoundBitwise) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a &= 8'hFF;\n"
      "    b |= 8'h01;\n"
      "    c ^= 8'hAA;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  auto* s2 = NthInitialStmt(r, 2);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  ASSERT_NE(s2, nullptr);
  EXPECT_EQ(s0->rhs->op, TokenKind::kAmpEq);
  EXPECT_EQ(s1->rhs->op, TokenKind::kPipeEq);
  EXPECT_EQ(s2->rhs->op, TokenKind::kCaretEq);
}

// --- 23. Compound assignment operators <<=, >>=, <<<=, >>>= ---
TEST(ParserSection10, Sec10_4_1_CompoundShifts) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a <<= 2;\n"
      "    b >>= 1;\n"
      "    c <<<= 3;\n"
      "    d >>>= 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  auto* s2 = NthInitialStmt(r, 2);
  auto* s3 = NthInitialStmt(r, 3);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  ASSERT_NE(s2, nullptr);
  ASSERT_NE(s3, nullptr);
  EXPECT_EQ(s0->rhs->op, TokenKind::kLtLtEq);
  EXPECT_EQ(s1->rhs->op, TokenKind::kGtGtEq);
  EXPECT_EQ(s2->rhs->op, TokenKind::kLtLtLtEq);
  EXPECT_EQ(s3->rhs->op, TokenKind::kGtGtGtEq);
}

// --- 24. Blocking assignment with replication: a = {4{b}} ---
TEST(ParserSection10, Sec10_4_1_ReplicationRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] a;\n"
      "  reg [1:0] b;\n"
      "  initial begin\n"
      "    a = {4{b}};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kReplicate);
}

// --- 25. Blocking assignment with cast: a = int'(b) ---
TEST(ParserSection10, Sec10_4_1_CastRhs) {
  auto r = Parse(
      "module m;\n"
      "  int a;\n"
      "  real b;\n"
      "  initial begin\n"
      "    a = int'(b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCast);
}

// --- 26. Blocking assignment with negedge intra-assignment event ---
TEST(ParserSection10, Sec10_4_1_IntraAssignNegedgeEvent) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, clk;\n"
      "  initial begin\n"
      "    a = @(negedge clk) b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kNegedge);
  ASSERT_NE(stmt->rhs, nullptr);
}

// --- 27. Blocking assignment to nested struct member: s.inner.field = val ---
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

// --- 28. Blocking assignment in nested if-else with expressions ---
TEST(ParserSection10, Sec10_4_1_NestedIfElseWithExpressions) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] out, a, b;\n"
      "  reg sel1, sel2;\n"
      "  initial begin\n"
      "    if (sel1)\n"
      "      if (sel2)\n"
      "        out = a + b;\n"
      "      else\n"
      "        out = a - b;\n"
      "    else\n"
      "      out = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->then_branch->then_branch->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->then_branch->then_branch->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->then_branch->else_branch->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->then_branch->else_branch->rhs->kind, ExprKind::kBinary);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kBlockingAssign);
}

// --- 29. Full blocking assignment pattern in always block ---
TEST(ParserSection10, Sec10_4_1_FullPatternAlwaysComb) {
  EXPECT_TRUE(
      ParseOk("module m(\n"
              "  input [7:0] a, b,\n"
              "  input sel,\n"
              "  output reg [7:0] result\n"
              ");\n"
              "  always @(*) begin\n"
              "    result = 0;\n"
              "    if (sel)\n"
              "      result = a + b;\n"
              "    else\n"
              "      result = a - b;\n"
              "  end\n"
              "endmodule\n"));
}

// --- 30. Blocking assignment with complex LHS and RHS combinations ---
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
