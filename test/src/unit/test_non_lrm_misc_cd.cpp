// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

struct ParseResult10d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult10d Parse(const std::string& src) {
  ParseResult10d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult10d& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

static Stmt* NthInitialStmt(ParseResult10d& r, size_t n) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      if (n < item->body->stmts.size()) return item->body->stmts[n];
    }
  }
  return nullptr;
}

static ModuleItem* FirstAlwaysItem(ParseResult10d& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      return item;
    }
  }
  return nullptr;
}

static Stmt* FirstAlwaysStmt(ParseResult10d& r) {
  auto* item = FirstAlwaysItem(r);
  if (!item || !item->body) return nullptr;
  if (item->body->kind == StmtKind::kBlock) {
    return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
  }
  return item->body;
}

namespace {

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

// =============================================================================
// LRM section 10.4.2 -- Nonblocking procedural assignments
// =============================================================================
// --- 1. Simple nonblocking assignment: q <= d ---
TEST(ParserSection10, Sec10_4_2_SimpleNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  reg q, d;\n"
      "  initial begin\n"
      "    q <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(stmt->lhs->text, "q");
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(stmt->rhs->text, "d");
}

// --- 2. Nonblocking with intra-assignment delay: q <= #10 d ---
TEST(ParserSection10, Sec10_4_2_IntraAssignDelay) {
  auto r = Parse(
      "module m;\n"
      "  reg q, d;\n"
      "  initial begin\n"
      "    q <= #10 d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->delay, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->text, "d");
}

// --- 3. Nonblocking with intra-assignment event: q <= @(posedge clk) d ---
TEST(ParserSection10, Sec10_4_2_IntraAssignEventPosedge) {
  auto r = Parse(
      "module m;\n"
      "  reg q, d, clk;\n"
      "  initial begin\n"
      "    q <= @(posedge clk) d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->text, "d");
}

// --- 4. Nonblocking in always_ff: always_ff @(posedge clk) q <= d ---
TEST(ParserSection10, Sec10_4_2_AlwaysFFNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  always_ff @(posedge clk)\n"
      "    q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysFFBlock);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysFF);
  auto* stmt = FirstAlwaysStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
}

// --- 5. Nonblocking in always @(posedge clk) ---
TEST(ParserSection10, Sec10_4_2_AlwaysPosedgeNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk)\n"
      "    q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysBlock);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
  ASSERT_GE(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  auto* stmt = FirstAlwaysStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
}

// --- 6. Nonblocking with binary expression RHS: q <= a + b ---
TEST(ParserSection10, Sec10_4_2_ExpressionRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] q, a, b;\n"
      "  initial begin\n"
      "    q <= a + b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
}

// --- 7. Nonblocking to bit-select: q[3] <= 1 ---
TEST(ParserSection10, Sec10_4_2_BitSelectLhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] q;\n"
      "  initial begin\n"
      "    q[3] <= 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->rhs, nullptr);
}

// --- 8. Nonblocking to part-select: q[7:4] <= 4'hF ---
TEST(ParserSection10, Sec10_4_2_PartSelectLhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] q;\n"
      "  initial begin\n"
      "    q[7:4] <= 4'hF;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->rhs, nullptr);
}

}  // namespace
