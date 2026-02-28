// §10.4.2: Nonblocking procedural assignments

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
// A.6.2 Production: nonblocking_assignment
// nonblocking_assignment ::= variable_lvalue <= [delay_or_event_control]
// expression
// =============================================================================
TEST(ParserA602, NonblockingAssignment_Simple) {
  auto r = Parse(
      "module m;\n"
      "  initial begin q <= d; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(ParserA602, NonblockingAssignment_WithIntraDelay) {
  // Nonblocking with intra-assignment delay
  auto r = Parse(
      "module m;\n"
      "  initial begin q <= #5 d; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(ParserA602, NonblockingAssignment_WithIntraEvent) {
  // Nonblocking with intra-assignment event control
  auto r = Parse(
      "module m;\n"
      "  initial begin q <= @(posedge clk) d; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
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

struct ParseResult11 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult11 Parse(const std::string& src) {
  ParseResult11 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult11& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

// --- 9. Nonblocking to concatenation LHS: {q1, q2} <= {d1, d2} ---
TEST(ParserSection10, Sec10_4_2_ConcatenationLhsRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg q1, q2, d1, d2;\n"
      "  initial begin\n"
      "    {q1, q2} <= {d1, d2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->lhs->elements.size(), 2u);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->rhs->elements.size(), 2u);
}

// --- 10. Nonblocking with ternary RHS: q <= sel ? a : b ---
TEST(ParserSection10, Sec10_4_2_TernaryRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg q, sel, a, b;\n"
      "  initial begin\n"
      "    q <= sel ? a : b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kTernary);
}

// --- 11. Nonblocking in begin-end block ---
TEST(ParserSection10, Sec10_4_2_InBeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  reg q, d;\n"
      "  initial begin\n"
      "    q <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_EQ(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kNonblockingAssign);
}

// --- 12. Nonblocking in if-else branches (mux pattern) ---
TEST(ParserSection10, Sec10_4_2_IfElseMuxPattern) {
  auto r = Parse(
      "module m;\n"
      "  reg q, sel, a, b;\n"
      "  initial begin\n"
      "    if (sel)\n"
      "      q <= a;\n"
      "    else\n"
      "      q <= b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kNonblockingAssign);
}

struct ParseResult9e {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9e Parse(const std::string& src) {
  ParseResult9e result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// LRM section 9.3.1 -- Blocks with nonblocking assignments.
// =============================================================================
TEST(ParserSection9, Sec9_3_1_BlockWithNonblockingAssigns) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a <= 1;\n"
      "    b <= 2;\n"
      "    c <= 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 3u);
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(body->stmts[i]->kind, StmtKind::kNonblockingAssign);
  }
}

// --- 14. Multiple nonblocking assignments in same block ---
TEST(ParserSection10, Sec10_4_2_MultipleInSameBlock) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c, d;\n"
      "  initial begin\n"
      "    a <= b;\n"
      "    c <= d;\n"
      "    b <= a;\n"
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
  EXPECT_EQ(s0->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(s1->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(s2->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(s0->lhs->text, "a");
  EXPECT_EQ(s1->lhs->text, "c");
  EXPECT_EQ(s2->lhs->text, "b");
}

// --- 15. Nonblocking with function call RHS ---
TEST(ParserSection10, Sec10_4_2_FunctionCallRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] q;\n"
      "  initial begin\n"
      "    q <= compute(a, b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
}

// --- 16. Nonblocking with system call RHS ---
TEST(ParserSection10, Sec10_4_2_SystemCallRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [31:0] q;\n"
      "  initial begin\n"
      "    q <= $random;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
}

struct ParseResult4d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult4d Parse(const std::string& src) {
  ParseResult4d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// §4.6: Non-blocking assignment ordering
// =============================================================================
TEST(ParserSection4, Sec4_6_NonblockingAssignOrdering) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a <= 1;\n"
      "    b <= 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kNonblockingAssign);
}

struct ParseResult4c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult4c Parse(const std::string& src) {
  ParseResult4c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// Returns the first always_* item from the first module.
static ModuleItem* FirstAlwaysItem(ParseResult4c& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock)
      return item;
  }
  return nullptr;
}

// ---------------------------------------------------------------------------
// 2. Non-blocking assignment in always block (NBA region)
// ---------------------------------------------------------------------------
TEST(ParserSection4, Sec4_5_NonblockingAssignInAlways) {
  auto r = Parse(
      "module m;\n"
      "  reg q, d, clk;\n"
      "  always @(posedge clk) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(item->body->lhs, nullptr);
  EXPECT_NE(item->body->rhs, nullptr);
}

// --- 17. Nonblocking to struct member: s.field <= val ---
TEST(ParserSection10, Sec10_4_2_StructMemberLhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    s.field <= 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
  ASSERT_NE(stmt->rhs, nullptr);
}

// --- 18. Nonblocking to array element: mem[idx] <= data ---
TEST(ParserSection10, Sec10_4_2_ArrayElementLhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] mem [0:255];\n"
      "  initial begin\n"
      "    mem[0] <= 8'hAB;\n"
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

// --- 19. Nonblocking with replication RHS ---
TEST(ParserSection10, Sec10_4_2_ReplicationRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] q;\n"
      "  initial begin\n"
      "    q <= {4{2'b10}};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kReplicate);
}

// --- 22. Nonblocking mixed with blocking in same module (different blocks) ---
TEST(ParserSection10, Sec10_4_2_MixedBlockingNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  reg q, d, a, b;\n"
      "  always @(posedge clk)\n"
      "    q <= d;\n"
      "  always @(*)\n"
      "    a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  int always_count = 0;
  bool found_nonblocking = false;
  bool found_blocking = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) {
      always_count++;
      if (item->body && item->body->kind == StmtKind::kNonblockingAssign) {
        found_nonblocking = true;
      }
      if (item->body && item->body->kind == StmtKind::kBlockingAssign) {
        found_blocking = true;
      }
    }
  }
  EXPECT_EQ(always_count, 2);
  EXPECT_TRUE(found_nonblocking);
  EXPECT_TRUE(found_blocking);
}

struct ParseResult4b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ModuleItem* FindItemByKind(ParseResult4b& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

static ModuleItem* FindInitialBlock(ParseResult4b& r) {
  return FindItemByKind(r, ModuleItemKind::kInitialBlock);
}

// ---------------------------------------------------------------------------
// 6. Multiple non-blocking assignments in sequence
// ---------------------------------------------------------------------------
TEST(ParserSection4, Sec4_5_MultipleNonblockingAssigns) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c, d;\n"
      "  initial begin\n"
      "    a <= b;\n"
      "    c <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* init_item = FindInitialBlock(r);
  ASSERT_NE(init_item, nullptr);
  auto* body = init_item->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kNonblockingAssign);
}

}  // namespace
